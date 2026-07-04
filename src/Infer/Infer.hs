module Infer.Infer
  ( inferExpr
  , inferType
  , defaultEnv
  ) where

import qualified Data.Map.Strict as Map
import Control.Monad.State
import Control.Monad.Except

import Infer.Ast
import Infer.Types
import Infer.Unify

-- | Inference monad: carries a fresh variable counter and can fail with TypeError
type Infer a = ExceptT TypeError (State Int) a

-- | Generate a fresh type variable
fresh :: Infer Type
fresh = do
  n <- get
  put (n + 1)
  return (TVar (letters !! n))
  where
    letters :: [String]
    letters = [1..] >>= flip replicateM ['a'..'z']

-- | Instantiate a scheme with fresh variables in the Infer monad
instantiateInfer :: Scheme -> Infer Type
instantiateInfer (Forall vs t) = do
  nvs <- mapM (const fresh) vs
  let s = Map.fromList (zip vs nvs)
  return (apply s t)

-- | Run type inference on an expression, returning either an error or the type
inferExpr :: TypeEnv -> Expr -> Either TypeError Type
inferExpr env expr =
  let (result, _) = runState (runExceptT (infer env expr)) 0
  in case result of
    Left err -> Left err
    Right (s, t) -> Right (apply s t)

-- | Convenience: infer and pretty-print (with normalized variable names)
inferType :: TypeEnv -> Expr -> Either TypeError String
inferType env expr = prettyType . normalizeType <$> inferExpr env expr

-- | Core Algorithm W implementation
infer :: TypeEnv -> Expr -> Infer (Subst, Type)

-- Variable
infer env (EVar x) =
  case envLookup x env of
    Nothing -> throwError (UnboundVariable x)
    Just scheme -> do
      t <- instantiateInfer scheme
      return (emptySubst, t)

-- Literal
infer _ (ELit (LInt _))    = return (emptySubst, TCon "Int")
infer _ (ELit (LBool _))   = return (emptySubst, TCon "Bool")
infer _ (ELit (LString _)) = return (emptySubst, TCon "String")

-- Lambda
infer env (ELam x body) = do
  tv <- fresh
  let env' = envInsert x (Forall [] tv) env
  (s, t) <- infer env' body
  return (s, TFun (apply s tv) t)

-- Application
infer env (EApp e1 e2) = do
  tv <- fresh
  (s1, t1) <- infer env e1
  (s2, t2) <- infer (apply s1 env) e2
  s3 <- liftUnify $ unify (apply s2 t1) (TFun t2 tv)
  return (composeSubst s3 (composeSubst s2 s1), apply s3 tv)

-- Let (with let-polymorphism)
infer env (ELet x e1 e2) = do
  (s1, t1) <- infer env e1
  let env' = apply s1 env
      scheme = generalize env' t1
      env'' = envInsert x scheme env'
  (s2, t2) <- infer env'' e2
  return (composeSubst s2 s1, t2)

-- If-then-else
infer env (EIf cond thenE elseE) = do
  (s1, tCond) <- infer env cond
  s2 <- liftUnify $ unify tCond (TCon "Bool")
  let s12 = composeSubst s2 s1
  (s3, tThen) <- infer (apply s12 env) thenE
  let s123 = composeSubst s3 s12
  (s4, tElse) <- infer (apply s123 env) elseE
  let s1234 = composeSubst s4 s123
  s5 <- liftUnify $ unify (apply s4 tThen) tElse
  return (composeSubst s5 s1234, apply s5 tElse)

-- Constructor
infer env (ECon name) =
  case envLookup name env of
    Nothing -> throwError (UnboundVariable name)
    Just scheme -> do
      t <- instantiateInfer scheme
      return (emptySubst, t)

-- Tuple
infer env (ETuple es) = do
  results <- inferList env es
  let (s, ts) = results
  return (s, TTuple ts)

-- Case / pattern matching
infer env (ECase scrut branches) = do
  (s0, scrutTy) <- infer env scrut
  tv <- fresh  -- result type
  sRef <- foldM (inferBranch (apply s0 env) scrutTy tv) s0 branches
  return (sRef, apply sRef tv)

-- | Infer types for a list of expressions, threading substitutions
inferList :: TypeEnv -> [Expr] -> Infer (Subst, [Type])
inferList env = foldM go (emptySubst, [])
  where
    go (s, ts) e = do
      (s', t) <- infer (apply s env) e
      return (composeSubst s' s, ts ++ [t])

-- | Infer a single case branch
inferBranch :: TypeEnv -> Type -> Type -> Subst -> CaseBranch -> Infer Subst
inferBranch env scrutTy resultTy s0 (pat, body) = do
  (patEnv, patTy) <- inferPattern env pat
  s1 <- liftUnify $ unify (apply s0 scrutTy) patTy
  let s01 = composeSubst s1 s0
      env' = apply s01 (mergeEnv env patEnv)
  (s2, bodyTy) <- infer env' body
  let s012 = composeSubst s2 s01
  s3 <- liftUnify $ unify (apply s012 resultTy) bodyTy
  return (composeSubst s3 s012)

-- | Infer the type introduced by a pattern, returning new bindings and pattern type
inferPattern :: TypeEnv -> Pattern -> Infer (TypeEnv, Type)
inferPattern _ (PVar x) = do
  tv <- fresh
  return (envFromList [(x, Forall [] tv)], tv)
inferPattern _ PWild = do
  tv <- fresh
  return (emptyEnv, tv)
inferPattern _ (PLit (LInt _))    = return (emptyEnv, TCon "Int")
inferPattern _ (PLit (LBool _))   = return (emptyEnv, TCon "Bool")
inferPattern _ (PLit (LString _)) = return (emptyEnv, TCon "String")
inferPattern env (PCon name pats) =
  case envLookup name env of
    Nothing -> throwError (UnboundVariable name)
    Just scheme -> do
      conTy <- instantiateInfer scheme
      (patEnvs, patTys) <- unzip <$> mapM (inferPattern env) pats
      resultTy <- fresh
      let expectedTy = foldr TFun resultTy patTys
      s <- liftUnify $ unify conTy expectedTy
      let combinedEnv = foldl mergeEnv emptyEnv patEnvs
      return (apply s combinedEnv, apply s resultTy)

-- | Merge two type environments (right-biased)
mergeEnv :: TypeEnv -> TypeEnv -> TypeEnv
mergeEnv (TypeEnv e1) (TypeEnv e2) = TypeEnv (Map.union e2 e1)

-- | Lift a unification result into the Infer monad
liftUnify :: Either TypeError Subst -> Infer Subst
liftUnify = liftEither

-- | Default environment with common constructors
defaultEnv :: TypeEnv
defaultEnv = envFromList
  [ ("True",    Forall [] (TCon "Bool"))
  , ("False",   Forall [] (TCon "Bool"))
  , ("Nothing", Forall ["a"] (TCon "Maybe"))
  , ("Just",    Forall ["a"] (TFun (TVar "a") (TCon "Maybe")))
  , ("Left",    Forall ["a", "b"] (TFun (TVar "a") (TCon "Either")))
  , ("Right",   Forall ["a", "b"] (TFun (TVar "b") (TCon "Either")))
  , ("Pair",    Forall ["a", "b"] (TFun (TVar "a") (TFun (TVar "b") (TTuple [TVar "a", TVar "b"]))))
  ]
