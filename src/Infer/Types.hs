module Infer.Types
  ( Type(..)
  , Scheme(..)
  , TVar
  , Subst
  , TypeEnv(..)
  , TypeError(..)
  , Substitutable(..)
  , emptySubst
  , composeSubst
  , envLookup
  , envInsert
  , envFromList
  , emptyEnv
  , generalize
  , instantiate
  , prettyType
  , normalizeType
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (intercalate)
import Control.Monad.State

-- | Type variable name
type TVar = String

-- | Substitution: mapping from type variables to types
type Subst = Map.Map TVar Type

-- | Types in our system
data Type
  = TVar TVar              -- ^ Type variable
  | TCon String             -- ^ Type constructor (Int, Bool, String)
  | TFun Type Type          -- ^ Function type (a -> b)
  | TTuple [Type]           -- ^ Tuple/product type
  deriving (Eq, Ord)

instance Show Type where
  show = prettyType

-- | Pretty print a type
prettyType :: Type -> String
prettyType (TVar v) = v
prettyType (TCon c) = c
prettyType (TFun a@(TFun _ _) b) = "(" ++ prettyType a ++ ") -> " ++ prettyType b
prettyType (TFun a b) = prettyType a ++ " -> " ++ prettyType b
prettyType (TTuple ts) = "(" ++ intercalate ", " (map prettyType ts) ++ ")"

-- | Type scheme (forall a1 a2 ... . type)
data Scheme = Forall [TVar] Type
  deriving (Show, Eq)

-- | Type environment: mapping from variable names to type schemes
newtype TypeEnv = TypeEnv (Map.Map String Scheme)
  deriving (Show, Eq)

-- | Type errors
data TypeError
  = UnificationFail Type Type
  | InfiniteType TVar Type
  | UnboundVariable String
  | UnificationMismatch [Type] [Type]
  | PatternMatchError String
  deriving (Show, Eq)

-- | Empty substitution
emptySubst :: Subst
emptySubst = Map.empty

-- | Compose two substitutions: apply s1 first, then s2
composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = Map.map (apply s1) s2 `Map.union` s1

-- | Class for types that support substitution and free type variables
class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> Set.Set TVar

instance Substitutable Type where
  apply s (TVar v) = Map.findWithDefault (TVar v) v s
  apply s (TFun t1 t2) = TFun (apply s t1) (apply s t2)
  apply s (TTuple ts) = TTuple (map (apply s) ts)
  apply _ t = t

  ftv (TVar v) = Set.singleton v
  ftv (TFun t1 t2) = ftv t1 `Set.union` ftv t2
  ftv (TTuple ts) = foldl Set.union Set.empty (map ftv ts)
  ftv _ = Set.empty

instance Substitutable Scheme where
  apply s (Forall vs t) = Forall vs (apply s' t)
    where s' = foldr Map.delete s vs
  ftv (Forall vs t) = ftv t `Set.difference` Set.fromList vs

instance Substitutable TypeEnv where
  apply s (TypeEnv env) = TypeEnv (Map.map (apply s) env)
  ftv (TypeEnv env) = foldl Set.union Set.empty (map ftv (Map.elems env))

instance Substitutable a => Substitutable [a] where
  apply s = map (apply s)
  ftv = foldl (\acc x -> acc `Set.union` ftv x) Set.empty

-- | Look up a variable in the environment
envLookup :: String -> TypeEnv -> Maybe Scheme
envLookup k (TypeEnv env) = Map.lookup k env

-- | Insert a binding into the environment
envInsert :: String -> Scheme -> TypeEnv -> TypeEnv
envInsert k v (TypeEnv env) = TypeEnv (Map.insert k v env)

-- | Create an environment from a list
envFromList :: [(String, Scheme)] -> TypeEnv
envFromList = TypeEnv . Map.fromList

-- | Empty type environment
emptyEnv :: TypeEnv
emptyEnv = TypeEnv Map.empty

-- | Generalize a type over the free variables not in the environment
generalize :: TypeEnv -> Type -> Scheme
generalize env t = Forall vs t
  where vs = Set.toList (ftv t `Set.difference` ftv env)

-- | Instantiate a scheme with fresh type variables
instantiate :: Scheme -> State Int Type
instantiate (Forall vs t) = do
  nvs <- mapM (const fresh) vs
  let s = Map.fromList (zip vs nvs)
  return (apply s t)
  where
    fresh :: State Int Type
    fresh = do
      n <- get
      put (n + 1)
      return (TVar (letters !! n))

    letters :: [String]
    letters = [1..] >>= flip replicateM ['a'..'z']

-- | Normalize type variables so they are named a, b, c, ... in order of first appearance
normalizeType :: Type -> Type
normalizeType ty = apply subst ty
  where
    -- Collect type variables in order of first appearance (left-to-right)
    collectVars :: Type -> [TVar]
    collectVars (TVar v) = [v]
    collectVars (TCon _) = []
    collectVars (TFun t1 t2) = collectVars t1 ++ collectVars t2
    collectVars (TTuple ts) = concatMap collectVars ts

    -- Remove duplicates preserving order
    nub' :: Eq a => [a] -> [a]
    nub' [] = []
    nub' (x:xs) = x : nub' (filter (/= x) xs)

    vars = nub' (collectVars ty)
    names = [1..] >>= flip replicateM ['a'..'z']
    subst = Map.fromList (zip vars (map TVar names))
