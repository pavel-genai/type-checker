module Main where

import Test.Hspec
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Control.Monad.State (evalState)
import Infer.Ast
import Infer.Types
import Infer.Unify
import Infer.Infer
import Infer.Parser

-- Helper: parse and infer
inferStr :: String -> Either String String
inferStr input = do
  expr <- parseExpr input
  case inferType defaultEnv expr of
    Left err -> Left (show err)
    Right ty -> Right ty

-- Helper: expect success
shouldInferTo :: String -> String -> Expectation
shouldInferTo input expected =
  inferStr input `shouldBe` Right expected

-- Helper: expect parse failure
shouldFailParse :: String -> Expectation
shouldFailParse input =
  case parseExpr input of
    Left _  -> return ()
    Right _ -> expectationFailure "Expected parse error"

main :: IO ()
main = hspec $ do
  describe "Literals" $ do
    it "infers Int for integer literals" $
      "42" `shouldInferTo` "Int"

    it "infers Bool for True" $
      "True" `shouldInferTo` "Bool"

    it "infers Bool for False" $
      "False" `shouldInferTo` "Bool"

    it "infers String for string literals" $
      "\"hello\"" `shouldInferTo` "String"

  describe "Lambda expressions" $ do
    it "infers identity function" $
      "\\x -> x" `shouldInferTo` "a -> a"

    it "infers const function" $
      "\\x -> \\y -> x" `shouldInferTo` "a -> b -> a"

    it "infers multi-arg lambda" $
      "\\x y -> x" `shouldInferTo` "a -> b -> a"

  describe "Function application" $ do
    it "infers application of identity" $
      "(\\x -> x) 42" `shouldInferTo` "Int"

    it "infers application of const" $
      "(\\x -> \\y -> x) True 42" `shouldInferTo` "Bool"

  describe "Let expressions" $ do
    it "infers simple let binding" $
      "let x = 42 in x" `shouldInferTo` "Int"

    it "supports let-polymorphism" $
      "let id = \\x -> x in id 42" `shouldInferTo` "Int"

    it "uses polymorphic binding at different types" $
      "let id = \\x -> x in if id True then id 1 else id 2" `shouldInferTo` "Int"

  describe "If-then-else" $ do
    it "infers if with matching branches" $
      "if True then 1 else 2" `shouldInferTo` "Int"

    it "rejects non-bool condition" $ do
      let result = inferStr "if 42 then 1 else 2"
      case result of
        Left _ -> return ()
        Right _ -> expectationFailure "Expected type error for non-bool condition"

    it "rejects mismatched branches" $ do
      let result = inferStr "if True then 1 else True"
      case result of
        Left _ -> return ()
        Right _ -> expectationFailure "Expected type error for mismatched branches"

  describe "Higher-order functions" $ do
    it "infers compose-like function" $
      "\\f -> \\g -> \\x -> f (g x)" `shouldInferTo` "(a -> b) -> (c -> a) -> c -> b"

    it "infers twice function" $
      "\\f -> \\x -> f (f x)" `shouldInferTo` "(a -> a) -> a -> a"

  describe "Unification" $ do
    it "unifies identical type constructors" $
      unify (TCon "Int") (TCon "Int") `shouldBe` Right emptySubst

    it "fails on different constructors" $ do
      let result = unify (TCon "Int") (TCon "Bool")
      case result of
        Left (UnificationFail _ _) -> return ()
        _ -> expectationFailure "Expected unification failure"

    it "binds type variable" $
      unify (TVar "a") (TCon "Int") `shouldBe` Right (Map.singleton "a" (TCon "Int"))

    it "detects infinite types" $ do
      let result = unify (TVar "a") (TFun (TVar "a") (TVar "a"))
      case result of
        Left (InfiniteType _ _) -> return ()
        _ -> expectationFailure "Expected infinite type error"

  describe "Parser" $ do
    it "parses integer literal" $
      parseExpr "42" `shouldBe` Right (ELit (LInt 42))

    it "parses lambda" $
      parseExpr "\\x -> x" `shouldBe` Right (ELam "x" (EVar "x"))

    it "parses let" $
      parseExpr "let x = 1 in x" `shouldBe` Right (ELet "x" (ELit (LInt 1)) (EVar "x"))

    it "parses if-then-else" $
      parseExpr "if True then 1 else 2" `shouldBe`
        Right (EIf (ELit (LBool True)) (ELit (LInt 1)) (ELit (LInt 2)))

    it "parses application" $
      parseExpr "f x" `shouldBe` Right (EApp (EVar "f") (EVar "x"))

    it "parses nested application left-associatively" $
      parseExpr "f x y" `shouldBe` Right (EApp (EApp (EVar "f") (EVar "x")) (EVar "y"))

    it "rejects invalid input" $
      shouldFailParse "let = in"

  describe "Case expressions" $ do
    it "infers case on literals" $
      "case 1 of | x -> x" `shouldInferTo` "Int"

    it "infers case with wildcard" $
      "case True of | _ -> 42" `shouldInferTo` "Int"

    it "infers case matching a bool literal pattern" $
      "case True of | True -> 1 | False -> 2" `shouldInferTo` "Int"

    it "infers case matching an int literal pattern" $
      "case 1 of | 1 -> True | x -> False" `shouldInferTo` "Bool"

    it "infers case matching a string literal pattern" $
      "case \"a\" of | \"a\" -> 1 | _ -> 2" `shouldInferTo` "Int"

    it "infers case with a constructor pattern binding a variable" $
      "case Just 1 of | Just x -> x | Nothing -> 0" `shouldInferTo` "Int"

    it "infers case with a nullary constructor pattern" $
      "case Nothing of | Nothing -> 0 | Just x -> x" `shouldInferTo` "Int"

    it "infers case with a parenthesised sub-pattern" $
      "case Just 1 of | Just (x) -> x | _ -> 0" `shouldInferTo` "Int"

    it "rejects a case whose branch bodies disagree" $ do
      let result = inferStr "case 1 of | x -> x | y -> True"
      case result of
        Left _  -> return ()
        Right _ -> expectationFailure "Expected type error for mismatched branch bodies"

    it "rejects a case whose patterns disagree with the scrutinee" $ do
      let result = inferStr "case 1 of | True -> 1"
      case result of
        Left _  -> return ()
        Right _ -> expectationFailure "Expected type error for pattern/scrutinee mismatch"

    it "rejects a case with an unbound constructor pattern" $
      case inferExpr defaultEnv
             (ECase (ELit (LInt 1)) [(PCon "Nope" [], ELit (LInt 1))]) of
        Left (UnboundVariable "Nope") -> return ()
        _ -> expectationFailure "Expected unbound constructor in pattern"

  describe "Constructors and data types" $ do
    it "infers Nothing as Maybe" $
      "Nothing" `shouldInferTo` "Maybe"

    it "infers Just applied to an Int" $
      "Just 42" `shouldInferTo` "Maybe"

    it "infers Left applied to a value as Either" $
      "Left 1" `shouldInferTo` "Either"

    it "infers Right applied to a value as Either" $
      "Right True" `shouldInferTo` "Either"

    it "infers Pair as a tuple constructor" $
      "Pair 1 True" `shouldInferTo` "(Int, Bool)"

    it "rejects an unbound constructor" $ do
      let result = inferStr "Foo"
      case result of
        Left _  -> return ()
        Right _ -> expectationFailure "Expected unbound constructor error"

    it "rejects an unbound variable" $ do
      let result = inferStr "unboundVar"
      case result of
        Left _  -> return ()
        Right _ -> expectationFailure "Expected unbound variable error"

  describe "Tuples" $ do
    it "infers a pair tuple" $
      "(\\x y -> Pair x y) 1 True" `shouldInferTo` "(Int, Bool)"

    it "infers polymorphic tuple element types via constructors" $
      "Pair True \"hi\"" `shouldInferTo` "(Bool, String)"

    it "infers an empty ETuple as the empty tuple type" $
      inferExpr defaultEnv (ETuple []) `shouldBe` Right (TTuple [])

    it "infers an ETuple of literals element-wise" $
      inferExpr defaultEnv (ETuple [ELit (LInt 1), ELit (LBool True)])
        `shouldBe` Right (TTuple [TCon "Int", TCon "Bool"])

    it "threads substitutions across ETuple elements" $
      inferExpr defaultEnv
        (EApp (ELam "x" (ETuple [EVar "x", ELit (LInt 1)])) (ELit (LBool True)))
        `shouldBe` Right (TTuple [TCon "Bool", TCon "Int"])

    it "propagates an error from within an ETuple" $
      case inferExpr defaultEnv (ETuple [EVar "nope"]) of
        Left (UnboundVariable "nope") -> return ()
        _ -> expectationFailure "Expected unbound variable error inside tuple"

  describe "Parser: patterns (via case scrutinee)" $ do
    it "parses a wildcard pattern" $
      firstPat "case x of | _ -> 1" `shouldBe` Right PWild

    it "parses a variable pattern" $
      firstPat "case x of | y -> 1" `shouldBe` Right (PVar "y")

    it "parses a True literal pattern" $
      firstPat "case x of | True -> 1" `shouldBe` Right (PLit (LBool True))

    it "parses a False literal pattern" $
      firstPat "case x of | False -> 1" `shouldBe` Right (PLit (LBool False))

    it "parses an integer literal pattern" $
      firstPat "case x of | 7 -> 1" `shouldBe` Right (PLit (LInt 7))

    it "parses a string literal pattern" $
      firstPat "case x of | \"hi\" -> 1" `shouldBe` Right (PLit (LString "hi"))

    it "parses a nullary constructor pattern" $
      firstPat "case x of | Nothing -> 1" `shouldBe` Right (PCon "Nothing" [])

    it "parses a constructor pattern with variable arguments" $
      firstPat "case x of | Just y -> 1" `shouldBe` Right (PCon "Just" [PVar "y"])

    it "parses a constructor pattern with a wildcard argument" $
      firstPat "case x of | Just _ -> 1" `shouldBe` Right (PCon "Just" [PWild])

    it "parses a constructor pattern with a parenthesised argument" $
      firstPat "case x of | Pair (y) z -> 1" `shouldBe`
        Right (PCon "Pair" [PVar "y", PVar "z"])

  describe "Parser: extra expression cases" $ do
    it "parses a bare constructor as ECon" $
      parseExpr "Nothing" `shouldBe` Right (ECon "Nothing")

    it "parses a string literal expression" $
      parseExpr "\"hi\"" `shouldBe` Right (ELit (LString "hi"))

    it "parses a case expression" $
      parseExpr "case x of | _ -> 1" `shouldBe`
        Right (ECase (EVar "x") [(PWild, ELit (LInt 1))])

    it "ignores line comments" $
      parseExpr "42 -- this is a comment" `shouldBe` Right (ELit (LInt 42))

    it "ignores block comments" $
      parseExpr "{- header -} 42" `shouldBe` Right (ELit (LInt 42))

    it "parses identifiers containing underscores and primes" $
      parseExpr "foo_bar'" `shouldBe` Right (EVar "foo_bar'")

    it "rejects a reserved word used as an identifier" $
      shouldFailParse "let"

    it "rejects trailing garbage after a complete expression" $
      shouldFailParse "42 )"

    it "rejects an empty input" $
      shouldFailParse ""

  describe "prettyType" $ do
    it "prints a type variable" $
      prettyType (TVar "a") `shouldBe` "a"

    it "prints a type constructor" $
      prettyType (TCon "Int") `shouldBe` "Int"

    it "prints a simple function type" $
      prettyType (TFun (TCon "Int") (TCon "Bool")) `shouldBe` "Int -> Bool"

    it "parenthesises a function type on the left of an arrow" $
      prettyType (TFun (TFun (TCon "Int") (TCon "Int")) (TCon "Bool"))
        `shouldBe` "(Int -> Int) -> Bool"

    it "does not parenthesise a right-nested arrow" $
      prettyType (TFun (TCon "Int") (TFun (TCon "Int") (TCon "Bool")))
        `shouldBe` "Int -> Int -> Bool"

    it "prints a tuple type" $
      prettyType (TTuple [TCon "Int", TCon "Bool", TVar "a"])
        `shouldBe` "(Int, Bool, a)"

    it "is used by the Show instance for Type" $
      show (TFun (TVar "a") (TVar "b")) `shouldBe` "a -> b"

  describe "normalizeType" $ do
    it "renames variables to a, b, ... in order of first appearance" $
      normalizeType (TFun (TVar "z") (TVar "q"))
        `shouldBe` TFun (TVar "a") (TVar "b")

    it "reuses the same fresh name for repeated variables" $
      normalizeType (TFun (TVar "z") (TVar "z"))
        `shouldBe` TFun (TVar "a") (TVar "a")

    it "leaves concrete types untouched" $
      normalizeType (TCon "Int") `shouldBe` TCon "Int"

    it "normalizes variables inside tuples" $
      normalizeType (TTuple [TVar "x", TVar "y", TVar "x"])
        `shouldBe` TTuple [TVar "a", TVar "b", TVar "a"]

  describe "Substitutable and substitutions" $ do
    it "apply replaces a bound variable" $
      apply (Map.singleton "a" (TCon "Int")) (TVar "a") `shouldBe` TCon "Int"

    it "apply leaves an unbound variable alone" $
      apply (Map.singleton "a" (TCon "Int")) (TVar "b") `shouldBe` TVar "b"

    it "apply recurses into function types" $
      apply (Map.singleton "a" (TCon "Int")) (TFun (TVar "a") (TVar "a"))
        `shouldBe` TFun (TCon "Int") (TCon "Int")

    it "apply recurses into tuple types" $
      apply (Map.singleton "a" (TCon "Int")) (TTuple [TVar "a", TVar "b"])
        `shouldBe` TTuple [TCon "Int", TVar "b"]

    it "apply on a constructor is a no-op" $
      apply (Map.singleton "a" (TCon "Int")) (TCon "Bool") `shouldBe` TCon "Bool"

    it "ftv of a variable is the singleton set" $
      ftv (TVar "a") `shouldBe` Set.singleton "a"

    it "ftv of a function type is the union" $
      ftv (TFun (TVar "a") (TVar "b")) `shouldBe` Set.fromList ["a", "b"]

    it "ftv of a tuple type is the union of elements" $
      ftv (TTuple [TVar "a", TVar "b", TCon "Int"])
        `shouldBe` Set.fromList ["a", "b"]

    it "ftv of a constructor is empty" $
      ftv (TCon "Int") `shouldBe` Set.empty

    it "ftv of a scheme excludes the bound variables" $
      ftv (Forall ["a"] (TFun (TVar "a") (TVar "b")))
        `shouldBe` Set.singleton "b"

    it "apply on a scheme does not touch bound variables" $
      apply (Map.singleton "a" (TCon "Int")) (Forall ["a"] (TVar "a"))
        `shouldBe` Forall ["a"] (TVar "a")

    it "apply on a scheme substitutes free variables" $
      apply (Map.singleton "b" (TCon "Int")) (Forall ["a"] (TVar "b"))
        `shouldBe` Forall ["a"] (TCon "Int")

    it "ftv of a list is the union over elements" $
      ftv [TVar "a", TVar "b", TVar "a"] `shouldBe` Set.fromList ["a", "b"]

    it "apply over a list maps element-wise" $
      apply (Map.singleton "a" (TCon "Int")) [TVar "a", TVar "b"]
        `shouldBe` [TCon "Int", TVar "b"]

    it "emptySubst is the empty map" $
      emptySubst `shouldBe` (Map.empty :: Subst)

    it "composeSubst applies the first substitution to the second's range" $
      composeSubst (Map.singleton "b" (TCon "Int"))
                   (Map.singleton "a" (TVar "b"))
        `shouldBe` Map.fromList [("a", TCon "Int"), ("b", TCon "Int")]

  describe "TypeEnv operations" $ do
    it "emptyEnv looks up to Nothing" $
      envLookup "x" emptyEnv `shouldBe` Nothing

    it "envInsert then envLookup returns the scheme" $
      envLookup "x" (envInsert "x" (Forall [] (TCon "Int")) emptyEnv)
        `shouldBe` Just (Forall [] (TCon "Int"))

    it "envFromList builds a lookupable environment" $
      envLookup "y" (envFromList [("y", Forall [] (TCon "Bool"))])
        `shouldBe` Just (Forall [] (TCon "Bool"))

    it "ftv of an environment unions its schemes' free variables" $
      ftv (envFromList [ ("x", Forall [] (TVar "a"))
                       , ("y", Forall ["b"] (TVar "b")) ])
        `shouldBe` Set.singleton "a"

    it "apply over an environment rewrites its schemes" $
      envLookup "x" (apply (Map.singleton "a" (TCon "Int"))
                           (envFromList [("x", Forall [] (TVar "a"))]))
        `shouldBe` Just (Forall [] (TCon "Int"))

  describe "generalize and instantiate" $ do
    it "generalizes the free variables not bound in the environment" $
      generalize emptyEnv (TFun (TVar "a") (TVar "a"))
        `shouldBe` Forall ["a"] (TFun (TVar "a") (TVar "a"))

    it "does not generalize variables free in the environment" $
      generalize (envFromList [("x", Forall [] (TVar "a"))])
                 (TFun (TVar "a") (TVar "b"))
        `shouldBe` Forall ["b"] (TFun (TVar "a") (TVar "b"))

    it "instantiate replaces bound variables with fresh ones" $ do
      let ty = evalState (instantiate (Forall ["a"] (TFun (TVar "a") (TVar "a")))) 0
      ty `shouldBe` TFun (TVar "a") (TVar "a")

    it "instantiate freshens distinct bound variables distinctly" $ do
      let ty = evalState (instantiate (Forall ["x", "y"] (TFun (TVar "x") (TVar "y")))) 0
      ty `shouldBe` TFun (TVar "a") (TVar "b")

    it "instantiate leaves free variables untouched" $ do
      let ty = evalState (instantiate (Forall ["a"] (TFun (TVar "a") (TVar "free")))) 0
      ty `shouldBe` TFun (TVar "a") (TVar "free")

  describe "Unification: further cases" $ do
    it "unifies function types component-wise" $
      unify (TFun (TVar "a") (TCon "Int")) (TFun (TCon "Bool") (TVar "b"))
        `shouldBe` Right (Map.fromList [("a", TCon "Bool"), ("b", TCon "Int")])

    it "binds a variable on the right-hand side" $
      unify (TCon "Int") (TVar "a") `shouldBe` Right (Map.singleton "a" (TCon "Int"))

    it "unifies a variable with itself to the empty substitution" $
      unify (TVar "a") (TVar "a") `shouldBe` Right emptySubst

    it "unifies tuples of equal length" $
      unify (TTuple [TVar "a", TCon "Int"]) (TTuple [TCon "Bool", TVar "b"])
        `shouldBe` Right (Map.fromList [("a", TCon "Bool"), ("b", TCon "Int")])

    it "fails to unify tuples of different length" $
      case unify (TTuple [TCon "Int"]) (TTuple [TCon "Int", TCon "Bool"]) of
        Left (UnificationFail _ _) -> return ()
        _ -> expectationFailure "Expected unification failure for tuple arity"

    it "fails to unify a function with a constructor" $
      case unify (TFun (TCon "Int") (TCon "Int")) (TCon "Int") of
        Left (UnificationFail _ _) -> return ()
        _ -> expectationFailure "Expected unification failure"

    it "detects an occurs-check failure on the right" $
      case unify (TFun (TVar "a") (TVar "a")) (TVar "a") of
        Left (InfiniteType _ _) -> return ()
        _ -> expectationFailure "Expected infinite type error"

    it "unifyMany succeeds on empty lists" $
      unifyMany [] [] `shouldBe` Right emptySubst

    it "unifyMany fails on lists of different length" $
      case unifyMany [TCon "Int"] [] of
        Left (UnificationMismatch _ _) -> return ()
        _ -> expectationFailure "Expected unification mismatch"

    it "unifyMany threads substitutions across pairs" $
      unifyMany [TVar "a", TVar "a"] [TCon "Int", TVar "b"]
        `shouldBe` Right (Map.fromList [("a", TCon "Int"), ("b", TCon "Int")])

  describe "inferExpr / inferType end to end" $ do
    it "inferExpr returns the raw (un-normalized) type" $
      inferExpr defaultEnv (ELit (LInt 1)) `shouldBe` Right (TCon "Int")

    it "inferExpr propagates a type error" $
      case inferExpr defaultEnv (EVar "nope") of
        Left (UnboundVariable "nope") -> return ()
        _ -> expectationFailure "Expected unbound variable error"

    it "inferType pretty-prints the identity type normalized" $
      inferType defaultEnv (ELam "x" (EVar "x")) `shouldBe` Right "a -> a"

  where
    -- Extract the first branch's pattern from a parsed case expression,
    -- exercising the pattern parser through the public parseExpr entry point.
    firstPat :: String -> Either String Pattern
    firstPat input = do
      expr <- parseExpr input
      case expr of
        ECase _ ((pat, _) : _) -> Right pat
        _                      -> Left "expected a case expression with a branch"
