{-# OPTIONS --without-K #-}

module Z3.Base where

{-# FOREIGN GHC
import Data.Bool
import GHC.Exts (Any)
import System.IO.Unsafe
import Z3.Base
#-}

open import Agda.Builtin.IO
open import Data.Bool
open import Data.Integer
open import Data.List
open import Data.List.NonEmpty
open import Data.List.Relation.Unary.All as list
open import Data.Maybe as Maybe
open import Data.Maybe.Relation.Unary.All as maybe
open import Data.Product
open import Data.String
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality as PropEq

import Level

postulate
    Config : Set
    withConfig : {a : Set} → (Config → IO a) → IO a

    Context : Set
    mkContext : Config → IO Context

    Symbol Sort App Pattern Constructor AST FuncDecl Model FuncInterp FuncEntry Params Solver : Set

{-# COMPILE GHC Config = type Config #-}
{-# COMPILE GHC Context = type Context #-}
{-# COMPILE GHC Symbol = type Symbol #-}
{-# COMPILE GHC Sort = type Sort #-}
{-# COMPILE GHC App = type App #-}
{-# COMPILE GHC Pattern = type Pattern #-}
{-# COMPILE GHC Constructor = type Constructor #-}
{-# COMPILE GHC Model = type Model #-}
{-# COMPILE GHC FuncInterp = type FuncInterp #-}
{-# COMPILE GHC FuncEntry = type FuncEntry #-}
{-# COMPILE GHC Params = type Params #-}
{-# COMPILE GHC Solver = type Solver #-}
{-# COMPILE GHC AST = type AST #-}
{-# COMPILE GHC FuncDecl = type FuncDecl #-}

private
    data SortKind : Set where
        UninterpretedSortKind BoolSortKind IntegerSortKind RealSortKind FiniteDomainSortKind : SortKind

    data Either (A B : Set) : Set where
        left  : A → Either A B
        right : B → Either A B
    {-# COMPILE GHC Either = data Either (Left | Right) #-}

    Either-⊎ : {A B : _} → Either A B → A ⊎ B
    Either-⊎ (left  a) = inj₁ a
    Either-⊎ (right b) = inj₂ b

    either : {A B C : _} → (A → C) → (B → C) → Either A B → C
    either f _ (left  a) = f a
    either _ g (right b) = g b

module _ {ctx : Context} where
    open import Agda.Builtin.Word using (Word64)

    postulate
        mkUninterpretedSort : Symbol → Sort
        mkBoolSort mkIntegerSort mkRealSort : Sort
        mkFiniteDomainSort : Symbol → Word64 → Sort
        mkSetSort : Sort → Sort

        mkFuncDecl : Symbol → List Sort → Sort → FuncDecl

        mkApp : FuncDecl → List AST → AST

        mkEq : AST → AST → AST
        mkNot : AST → AST
        mkIfThenElse : AST → AST → AST → AST
        mkImplies mkXor : AST → AST → AST
        mkAnd mkOr : List AST → AST
        mkDistinct : List⁺ AST → AST
        mkBool : Bool → AST

        mkInteger : ℤ → Sort → AST

    private
        postulate
            getSortKind : Sort → SortKind

    {-# COMPILE GHC mkUninterpretedSort = \ ctx s -> unsafePerformIO $ mkUninterpretedSort ctx s #-}
    {-# COMPILE GHC mkBoolSort = unsafePerformIO . mkBoolSort #-}
    {-# COMPILE GHC mkIntegerSort = unsafePerformIO . mkIntSort #-}
    {-# COMPILE GHC mkRealSort = unsafePerformIO . mkRealSort #-}
    {-# COMPILE GHC mkFiniteDomainSort = \ ctx s n -> unsafePerformIO $ mkFiniteDomainSort ctx s n #-}
    {-# COMPILE GHC mkSetSort = \ ctx sort -> unsafePerformIO $ mkSetSort ctx sort #-}

    {-# COMPILE GHC mkInteger = \ ctx n sort -> unsafePerformIO $ mkInteger' ctx n sort #-}
    {-# FOREIGN GHC
        mkInteger' :: Context -> Integer -> Sort -> IO AST
        mkInteger' = mkIntegral
      #-}

    mkConst mkVar : Symbol → Sort → AST
    mkConst s sort = mkApp (mkFuncDecl s [] sort) []
    mkVar = mkConst

    mkBoolVar : Symbol → AST
    mkBoolVar s = mkVar s mkBoolSort

    ⟦_⟧ : Sort → Maybe Set
    ⟦ sort ⟧ with getSortKind sort
    ... | BoolSortKind = just Bool
    ... | IntegerSortKind = just ℤ
    ... | _ = nothing

    module _ (solv : Solver) where
        private
            postulate
                check' : List AST → Either ⊤ (Either (List AST) Model)
            {-# COMPILE GHC check' = \ ctx solv as -> unsafePerformIO $ do
                solverCheckAssumptions ctx solv as >>= \ case {
                    Undef -> pure $ Left ();
                    Unsat -> pure . Left <$> solverGetUnsatCore ctx solv;
                    Sat -> pure . Right <$> solverGetModel ctx solv;
                }
              #-}

        check : List AST → Maybe (List AST ⊎ Model)
        check = Maybe.map Either-⊎ ∘ (λ { (left tt) → nothing; (right a) → just a }) ∘ check'

    private
        postulate
            evalBool' : Model → AST → Either ⊤ Bool
            evalInt'  : Model → AST → Either ⊤ ℤ

    {-# COMPILE GHC evalBool' = \ ctx model -> maybe (Left ()) Right . unsafePerformIO . evalBool ctx model #-}
    {-# COMPILE GHC evalInt'  = \ ctx model -> maybe (Left ()) Right . unsafePerformIO . evalInt  ctx model #-}

    evalBool : Model → AST → Maybe Bool
    evalBool model = either (const nothing) just ∘ evalBool' model

    evalInteger : Model → AST → Maybe ℤ
    evalInteger model = either (const nothing) just ∘ evalInt'  model
