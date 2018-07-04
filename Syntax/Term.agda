module Syntax.Term where

open import Utils
open import Data.Product
open import Data.Nat
open import Data.Empty
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

mutual
  data Term : Set where
    Var  : Term
    _·_  : Term → Term → Term
    Lam  : Term → Term
    U    : Term
    Π    : Term → Term → Term
    _[_]ₛ : Term → Subst → Term

  data Subst : Set where
    Id  : Subst
    _,_ : Subst → Term → Subst
    _·_ : Subst → Subst → Subst
    ↑   : Subst

data Ctxt : Set where
  ◇ : Ctxt
  _#_ : Ctxt → Term → Ctxt
infixl 7 _#_

clen : Ctxt → ℕ
clen ◇ = 0
clen (Γ # _) = suc (clen Γ)

idsub : Ctxt → Subst
idsub ◇ = Id
idsub (Γ # A) = (idsub Γ · ↑) , Var
