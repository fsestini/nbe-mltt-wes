module Syntax.Typed.System where

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Syntax.Term
open import Data.Product

mutual

  infix 4 ⊢_
  data ⊢_ : Ctxt → Set where
    ⊢◇ : ⊢ ◇
    ⊢# : ∀{Γ A} → ⊢ Γ → Γ ⊢ A → ⊢ Γ # A

  infix 4 _⊢ₛ_∶_
  data _⊢ₛ_∶_ : Ctxt → Subst → Ctxt → Set where
    ⊢Id : ∀{Γ} → ⊢ Γ → Γ ⊢ₛ Id ∶ Γ
    ⊢,  : ∀{Γ Δ A σ t} → Γ ⊢ₛ σ ∶ Δ → Δ ⊢ A → Γ ⊢ t ∶ A [ σ ]ₛ → Γ ⊢ₛ σ , t ∶ Δ # A
    ⊢·  : ∀{Γ Δ ∇ σ τ} → Γ ⊢ₛ σ ∶ Δ → ∇ ⊢ₛ τ ∶ Γ → ∇ ⊢ₛ σ · τ ∶ Δ
    ⊢↑  : ∀{Γ A} → Γ ⊢ A → Γ # A ⊢ₛ ↑ ∶ Γ

  infix 4 _⊢_
  data _⊢_ : Ctxt → Term → Set where
    U : ∀{Γ} → ⊢ Γ → Γ ⊢ U
    Π : ∀{Γ A P} → Γ # A ⊢ P → Γ ⊢ Π A P
    El : ∀{Γ A} → Γ ⊢ A ∶ U → Γ ⊢ A
    sub : ∀{Γ Δ A σ} → Γ ⊢ A → Δ ⊢ₛ σ ∶ Γ → Δ ⊢ A [ σ ]ₛ

  infix 4 _⊢_∶_
  data _⊢_∶_ : Ctxt → Term → Term → Set where
    var : ∀{Γ A} → Γ ⊢ A → Γ # A ⊢ Var ∶ A [ ↑ ]ₛ
    lam : ∀{Γ A B t} → Γ # A ⊢ t ∶ B → Γ ⊢ Lam t ∶ Π A B
    app : ∀{Γ Δ A B t s σ} → Γ ⊢ₛ σ ∶ Δ → Δ # A ⊢ B 
        → Γ ⊢ t ∶ (Π A B) [ σ ]ₛ → Γ ⊢ s ∶ A [ σ ]ₛ → Γ ⊢ t · s ∶ B [ σ , s ]ₛ
    coe : ∀{Γ t A B} → Γ ⊢ t ∶ A → Γ ⊢ A ∼ B → Γ ⊢ t ∶ B
    sub : ∀{Γ Δ t A σ} → Γ ⊢ t ∶ A → Δ ⊢ₛ σ ∶ Γ → Δ ⊢ t [ σ ]ₛ ∶ A [ σ ]ₛ

  infix 4 _⊢_∼_
  data _⊢_∼_ : Ctxt → Term → Term → Set where
    ∼refl : ∀{Γ A} → Γ ⊢ A → Γ ⊢ A ∼ A
    ∼symm : ∀{Γ A B} → Γ ⊢ A ∼ B → Γ ⊢ B ∼ A
    ∼trans : ∀{Γ A B C} → Γ ⊢ A ∼ B → Γ ⊢ B ∼ C → Γ ⊢ A ∼ C
    ∼El : ∀{Γ A B} → Γ ⊢ A ∼ B ∶ U → Γ ⊢ A ∼ B
    ∼Us  : ∀{Δ Γ σ} → Δ ⊢ₛ σ ∶ Γ → Δ ⊢ U [ σ ]ₛ ∼ U
    ∼Sub : ∀{Γ Δ A B σ τ} → Γ ⊢ A ∼ B → Δ ⊢ₛ σ ∼ τ ∶ Γ → Δ ⊢ A [ σ ]ₛ ∼ B [ τ ]ₛ
    ∼scomp : ∀{∇ Δ Γ A σ τ} → Γ ⊢ A → Δ ⊢ₛ σ ∶ Γ → ∇ ⊢ₛ τ ∶ Δ
           → ∇ ⊢ (A [ σ ]ₛ) [ τ ]ₛ ∼ (A [ σ · τ ]ₛ)
    ∼Id  : ∀{Γ A} → Γ ⊢ A → Γ ⊢ A [ Id ]ₛ ∼ A

  infix 4 _⊢_∼_∶_
  data _⊢_∼_∶_ : Ctxt → Term → Term → Term → Set where

    ∼refl : ∀{Γ t A} → Γ ⊢ t ∶ A → Γ ⊢ t ∼ t ∶ A
    ∼symm : ∀{Γ t s A} → Γ ⊢ t ∼ s ∶ A → Γ ⊢ s ∼ t ∶ A
    ∼trans : ∀{Γ t s w A} → Γ ⊢ t ∼ s ∶ A → Γ ⊢ s ∼ w ∶ A → Γ ⊢ t ∼ w ∶ A

    ∼β : ∀{Δ Γ A B t s σ} → Γ # A ⊢ t ∶ B → Δ ⊢ₛ σ ∶ Γ → Δ ⊢ s ∶ A [ σ ]ₛ
       → Δ ⊢ (Lam t [ σ ]ₛ) · s ∼ t [ σ , s ]ₛ ∶ B [ σ , s ]ₛ

    ∼app : ∀{Δ Γ r r' s s' A B σ}
         → Γ ⊢ r ∼ r' ∶ (Π A B) [ σ ]ₛ → Γ ⊢ s ∼ s' ∶ A [ σ ]ₛ → Γ ⊢ₛ σ ∶ Δ → Δ # A ⊢ B
         → Γ ⊢ r · s ∼ r' · s' ∶ B [ σ , s ]ₛ

    ∼coe : ∀{Γ t s A B} → Γ ⊢ t ∼ s ∶ A → Γ ⊢ A ∼ B → Γ ⊢ t ∼ s ∶ B

    ∼Sub : ∀{Γ Δ A t s σ τ} → Γ ⊢ t ∼ s ∶ A → Δ ⊢ₛ σ ∼ τ ∶ Γ → Δ ⊢ t [ σ ]ₛ ∼ s [ τ ]ₛ ∶ A [ σ ]ₛ
    ∼Id  : ∀{Γ A t} → Γ ⊢ t ∶ A → Γ ⊢ t [ Id ]ₛ ∼ t ∶ A

    ∼sapp : ∀{∇ Δ Γ A B t s σ τ} → Γ ⊢ t ∶ (Π A B) [ σ ]ₛ → Γ ⊢ s ∶ A [ σ ]ₛ → Γ ⊢ₛ σ ∶ Δ → ∇ ⊢ₛ τ ∶ Γ
          → Δ # A ⊢ B → ∇ ⊢ (t · s) [ τ ]ₛ ∼ (t [ τ ]ₛ) · (s [ τ ]ₛ) ∶ B [ σ · τ , s [ τ ]ₛ ]ₛ

    ∼scomp : ∀{∇ Δ Γ A t σ τ} → Γ ⊢ t ∶ A → Δ ⊢ₛ σ ∶ Γ → ∇ ⊢ₛ τ ∶ Δ
           → ∇ ⊢ (t [ σ ]ₛ) [ τ ]ₛ ∼ (t [ σ · τ ]ₛ) ∶ A [ σ · τ ]ₛ
    ∼var   : ∀{Γ Δ t A σ} → Δ ⊢ A → Γ ⊢ₛ σ ∶ Δ → Γ ⊢ t ∶ A [ σ ]ₛ → Γ ⊢ Var [ σ , t ]ₛ ∼ t ∶ A [ σ ]ₛ

  infix 4 _⊢ₛ_∼_∶_
  data _⊢ₛ_∼_∶_ : Ctxt → Subst → Subst → Ctxt → Set where
    ∼refl : ∀{Γ σ Δ} → Γ ⊢ₛ σ ∶ Δ → Γ ⊢ₛ σ ∼ σ ∶ Δ
    ∼symm : ∀{Γ σ s Δ} → Γ ⊢ₛ σ ∼ s ∶ Δ → Γ ⊢ₛ s ∼ σ ∶ Δ
    ∼trans : ∀{Γ σ s w Δ} → Γ ⊢ₛ σ ∼ s ∶ Δ → Γ ⊢ₛ s ∼ w ∶ Δ → Γ ⊢ₛ σ ∼ w ∶ Δ

    ∼Cons : ∀{Δ Γ A t s σ τ} → Δ ⊢ₛ σ ∼ τ ∶ Γ → Δ ⊢ t ∼ s ∶ A [ σ ]ₛ → Γ ⊢ A → Δ ⊢ₛ σ , t ∼ τ , s ∶ Γ # A
    ∼IdL  : ∀{Γ Δ σ} → Γ ⊢ₛ σ ∶ Δ → Γ ⊢ₛ Id · σ ∼ σ ∶ Δ
    ∼IdR  : ∀{Γ Δ σ} → Γ ⊢ₛ σ ∶ Δ → Γ ⊢ₛ σ · Id ∼ σ ∶ Δ
    ∼Up   : ∀{Γ Δ A σ t} → Γ ⊢ₛ σ ∶ Δ → Δ ⊢ A → Γ ⊢ t ∶ A [ σ ]ₛ → Γ ⊢ₛ ↑ · (σ , t) ∼ σ ∶ Δ
    ∼Assoc : ∀{Γ₄ Γ₃ Γ₂ Γ₁ σ₃ σ₂ σ₁} 
           → Γ₄ ⊢ₛ σ₃ ∶ Γ₃ → Γ₃ ⊢ₛ σ₂ ∶ Γ₂ → Γ₂ ⊢ₛ σ₁ ∶ Γ₁
           → Γ₄ ⊢ₛ (σ₁ · σ₂) · σ₃ ∼ σ₁ · (σ₂ · σ₃) ∶ Γ₁
    ∼Dist : ∀{Γ Γ' Δ σ τ t A} → Δ ⊢ A
          → Γ ⊢ₛ τ ∶ Γ' → Γ' ⊢ₛ σ ∶ Δ → Γ' ⊢ t ∶ A [ σ ]ₛ → Γ ⊢ₛ (σ , t) · τ ∼ σ · τ , t [ τ ]ₛ ∶ Δ # A
    ∼comp1 : ∀{Γ Δ σ σ' t t' A} → Δ ⊢ A → Γ ⊢ₛ σ ∼ σ' ∶ Δ → Γ ⊢ t ∼ t' ∶ A [ σ ]ₛ
           → Γ ⊢ₛ (σ , t) ∼ (σ' , t') ∶ Δ # A
    ∼comp2 : ∀{Γ₁ Γ₂ Γ₃ σ σ' τ τ'} → Γ₁ ⊢ₛ σ ∼ σ' ∶ Γ₂ → Γ₃ ⊢ₛ τ ∼ τ' ∶ Γ₁
           → Γ₃ ⊢ₛ (σ · τ) ∼ (σ' · τ') ∶ Γ₂
    ∼ext   : ∀{Γ A} → Γ ⊢ A → Γ # A ⊢ₛ (Id · ↑ , Var) ∼ Id ∶ Γ # A

≡tm : ∀{Γ A A' t t'} → A ≡ A' → t ≡ t' → Γ ⊢ t ∶ A → Γ ⊢ t' ∶ A'
≡tm refl refl tm = tm

≡∼ : ∀{Γ t t' s s' A A'}
   → t ≡ t' → s ≡ s' → A ≡ A'
   → Γ ⊢ t ∼ s ∶ A → Γ ⊢ t' ∼ s' ∶ A'
≡∼ refl refl refl eq = eq
