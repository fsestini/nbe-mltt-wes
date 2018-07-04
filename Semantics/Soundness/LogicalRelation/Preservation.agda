module Semantics.Soundness.LogicalRelation.Preservation where

open import Data.Nat
open import Function
open import Data.Maybe
open import Syntax
open import Semantics.Domain
open import Semantics.Completeness
open import Data.Product renaming (_,_ to _,,_)
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Semantics.Soundness.LogicalRelation.Definition

open ⟦_⟧_∈ₜ_
open _●_∈ₜ_

∼preservation𝒰 : ∀{Γ A B X} (ty : X ∈ₜ 𝒰) → Γ ⊢ A ∼ B → Γ ⊢ A ®𝒰 ty → Γ ⊢ B ®𝒰 ty
∼preservation𝒰 (uNe e) eq (Ad ,, h) = 
  invert-ctx-ty (proj₁ (eq-lemma-ty eq)) ,, 
  λ x → ∼trans (∼Sub (∼symm eq) (∼refl (renIsSub x))) (h x)

∼preservation : ∀{Γ A B X} (ty : X ∈ₜ 𝒯)
               → Γ ⊢ A ∼ B → Γ ⊢ A ® ty → Γ ⊢ B ® ty
∼preservation (𝒰⊆𝒯 x) eq rel = ∼preservation𝒰 x eq rel
∼preservation tU eq rel = ∼trans (∼symm eq) rel
∼preservation (tPi pA x) eq (_ ,, b ,, rr ,, h ,, hh) = 
  _ ,, b ,, ∼trans (∼symm eq) rr ,, h ,, hh

∼preservation𝒰-tm : ∀{Γ A B X t s a} (ty : X ∈ₜ 𝒰) (d : a ∈ El𝒰 ty )
  → Γ ⊢ A ∼ B → Γ ⊢ t ∼ s ∶ A → Γ ⊢ t ∶ A ®𝒰 ty ∋ d → Γ ⊢ s ∶ B ®𝒰 ty ∋ d
∼preservation𝒰-tm (uNe e) p eq1 eq2 (td ,, h1 ,, h2) = 
  td ,, (λ x → ∼trans (∼Sub (∼symm eq1) (∼refl (renIsSub x))) (h1 x)) ,, 
        (λ x → ∼coe (∼trans (∼Sub (∼symm eq2) (∼refl (renIsSub x))) (h2 x)) (∼Sub eq1 (∼refl (renIsSub x))))
        
∼preservation-tm : ∀{Γ A B X t s a} (ty : X ∈ₜ 𝒯) (d : a ∈ El𝒯 ty )
  → Γ ⊢ A ∼ B → Γ ⊢ t ∼ s ∶ A → Γ ⊢ t ∶ A ® ty ∋ d → Γ ⊢ s ∶ B ® ty ∋ d
∼preservation-tm (𝒰⊆𝒯 x) p eq1 eq2 rel = ∼preservation𝒰-tm x p eq1 eq2 rel
∼preservation-tm tU p eq1 eq2 (a ,, b ,, d) = 
  ∼trans (∼symm eq1) a ,, (∼preservation𝒰 p (∼El (∼coe eq2 a)) b) ,, λ x → let w = ∼refl (renIsSub x) 
  in ∼trans (∼coe (∼Sub (∼symm eq2) w) (∼trans (∼Sub a w) (∼Us (renIsSub x)))) (d x)
∼preservation-tm (tPi pA x) p eq1 eq2 (semLam t ,, _ ,, b ,, k ,, k2 ,, k3 ,, h) = 
  semLam t ,, _ ,, ∼trans (∼symm eq1) b ,, k ,, ∼coe (∼trans (∼symm eq2) k2) eq1 ,, k3 ,, h
∼preservation-tm (tPi pA x) p eq1 eq2 (semNe e ,, kk ,, kkk) = semNe e ,, (λ w → 
  let www = ∼refl (renIsSub w) in ∼coe (∼trans (∼Sub (∼symm eq2) www) (kk w)) 
    (∼Sub eq1 www)) ,, kkk
