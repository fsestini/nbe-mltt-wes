module Semantics.Completeness.Completeness where

open import Function
open import Data.Nat
open import Data.Maybe
open import Syntax
open import Semantics.Domain
open import Semantics.Completeness.Type
open import Semantics.Completeness.Lemmata
open import Data.Product renaming (_,_ to _,,_ ; proj₁ to p1 ; proj₂ to p2)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Syntax.Typed
open import Semantics.Completeness.Rule

open SemTy
open ⟦_⟧≃⟦_⟧_∈ₜ_
open ⟦_⟧≃⟦_⟧_∈ₛ_
open ⟦_⟧ₜ
open ⟦_⟧_∈ₜ_

idenvp : ∀{Γ} → ⊢ Γ → idenv Γ ∈ₛ ⟦ Γ ⟧ₛ
idenvp ⊢◇ = cEmpty
idenvp (⊢# c x) = cExt (idenvp c) ⟨ (↘t1 h) ∣ (∈ty h) 
       ∣ (hasNe (El𝒯 (∈ty h)) (Lev (clen _))) ⟩
  where h = p2 (models-ty x) (idenvp c)

nf-ty : ∀{Γ A} → Γ ⊢ A → Term
nf-ty {Γ} ty = reify (clen Γ) (res ((p2 $ models-ty ty) (idenvp (invert-ctx-ty ty))))

nf-tm : ∀{Γ t A} → Γ ⊢ t ∶ A → Term
nf-tm {Γ} tm = reify (clen Γ) (res (p2 (models-tm tm) (idenvp (invert-ctx-tm tm))))

completeness-ty : ∀{Γ A B} → (eq : Γ ⊢ A ∼ B) → nf-ty (p1 (eq-lemma-ty eq)) ≡ nf-ty (p2 (eq-lemma-ty eq))
completeness-ty {Γ} eq = 
  trans (cong nf (Eval-fun (↘t1 hA) (↘t1 h))) (cong nf (Eval-fun (↘t2 h) (↘t2 hB)))
  where Ad = p1 $ eq-lemma-ty eq ; Bd = p2 $ eq-lemma-ty eq
        c = invert-ctx-ty Ad ; c' = invert-ctx-ty Bd
        h = models-ty-eq eq (idenvp c)
        hA = (p2 $ models-ty Ad) (idenvp c)
        hB = (p2 $ models-ty Bd) (idenvp c')
        n = clen Γ ; nf = reify n

completeness-tm : ∀{Γ t s A}
                → (eq : Γ ⊢ t ∼ s ∶ A) → nf-tm (p1 (eq-lemma-tm eq)) ≡ nf-tm (p2 (eq-lemma-tm eq))
completeness-tm {Γ} eq =
  trans (cong nf (Eval-fun (↘t1 hA) (↘t1 h))) (cong nf (Eval-fun (↘t2 h) (↘t2 hB)))
  where td = p1 (eq-lemma-tm eq) ; sd = p2 (eq-lemma-tm eq)
        c = invert-ctx-tm td ; c' = invert-ctx-tm sd
        h = p2 (models-tm-eq eq) (idenvp c)
        hA = p2 (models-tm td) (idenvp c)
        hB = p2 (models-tm sd) (idenvp c')
        n = clen Γ ; nf = reify n
