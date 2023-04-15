module Semantics.Soundness.Soundness where

open import Utils
open import Function
open import Semantics.Soundness.Fundamental
open import Semantics.Soundness.LogicalRelation
open import Syntax
open import Semantics.Domain
open import Semantics.Completeness

open import Data.Product renaming (_,_ to _,,_)
open import Syntax.Typed
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat

open _●_∈ₜ_
open ⟦_⟧≃⟦_⟧_∈ₜ_
open ⟦_⟧_∈ₜ_
open ⟦_⟧≃⟦_⟧_∈ₛ_
open ⟦_⟧ₜ
open SemTy

⊢idsub : ∀{Γ} (c : ⊢ Γ) → Γ ⊢ₛ idsub Γ ∶ Γ × Γ ⊢ₛ idsub Γ ∼ Id ∶ Γ
⊢idsub ⊢◇ = ⊢Id ⊢◇ ,, ∼refl (⊢Id ⊢◇)
⊢idsub (⊢# c x) = (⊢, (⊢· (proj₁ (⊢idsub c)) (⊢↑ x)) x tm) ,, 
       ∼trans (∼comp1 x (∼comp2 (proj₂ h) (∼refl (⊢↑ x))) (∼refl tm)) (∼ext x)
  where h = ⊢idsub c ; tm = (coe (var x) (∼symm (∼Sub' x 
               (∼trans (∼comp2 (proj₂ h) (∼refl (⊢↑ x))) (∼IdL (⊢↑ x))))))

idrel : ∀{Γ} (c : ⊢ Γ) → Γ ⊢ₛ idsub Γ ∶ Γ ® idenvp c
idrel ⊢◇ = ◇®
idrel (⊢# {Γ = Γ} {A = A} c x) = #® x (↑® h (rUp' x)) 
      (∼preservation-tm (∈ty hh) (hasNe (El𝒯 (∈ty hh)) (Lev (clen Γ))) 
        (∼symm (∼Sub' x (∼trans (∼comp2 (proj₂ h3) (∼refl (⊢↑ x))) (∼IdL (⊢↑ x))))) (∼refl (var x)) nne)
  where
    h = idrel c ; hh = proj₂ (models-ty x) (idenvp c) ; h3 = ⊢idsub c
    hA = fundamental-ty x h
    nne = (allNe (∈ty hh) (⊢# c x) (λ {Δ} {w} wp → 
                 let cmp = renComp wp (rUp x (rId c))
                 in  (∼trans (∼trans (∼scomp x (⊢↑ x) (renIsSub wp)) (∼Sub (∼symm (∼trans (∼Sub' x (proj₂ h3)) 
                           (∼Id x))) (∼trans (∼comp2 (∼symm (∼IdL (⊢↑ x))) (∼refl (renIsSub wp))) 
                             (∼symm (proj₂ (proj₂ cmp)))))) (convert-® (proj₁ (proj₂ cmp)) (∈ty hh) hA)))
             λ wp → ∼coe (renVar (⊢# c x) wp) (∼symm (∼trans (∼scomp x (⊢↑ x) (renIsSub wp)) (∼Sub' x (wup x wp)))))

soundness-ty : ∀{Γ A} → (p : Γ ⊢ A) → Γ ⊢ A ∼ nf-ty p
soundness-ty p = ∼trans (∼symm (∼trans (∼Id (sub p (proj₁ ids))) 
             (∼trans (∼Sub (∼refl p) (proj₂ ids)) (∼Id p)))) (convert-® (rId c) mm h)
  where c = invert-ctx-ty p
        h = fundamental-ty p (idrel c)
        mm = ∈ty ((proj₂ $ models-ty p) (idenvp c))
        ids = ⊢idsub c

soundness-tm : ∀{Γ t A} → (q : Γ ⊢ A) (p : Γ ⊢ t ∶ A) → Γ ⊢ t ∼ nf-tm p ∶ A
soundness-tm q p = ∼trans (∼symm (∼trans (∼Id 
                 (coe (sub p (proj₁ ids)) (∼trans (∼Sub' q (proj₂ ids)) (∼Id q)))
                 ) (∼trans (∼coe (∼Sub (∼refl p) (proj₂ ids)) 
             (∼trans (∼Sub (∼refl q) (proj₂ ids)) (∼Id q))) (∼Id p)))) (∼coe (convert-®-tm (rId c) (∈ty' mm) (∈tm mm) h) 
             (∼trans (∼Id (sub q (proj₁ ids))) (∼trans (∼Sub (∼refl q) (proj₂ ids)) (∼Id q))))
  where c = invert-ctx-tm p ; mm = proj₂ (models-tm p) (idenvp c)
        h = fundamental-tm p (idrel c) ; ids = ⊢idsub c
