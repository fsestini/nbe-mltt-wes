module Semantics.Soundness.LogicalRelation.Kripke where

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
open import Semantics.Soundness.LogicalRelation.Preservation

open ⟦_⟧_∈ₜ_
open _●_∈ₜ_

mutual
  kripke-u-ty : ∀{Γ Δ A w X} → Δ ⊢ᵣ w ∶ Γ
              → (ty : X ∈ₜ 𝒰)
              → Γ ⊢ A ®𝒰 ty → Δ ⊢ A [ w ]ₛ ®𝒰 ty
  kripke-u-ty wp (uNe e) (_ ,, h) = invert-ctx-sub ww ,, λ x → 
    let cmp = renComp x wp in ∼trans (∼trans (∼scomp Ad ww (renIsSub x)) 
      (∼Sub' Ad (∼symm (proj₂ (proj₂ cmp))))) (h (proj₁ (proj₂ cmp)))
    where ww = renIsSub wp ; Ad = id-left-ty (h (rId (invert-ctx-sub' ww)))

  kripke-u-tm : ∀{Γ Δ t A a w X} → Δ ⊢ᵣ w ∶ Γ
              → (ty : X ∈ₜ 𝒰) (p : a ∈ El𝒰 ty)
              → Γ ⊢ t ∶ A ®𝒰 ty ∋ p → Δ ⊢ t [ w ]ₛ ∶ A [ w ]ₛ ®𝒰 ty ∋ p
  kripke-u-tm wp (uNe e) p (_ ,, h1 ,, h2) = invert-ctx-sub ww ,, 
    (λ x → let cmp = renComp x wp ; ww' = renIsSub x
           in ∼trans (∼trans (∼scomp Ad ww ww') (∼Sub' Ad (∼symm (proj₂ $ proj₂ $ cmp)))) (h1 (proj₁ $ proj₂ $ cmp))) ,, 
    λ x → let cmp = renComp x wp ; ww' = renIsSub x 
          in ∼coe (∼trans (∼scomp tm ww ww') (∼trans (∼Sub (∼refl tm) (∼symm (proj₂ $ proj₂ $ cmp))) (∼coe (h2 (proj₁ $ proj₂ $ cmp)) 
                          (∼Sub' Ad (proj₂ $ proj₂ $ cmp))))) (∼symm (∼scomp Ad ww ww'))
    where ww = renIsSub wp ; c = invert-ctx-sub' ww
          Ad = id-left-ty (h1 (rId (invert-ctx-sub' ww)))
          tm = id-left-tm $ h2 (rId c)

  kripke-tm : ∀{Γ Δ t A a w X} → Δ ⊢ᵣ w ∶ Γ
            → (ty : X ∈ₜ 𝒯) (p : a ∈ El𝒯 ty)
            → Γ ⊢ t ∶ A ® ty ∋ p → Δ ⊢ t [ w ]ₛ ∶ A [ w ]ₛ ® ty ∋ p
  kripke-tm wp (𝒰⊆𝒯 x) pa rel = kripke-u-tm wp x pa rel
  kripke-tm wp tU pa (conv ,, rel ,, h) = ∼trans (∼Sub conv (∼refl ww)) (∼Us ww) ,, 
    ((kripke-u-ty wp pa rel) ,, λ x → let cmp = renComp x wp in 
    ∼trans (∼trans (∼coe (∼scomp td ww (renIsSub x)) (∼Us (⊢· ww (renIsSub x)))) 
      (∼coe (∼Sub (∼refl td) (∼symm (proj₂ (proj₂ cmp)))) (∼Us (⊢· ww (renIsSub x))))) (h (proj₁ (proj₂ cmp))))
    where ww = renIsSub wp ; td = invert-idsub-tm (proj₁ (eq-lemma-tm (h (rId (invert-ctx-sub' ww)))))
  kripke-tm {w = w} wp (tPi pA x) pa (semLam t ,, (_ ,, σ) ,, tyconv ,, td ,, tmconv ,, envconv ,, h) = 
    (semLam t) ,, ((_ ,, (σ · w)) ,, (∼trans (∼Sub tyconv (∼refl ww)) 
      (∼scomp (Π (invert-ty td)) sd ww) ,, (td ,, (∼trans (∼Sub tmconv (∼refl ww)) (∼coe (∼scomp (lam td) sd ww) 
                 (∼symm (∼trans (∼Sub tyconv (∼refl ww)) (∼scomp (Π (invert-ty td)) sd ww)))) ,, 
      (λ x₁ → let cmp = renComp x₁ wp
              in ∼trans (∼trans (∼Assoc (renIsSub x₁) ww sd) 
                (∼comp2 (∼refl sd) (∼symm (proj₂ (proj₂ cmp))))) (envconv (proj₁ (proj₂ cmp)))) ,,
                λ { {s} {a} {∇} {w'} x₁ q x₂ → 
                    let cmp = renComp x₁ wp ; ss = derₜ (∈t pA) q x₂ ; Ad = (proj₂ $ split-ctx $ invert-ctx-tm td)
                        asd = h {s} {a} {∇} {proj₁ cmp} (proj₁ (proj₂ cmp)) q 
                            (∼preservation-tm (∈t pA) q (∼Sub' Ad
                              (∼trans (∼Assoc (renIsSub x₁) ww sd) (∼comp2 (∼refl sd) (∼symm (proj₂ $ proj₂ $ cmp))))) (∼refl ss) x₂)
                        uhm = (∼comp1 Ad (∼trans (∼comp2 (∼refl sd) (proj₂ $ proj₂ cmp)) 
                                         (∼symm (∼Assoc (renIsSub x₁) ww sd))) (∼refl (coe ss (∼Sub' Ad (∼trans (∼Assoc (renIsSub x₁) ww sd) 
                                           (∼comp2 (∼refl sd) (∼symm (proj₂ $ proj₂ cmp))))))))
                    in  ∼preservation-tm (∈t (x q)) (●∈tm (pa q)) (∼Sub' (invert-ty td) uhm) (∼Sub (∼refl td) uhm) asd }))))
    where ww = renIsSub wp 
          sd = inverti-idsub-sub (proj₁ (eq-lemma-sub (envconv (rId (invert-ctx-sub' ww)))))
  kripke-tm wp (tPi pA x) pa (semNe e ,, h ,, c) = 
    (semNe e) ,, (λ x → let cmp = renComp x wp ; ww' = renIsSub x in
      ∼coe (∼trans (∼coe (∼trans (∼scomp td ww ww') (∼Sub (∼refl td) (∼symm (proj₂ $ proj₂ $ cmp)))) 
        (∼Sub' (invert-ty td) (∼symm (proj₂ $ proj₂ $ cmp)))) (h (proj₁ (proj₂ cmp)))) 
          (∼trans (∼Sub' Ad (proj₂ $ proj₂ $ cmp)) (∼symm (∼scomp Ad ww ww')))) ,, (invert-ctx-sub ww)
    where ww = renIsSub wp ; td = id-left-tm (h (rId c)) ; Ad = invert-ty td
