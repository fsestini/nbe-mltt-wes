module Semantics.Soundness.LogicalRelation.Conversion where

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

open ⟦_⟧ₜ
open ⟦_⟧_∈ₜ_
open SemTy
open _●_∈ₜ_

convert-®𝒰-tm : ∀{Δ Γ t A a X w} 
    → Δ ⊢ᵣ w ∶ Γ → (ty : X ∈ₜ 𝒰) (p : a ∈ El𝒰 ty) → Γ ⊢ t ∶ A ®𝒰 ty ∋ p → Δ ⊢ t [ w ]ₛ ∼ reify (clen Δ) a ∶ A [ w ]ₛ
convert-®𝒰-tm w (uNe e) p rel = proj₂ (proj₂ rel) w

convert-®𝒰 : ∀{Δ Γ A X w} → Δ ⊢ᵣ w ∶ Γ → (ty : X ∈ₜ 𝒰) → Γ ⊢ A ®𝒰 ty → Δ ⊢ A [ w ]ₛ ∼ reify (clen Δ) X
convert-®𝒰 w (uNe e) r = proj₂ r w

IdWk-lemma : ∀{∇ w} → ∇ ⊢ᵣ w ∶ ◇ → ∇ ⊢ₛ Id · w ∼ wks (clen ∇) ∶ ◇
IdWk-lemma (rId x) = ∼IdL (⊢Id x)
IdWk-lemma (rUp x w) = ∼trans (∼IdL (⊢· (renIsSub w) (⊢↑ x))) 
  (∼comp2 (∼trans (∼symm (∼IdL (renIsSub w))) (IdWk-lemma w)) (∼refl (⊢↑ x)))
IdWk-lemma (rUp' x) = ∼refl (⊢· (⊢Id ⊢◇) (⊢↑ x))

mutual

  convert-®-tm : ∀{Γ Δ t A a w X} → Δ ⊢ᵣ w ∶ Γ
               → (ty : X ∈ₜ 𝒯) (p : a ∈ El𝒯 ty)
               → Γ ⊢ t ∶ A ® ty ∋ p → Δ ⊢ t [ w ]ₛ ∼ reify (clen Δ) a ∶ A [ w ]ₛ
  convert-®-tm w (𝒰⊆𝒯 x) p rel = convert-®𝒰-tm w x p rel
  convert-®-tm w tU p (proj₃ ,, conv ,, h) =
    ∼coe (h w) (∼symm (∼trans (∼Sub proj₃ (∼refl ww)) (∼Us ww))) where ww = renIsSub w
  convert-®-tm w (tPi pA x) p (semLam t ,, _ ,, tyconv ,, td ,, tmconv ,, envconv ,, hh) =
    ∼trans (∼Sub tmconv (∼refl ww)) (∼coe (∼trans (∼scomp (lam td) 
      sd ww) (∼Sub (∼refl (lam td)) (envconv w))) (∼symm (∼trans (∼Sub tyconv (∼refl ww)) 
          (∼scomp (Π (invert-ty td)) sd ww))))
    where ww = renIsSub w ; c = invert-ctx-tm (proj₁ (eq-lemma-tm tmconv))
          sd = (inverti-idsub-sub (proj₁ (eq-lemma-sub (envconv (rId c)))))
  convert-®-tm w (tPi pA x) p (semNe e ,, proj₄) = proj₁ proj₄ w

  convert-® : ∀{Δ Γ A X w} → Δ ⊢ᵣ w ∶ Γ → (ty : X ∈ₜ 𝒯) → Γ ⊢ A ® ty → Δ ⊢ A [ w ]ₛ ∼ reify (clen Δ) X
  convert-® w (𝒰⊆𝒯 x) rel = convert-®𝒰 w x rel
  convert-® w tU conv = ∼trans (∼Sub conv (∼refl (renIsSub w))) (∼Us (renIsSub w))
  convert-® w (tPi Ah Bh) (proj₃ ,, Bd ,, k ,, rels ,, h) = 
    ∼trans (∼Sub k (∼refl ww)) (∼trans (∼scomp pi sd ww) (∼Sub' pi (rels w)))
    where ww = renIsSub w ; pi = Π Bd ; c = invert-ctx-sub' ww
          sd = (inverti-idsub-sub (proj₁ (eq-lemma-sub (rels (rId c)))))

  convert-®-sub : ∀{Γ Δ ∇ w σ ρ} → ∇ ⊢ᵣ w ∶ Γ → (p : ρ ∈ₛ ⟦ Δ ⟧ₛ)
                → Γ ⊢ₛ σ ∶ Δ ® p → ∇ ⊢ₛ σ · w ∼ reifyEnv (clen ∇) ρ ∶ Δ
  convert-®-sub n .cEmpty ◇® = IdWk-lemma n
  convert-®-sub n .(cExt _ _) (#® {p = p} x rel x₁) = 
    ∼trans (∼Dist x wp sb td) (∼comp1 x (convert-®-sub n _ rel) 
      (∼coe (convert-®-tm n (inT p) (nn p) x₁) (∼scomp x sb wp)))
    where wp = renIsSub n ; sb = derₛ rel ; td = derₜ (inT p) (nn p) x₁
  convert-®-sub n p (↑® rel w) = ∼trans (∼Assoc (renIsSub n) (renIsSub w) (derₛ rel)) 
    (∼trans (∼comp2 (∼refl (derₛ rel)) (∼symm (proj₂ (proj₂ (renComp n w))))) 
      (convert-®-sub (proj₁ (proj₂ (renComp n w))) p rel))
  convert-®-sub n p (∼® x rel x₁) = ∼trans (∼comp2 x₁ (∼refl (renIsSub n))) (convert-®-sub n p rel)
