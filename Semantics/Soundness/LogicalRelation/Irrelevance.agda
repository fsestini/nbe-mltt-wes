module Semantics.Soundness.LogicalRelation.Irrelevance where

open import Data.Nat
open import Function
open import Data.Maybe
open import Syntax
open import Semantics.Domain
open import Semantics.Completeness
open import Semantics.Completeness.Lemmata
open import Data.Product renaming (_,_ to _,,_)
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Semantics.Soundness.LogicalRelation.Definition

open SemTy
open _●_∈ₜ_
open ⟦_⟧ₜ
open ⟦_⟧_∈ₜ_

ty-irrel𝒰 : ∀{Γ A B X Y} → A ≡ B → X ≡ Y → (ty : X ∈ₜ 𝒰) → (ty' : Y ∈ₜ 𝒰)
           → Γ ⊢ A ®𝒰 ty → Γ ⊢ B ®𝒰 ty'
ty-irrel𝒰 refl refl (uNe e) (uNe .e) rel = rel

tm-irrel𝒰 : ∀{Γ A B X Y t s a}
          → t ≡ s → A ≡ B → X ≡ Y
          → (ty : X ∈ₜ 𝒰) → (ty' : Y ∈ₜ 𝒰)
          → (p : P (El𝒰 ty) a) → (p' : P (El𝒰 ty') a)
          → Γ ⊢ t ∶ A ®𝒰 ty ∋ p → Γ ⊢ s ∶ B ®𝒰 ty' ∋ p'
tm-irrel𝒰 refl refl refl (uNe e) (uNe .e) p p' rel = rel         

mutual
  ty-irrel𝒯 : ∀{Γ A B X Y} → A ≡ B → X ≡ Y → (ty : X ∈ₜ 𝒯) → (ty' : Y ∈ₜ 𝒯)
             → Γ ⊢ A ® ty → Γ ⊢ B ® ty'
  ty-irrel𝒯 refl refl (𝒰⊆𝒯 x) (𝒰⊆𝒯 x₁) rel = ty-irrel𝒰 refl refl x x₁ rel
  ty-irrel𝒯 refl refl (𝒰⊆𝒯 ()) tU rel
  ty-irrel𝒯 refl refl (𝒰⊆𝒯 ()) (tPi pA x₁) rel
  ty-irrel𝒯 refl refl tU (𝒰⊆𝒯 ()) rel
  ty-irrel𝒯 refl refl tU tU rel = rel
  ty-irrel𝒯 refl refl (tPi pA x) (𝒰⊆𝒯 ()) rel
  ty-irrel𝒯 refl refl (tPi h1 h2) (tPi h1' h2') (_ ,, Bd ,, conv ,, h ,, hh) = 
    _ ,, Bd ,, conv ,, h ,, λ x p x₁ →
       let eq = Eval-fun (ev h1') (ev h1)
           p' = sameTerm𝒯≃ eq (∈t h1') (∈t h1) p
           k = hh x p' (tm-irrel𝒯 refl refl refl eq (∈t h1') (∈t h1) p p' x₁)
       in ty-irrel𝒯 refl (Eval-fun (ev (h2 p')) (ev (h2' p))) (∈t (h2 p')) (∈t (h2' p)) k

  tm-irrel𝒯 : ∀{Γ A B X Y t s a b}
            → t ≡ s → a ≡ b → A ≡ B → X ≡ Y
            → (ty : X ∈ₜ 𝒯) → (ty' : Y ∈ₜ 𝒯)
            → (p : P (El𝒯 ty) a) → (p' : P (El𝒯 ty') b)
            → Γ ⊢ t ∶ A ® ty ∋ p → Γ ⊢ s ∶ B ® ty' ∋ p'
  tm-irrel𝒯 refl refl refl refl (𝒰⊆𝒯 x) (𝒰⊆𝒯 y) p p' q = tm-irrel𝒰 refl refl refl x y p p' q
  tm-irrel𝒯 refl refl refl refl (𝒰⊆𝒯 ()) tU _ _ _
  tm-irrel𝒯 refl refl refl refl (𝒰⊆𝒯 ()) (tPi _ _) _ _ _
  tm-irrel𝒯 refl refl refl refl tU (𝒰⊆𝒯 ()) _ _ _
  tm-irrel𝒯 refl refl refl refl tU tU p p' (a ,, b ,, c) = a ,, ty-irrel𝒰 refl refl p p' b ,, c
  tm-irrel𝒯 refl refl refl refl (tPi _ _) (𝒰⊆𝒯 ()) _ _ _
  tm-irrel𝒯 {Γ} {A} {t = t} refl refl refl refl (tPi h1 h2) (tPi h1' h2') p p'
    (semLam t₁ ,, _ ,, tyconv ,, td ,, tmconv ,, rfenv ,, h) = semLam t₁ ,, _ ,, tyconv ,, 
      td ,, tmconv ,, rfenv ,, λ x q x₁ → 
        let eq = (Eval-fun (ev h1') (ev h1))
            p'' = (sameTerm𝒯≃ eq (∈t h1') (∈t h1) q)
            k = h x p'' (tm-irrel𝒯 refl refl refl eq (∈t h1') (∈t h1) q p'' x₁)
        in tm-irrel𝒯 refl (●-fun (↘ap (p p'')) (↘ap (p' q))) refl (Eval-fun (ev (h2 p'')) 
                     (ev (h2' q))) (∈t (h2 p'')) (∈t (h2' q)) (●∈tm (p p'')) (●∈tm (p' q)) k
  tm-irrel𝒯 {Γ} {A} {t = t} refl refl refl refl (tPi h1 h2) (tPi h1' h2') p p' (semNe e ,, proj₄) = 
    semNe e ,, proj₄


irrelₛ : ∀{Γ σ Δ ρ} (p p' : ρ ∈ₛ ⟦ Δ ⟧ₛ)
       → Γ ⊢ₛ σ ∶ Δ ® p → Γ ⊢ₛ σ ∶ Δ ® p'
irrelₛ .cEmpty cEmpty ◇® = ◇®
irrelₛ (cExt a b) (cExt x₁ x₂) (#® gu rel x) = #® gu (irrelₛ _ x₁ rel) 
  (tm-irrel𝒯 refl refl refl (Eval-fun (ev b) (ev x₂)) (inT b) (inT x₂) (nn b) (nn x₂) x)
irrelₛ p p' (∼® gu rel x) = ∼® gu (irrelₛ p p' rel) x
irrelₛ p p' (↑® rel x) = ↑® (irrelₛ p p' rel) x
