module Syntax.Typed.Inversion where

open import Syntax.Term
open import Syntax.Typed.System
open import Data.Product

split-ctx : ∀{Γ A} → ⊢ Γ # A → ⊢ Γ × Γ ⊢ A
split-ctx (⊢# c x) = c , x

mutual

  invert-ctx-ty : ∀{Γ A} → Γ ⊢ A → ⊢ Γ
  invert-ctx-ty (U c) = c
  invert-ctx-ty (Π t₁) = proj₁ (split-ctx (invert-ctx-ty t₁))
  invert-ctx-ty (El x) = invert-ctx-tm x
  invert-ctx-ty (sub t x) = invert-ctx-sub x

  invert-ctx-tm : ∀{Γ t A} → Γ ⊢ t ∶ A → ⊢ Γ
  invert-ctx-tm (var x) = ⊢# (invert-ctx-ty x) x
  invert-ctx-tm (lam t) = proj₁ (split-ctx (invert-ctx-tm t))
  invert-ctx-tm (app x x₂ t t₁) = invert-ctx-tm t
  invert-ctx-tm (coe t x) = invert-ctx-tm t
  invert-ctx-tm (sub t x₁) = invert-ctx-sub x₁

  invert-ctx-sub : ∀{Δ σ Γ} → Δ ⊢ₛ σ ∶ Γ → ⊢ Δ
  invert-ctx-sub (⊢Id c) = c
  invert-ctx-sub (⊢, s x x₁) = invert-ctx-tm x₁
  invert-ctx-sub (⊢· s s₁) = invert-ctx-sub s₁
  invert-ctx-sub (⊢↑ t) = ⊢# (invert-ctx-ty t) t

invert-ctx-sub' : ∀{Δ σ Γ} → Δ ⊢ₛ σ ∶ Γ → ⊢ Γ
invert-ctx-sub' (⊢Id x) = x
invert-ctx-sub' (⊢, s x x₁) = ⊢# (invert-ctx-sub' s) x
invert-ctx-sub' (⊢· s s₁) = invert-ctx-sub' s
invert-ctx-sub' (⊢↑ x) = invert-ctx-ty x

∼Sub' : ∀{Γ A Δ σ τ} → Δ ⊢ A → Γ ⊢ₛ σ ∼ τ ∶ Δ → Γ ⊢ A [ σ ]ₛ ∼ A [ τ ]ₛ
∼Sub' Ad eq = ∼Sub (∼refl Ad) eq

∼compdist-ty : ∀{Γ ∇ Δ A B s τ σ} 
             → Δ # A ⊢ B → Γ ⊢ₛ τ ∶ ∇ → ∇ ⊢ₛ σ ∶ Δ → ∇ ⊢ s ∶ A [ σ ]ₛ
             → Γ ⊢ B [ σ , s ]ₛ [ τ ]ₛ ∼ B [ (σ · τ) , s [ τ ]ₛ ]ₛ
∼compdist-ty Bd tu sd s = ∼trans (∼scomp Bd (⊢, sd Ad s) tu) (∼Sub' Bd (∼Dist Ad tu sd s))
  where Ad = proj₂ (split-ctx (invert-ctx-ty Bd))

mutual

  invert-ty : ∀{Γ t A} → Γ ⊢ t ∶ A → Γ ⊢ A
  invert-ty (var x) = sub x (⊢↑ x)
  invert-ty (lam t) = Π (invert-ty t)
  invert-ty (app x x₁ t t₁) = sub x₁ (⊢, x (proj₂ (split-ctx (invert-ctx-ty x₁))) t₁)
  invert-ty (coe t x) = proj₂ (eq-lemma-ty x)
  invert-ty (sub t x₁) = sub (invert-ty t) x₁

  sub+comp : ∀{Γ Δ ∇ A σ τ t} → ∇ ⊢ t ∶ A → Δ ⊢ₛ σ ∶ ∇ → Γ ⊢ₛ τ ∶ Δ
           → Γ ⊢ t [ σ ]ₛ [ τ ]ₛ ∶ A [ σ · τ ]ₛ
  sub+comp t sb tu = coe (sub (sub t sb) tu) (∼scomp (invert-ty t) sb tu)

  invert-ty-eq : ∀{Γ t s A} → Γ ⊢ t ∼ s ∶ A → Γ ⊢ A
  invert-ty-eq (∼refl x) = invert-ty x
  invert-ty-eq (∼symm eq) = invert-ty-eq eq
  invert-ty-eq (∼trans eq eq₁) = invert-ty-eq eq
  invert-ty-eq (∼β x x₁ x₂) = sub (invert-ty x) (⊢, x₁ Ad x₂)
    where Ad = proj₂ (split-ctx (invert-ctx-ty (invert-ty x)))
  invert-ty-eq (∼app eq eq₁ x x₁) =
    sub x₁ (⊢, x (proj₂ (split-ctx (invert-ctx-ty x₁))) (proj₁ h))
    where h = eq-lemma-tm eq₁
  invert-ty-eq (∼coe eq x) = proj₂ (eq-lemma-ty x)
  invert-ty-eq (∼Sub eq x) = sub (invert-ty-eq eq) (proj₁ (eq-lemma-sub x))
  invert-ty-eq (∼Id x) = invert-ty x
  invert-ty-eq (∼sapp x x₁ x₂ x₃ Bd) = 
    sub Bd (⊢, (⊢· x₂ x₃) Ad (coe (sub x₁ x₃) (∼scomp Ad x₂ x₃)))
    where Ad = proj₂ (split-ctx (invert-ctx-ty Bd))
  invert-ty-eq (∼scomp x x₁ x₂) = sub (invert-ty x) (⊢· x₁ x₂)
  invert-ty-eq (∼var x x₁ x₂) = invert-ty x₂

  eq-lemma-ty : ∀{Γ A B} → Γ ⊢ A ∼ B → Γ ⊢ A × Γ ⊢ B
  eq-lemma-ty (∼refl x) = x , x
  eq-lemma-ty (∼symm eq) = (proj₂ h) , (proj₁ h)
    where h = eq-lemma-ty eq
  eq-lemma-ty (∼trans eq eq₁) = proj₁ h , proj₂ h'
    where h = eq-lemma-ty eq ; h' = eq-lemma-ty eq₁
  eq-lemma-ty (∼El x) = (El (proj₁ h)) , (El (proj₂ h))
    where h = eq-lemma-tm x
  eq-lemma-ty (∼Us x) = (sub (U (invert-ctx-sub' x)) x) , (U (invert-ctx-sub x))
  eq-lemma-ty (∼Sub eq x) = sub (proj₁ h) (proj₁ h') , sub (proj₂ h) (proj₂ h')
    where h = eq-lemma-ty eq ; h' = eq-lemma-sub x
  eq-lemma-ty (∼scomp x x₁ x₂) = (sub (sub x x₁) x₂) , (sub x (⊢· x₁ x₂))
  eq-lemma-ty (∼Id x) = sub x (⊢Id (invert-ctx-ty x)) , x

  eq-lemma-tm : ∀{Γ t s A} → Γ ⊢ t ∼ s ∶ A → Γ ⊢ t ∶ A × Γ ⊢ s ∶ A
  eq-lemma-tm (∼refl x) = x , x
  eq-lemma-tm (∼symm eq) = proj₂ h , proj₁ h
    where h = eq-lemma-tm eq
  eq-lemma-tm (∼trans eq eq₁) = proj₁ h , proj₂ h'
    where h = eq-lemma-tm eq ; h' = eq-lemma-tm eq₁
  eq-lemma-tm (∼β x x₁ x₂) = (app x₁ (invert-ty x) 
    (sub (lam x) x₁) x₂) , (sub x (⊢, x₁ (proj₂ (split-ctx (invert-ctx-tm x))) x₂))
  eq-lemma-tm (∼app eq eq₁ sb Bd) = 
    app sb Bd (proj₁ h) (proj₁ h') , coe (app sb Bd (proj₂ h) (proj₂ h')) 
      (∼Sub (∼refl Bd) (∼Cons (∼refl sb) (∼symm eq₁) (proj₂ (split-ctx (invert-ctx-ty Bd)))))
    where h = eq-lemma-tm eq ; h' = eq-lemma-tm eq₁
  eq-lemma-tm (∼coe eq x) = coe (proj₁ h) x , coe (proj₂ h) x
    where h = eq-lemma-tm eq
  eq-lemma-tm (∼Sub eq x) = 
    sub (proj₁ h) (proj₁ h') , 
    coe (sub (proj₂ h) (proj₂ h')) (∼Sub (∼refl (invert-ty-eq eq)) (∼symm x))
    where h = eq-lemma-tm eq ; h' = eq-lemma-sub x
  eq-lemma-tm (∼Id x) = (coe (sub x (⊢Id (invert-ctx-tm x))) (∼Id (invert-ty x))) , x
  eq-lemma-tm (∼sapp x x₁ x₂ x₃ Bd) = 
    (coe (sub (app x₂ Bd x x₁) x₃) (∼compdist-ty Bd x₃ x₂ x₁)) , 
      app (⊢· x₂ x₃) Bd (coe (sub x x₃) (∼scomp (Π Bd) x₂ x₃)) (coe (sub x₁ x₃) (∼scomp Ad x₂ x₃))
    where Ad = proj₂ (split-ctx (invert-ctx-ty Bd))
  eq-lemma-tm (∼scomp x x₁ x₂) = sub+comp x x₁ x₂ , sub x (⊢· x₁ x₂)
  eq-lemma-tm (∼var Ad x x₁) = (coe (sub (var Ad) (⊢, x Ad x₁)) 
    (∼trans (∼scomp Ad (⊢↑ Ad) (⊢, x Ad x₁)) (∼Sub (∼refl Ad) (∼Up x Ad x₁)))) , x₁

  eq-lemma-sub : ∀{Γ Δ σ τ} → Δ ⊢ₛ σ ∼ τ ∶ Γ → Δ ⊢ₛ σ ∶ Γ × Δ ⊢ₛ τ ∶ Γ
  eq-lemma-sub (∼refl x) = x , x
  eq-lemma-sub (∼symm eq) = proj₂ h , proj₁ h
    where h = eq-lemma-sub eq
  eq-lemma-sub (∼trans eq eq₁) = (proj₁ h) , (proj₂ h')
    where h = eq-lemma-sub eq ; h' = eq-lemma-sub eq₁
  eq-lemma-sub (∼Cons eq x Ad) = ⊢, (proj₁ h) Ad (proj₁ h') , ⊢, (proj₂ h) Ad 
    (coe (proj₂ h') (∼Sub (∼refl Ad) eq))
    where h = eq-lemma-sub eq ; h' = eq-lemma-tm x
  eq-lemma-sub (∼IdL x) = (⊢· (⊢Id (invert-ctx-sub' x)) x) , x
  eq-lemma-sub (∼IdR x) = (⊢· x (⊢Id (invert-ctx-sub x))) , x
  eq-lemma-sub (∼Up x Ad x₁) = (⊢· (⊢↑ Ad) (⊢, x Ad x₁)) , x
    where h = invert-ty x₁
  eq-lemma-sub (∼Assoc x x₁ x₂) = (⊢· (⊢· x₂ x₁) x) , (⊢· x₂ (⊢· x₁ x))
  eq-lemma-sub (∼Dist Ad x x₁ x₂) = (⊢· (⊢, x₁ Ad x₂) x) , (⊢, (⊢· x₁ x) Ad (coe (sub x₂ x) (∼scomp Ad x₁ x)))
  eq-lemma-sub (∼comp1 ty eq x) = (⊢, (proj₁ h1) ty (proj₁ h2)) , ⊢, (proj₂ h1) ty (coe (proj₂ h2) (∼Sub (∼refl ty) eq))
    where h1 = eq-lemma-sub eq ; h2 = eq-lemma-tm x
  eq-lemma-sub (∼comp2 eq eq₁) = ⊢· (proj₁ h1) (proj₁ h2) , ⊢· (proj₂ h1) (proj₂ h2)
    where h1 = eq-lemma-sub eq ; h2 = eq-lemma-sub eq₁
  eq-lemma-sub (∼ext ty) = (⊢, (⊢· (⊢Id (invert-ctx-ty ty)) (⊢↑ ty)) ty (coe (var ty) 
    (∼Sub' ty (∼symm (∼IdL (⊢↑ ty)))))) , 
    ⊢Id (⊢# (invert-ctx-ty ty) ty)

invert-idsub-tm : ∀{Γ t A} → Γ ⊢ t [ Id ]ₛ ∶ A → Γ ⊢ t ∶ A
invert-idsub-tm (coe tm x) = coe (invert-idsub-tm tm) x
invert-idsub-tm (sub tm (⊢Id x)) = coe tm (∼symm (∼Id (invert-ty tm)))

invert-idsub-ty : ∀{Γ A} → Γ ⊢ A [ Id ]ₛ → Γ ⊢ A
invert-idsub-ty (El x) = El (invert-idsub-tm x)
invert-idsub-ty (sub ty (⊢Id x)) = ty

inverti-idsub-sub : ∀{Γ Δ σ} → Γ ⊢ₛ σ · Id ∶ Δ → Γ ⊢ₛ σ ∶ Δ
inverti-idsub-sub (⊢· sb (⊢Id x)) = sb
