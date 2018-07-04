module Semantics.Domain where

open import Utils
open import Syntax
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Product renaming (_,_ to _,,_)

mutual

  data D : Set where
    DNe : Dne → D
    Dλ : Term → Env → D
    DΠ : Term → Term → Env → D
    DU : D

  data Dne : Set where
    Lev : ℕ → Dne
    NeApp : Dne → D → Dne

  data Env : Set where
    ε : Env
    _,_ : Env → D → Env

isDne : D → Set
isDne (DNe x) = ⊤
isDne (Dλ x x₁) = ⊥
isDne (DΠ d x x₁) = ⊥
isDne DU = ⊥

wks : ℕ → Subst
wks zero = Id
wks (suc n) = wks n · ↑

mutual

  data Nfs : Subst → Set where
    nfsId : Nfs Id
    nfsCons : ∀{σ a} → Nfs σ → Nf a → Nfs (σ , a)
    nfsUp   : ∀{σ} → Nfs σ → Nfs (σ · ↑)

  data Nf : Term → Set where
    nfNe : ∀{e} → Ne e → Nf e
    nfLam : ∀{t σ} → Nfs σ → Nf ((Lam t) [ σ ]ₛ)
    nfPi  : ∀{A B σ} → Nfs σ → Nf ((Π A B) [ σ ]ₛ)
    nfU   : Nf U
    
  data Ne : Term → Set where
    neVar : ∀{n} → Ne (Var [ wks n ]ₛ)
    neApp : ∀{e t} → Ne e → Nf t → Ne (e · t)

lookup : Env → ℕ → D
lookup ε n = DU
lookup (e , x) zero = x
lookup (e , x) (suc n) = lookup e n

mutual

  infix 4 ⟦_⟧ₛ_↘_
  data ⟦_⟧ₛ_↘_ : Subst → Env → Env → Set where
    sId : ∀{ρ} → ⟦ Id ⟧ₛ ρ ↘ ρ
    sCons : ∀{σ t ρ ρ' a} → ⟦ σ ⟧ₛ ρ ↘ ρ' → ⟦ t ⟧ ρ ↘ a → ⟦ σ , t ⟧ₛ ρ ↘ ρ' , a
    sComp : ∀{σ τ ρ ρ' ρ''} → ⟦ τ ⟧ₛ ρ ↘ ρ' → ⟦ σ ⟧ₛ ρ' ↘ ρ'' → ⟦ σ · τ ⟧ₛ ρ ↘ ρ''
    sUp   : ∀{ρ a} → ⟦ ↑ ⟧ₛ (ρ , a) ↘ ρ

  infix 4 _●_↘_
  data _●_↘_ : D → D → D → Set where
    ●β : ∀{t ρ a b} → ⟦ t ⟧ ρ , a ↘ b → Dλ t ρ ● a ↘ b
    ●Ne : ∀{e d} → DNe e ● d ↘ DNe (NeApp e d)

  infix 4 ⟦_⟧_↘_
  data ⟦_⟧_↘_ : Term → Env → D → Set where
    eVar : ∀{ρ a} → ⟦ Var ⟧ (ρ , a) ↘ a
    eLam : ∀{t ρ} → ⟦ Lam t ⟧ ρ ↘ Dλ t ρ
    eApp : ∀{t s ρ a b c} → ⟦ t ⟧ ρ ↘ a → ⟦ s ⟧ ρ ↘ b → a ● b ↘ c → ⟦ t · s ⟧ ρ ↘ c
    ePi  : ∀{A B ρ} → ⟦ Π A B ⟧ ρ ↘ DΠ A B ρ
    eU   : ∀{ρ} → ⟦ U ⟧ ρ ↘ DU
    eSub : ∀{σ t a ρ ρ'} → ⟦ σ ⟧ₛ ρ ↘ ρ' → ⟦ t ⟧ ρ' ↘ a → ⟦ t [ σ ]ₛ ⟧ ρ ↘ a

mutual
  Eval-fun : ∀{t ρ a b} → ⟦ t ⟧ ρ ↘ a → ⟦ t ⟧ ρ ↘ b → a ≡ b
  Eval-fun eVar eVar = refl
  Eval-fun eLam eLam = refl
  Eval-fun (eApp e1 e2 x) (eApp e3 e4 x₁) 
    rewrite Eval-fun e1 e3 | Eval-fun e2 e4 = ●-fun x x₁
  Eval-fun ePi ePi = refl
  Eval-fun eU eU = refl
  Eval-fun (eSub x e1) (eSub x₁ e2)
    rewrite Evals-fun x x₁ = Eval-fun e1 e2
  
  Evals-fun : ∀{σ ρ ρ1 ρ2} → ⟦ σ ⟧ₛ ρ ↘ ρ1 → ⟦ σ ⟧ₛ ρ ↘ ρ2 → ρ1 ≡ ρ2
  Evals-fun sId sId = refl
  Evals-fun (sCons e1 x) (sCons e2 x₁)
    rewrite Evals-fun e1 e2 | Eval-fun x x₁ = refl
  Evals-fun (sComp e1 e2) (sComp e3 e4)
    rewrite Evals-fun e1 e3 | Evals-fun e2 e4 = refl
  Evals-fun sUp sUp = refl
  
  ●-fun : ∀{a b c d} → a ● b ↘ c → a ● b ↘ d → c ≡ d
  ●-fun (●β x) (●β x₁) = Eval-fun x x₁
  ●-fun ●Ne ●Ne = refl
  
≡Eval : ∀{t ρ a b} → ⟦ t ⟧ ρ ↘ a → b ≡ a → ⟦ t ⟧ ρ ↘ b
≡Eval e refl = e

≡Evals : ∀{t ρ a b} → ⟦ t ⟧ₛ ρ ↘ a → b ≡ a → ⟦ t ⟧ₛ ρ ↘ b
≡Evals e refl = e

≡Eval' : ∀{t ρ ρ' a} → ⟦ t ⟧ ρ ↘ a → ρ ≡ ρ' → ⟦ t ⟧ ρ' ↘ a
≡Eval' e refl = e

data _⊢ᵣ_∶_ : Ctxt → Subst → Ctxt → Set where
  rId : ∀{Γ} → ⊢ Γ → Γ ⊢ᵣ Id ∶ Γ
  rUp : ∀{Γ Δ A r} → Γ ⊢ A → Γ ⊢ᵣ r ∶ Δ → (Γ # A) ⊢ᵣ (r · ↑) ∶ Δ
  rUp' : ∀{Γ A} → Γ ⊢ A → (Γ # A) ⊢ᵣ ↑ ∶ Γ

renIsSub : ∀{Δ Γ w} → Δ ⊢ᵣ w ∶ Γ → Δ ⊢ₛ w ∶ Γ
renIsSub (rId c) = ⊢Id c -- ⊢Id
renIsSub (rUp Ad w) = ⊢· (renIsSub w) (⊢↑ Ad)
renIsSub (rUp' Ad) = (⊢↑ Ad)

renComp : ∀{∇ Δ Γ w1 w2} → ∇ ⊢ᵣ w1 ∶ Δ → Δ ⊢ᵣ w2 ∶ Γ → Σ Subst λ w → (∇ ⊢ᵣ w ∶ Γ) × (∇ ⊢ₛ w ∼ w2 · w1 ∶ Γ)
renComp (rId c) w2 = _ ,, w2 ,, ∼symm (∼IdR (renIsSub w2))
renComp (rUp Ad w1) w2 = _ ,, rUp Ad (proj₁ (proj₂ (renComp w1 w2))) ,, 
        ∼trans (∼comp2 (proj₂ (proj₂ (renComp w1 w2))) (∼refl (⊢↑ Ad))) 
          (∼Assoc (⊢↑ Ad) (renIsSub w1) (renIsSub w2))
renComp (rUp' Ad) w2 = _ ,, rUp Ad w2 ,, ∼refl (⊢· (renIsSub w2) (⊢↑ Ad))

postulate minus-prop : ∀{n m} → n ≥ m → suc n - m ≡ suc (n - m)

wk-len : ∀{Γ Δ A w} → Γ ⊢ᵣ w ∶ (Δ # A) → clen Γ > clen Δ
wk-len (rId x) = s≤s (≤refl (clen _))
wk-len (rUp x w) = >succ (wk-len w)
wk-len (rUp' x) = >succ (s≤s (≤refl _))

wer : ∀{n m} → n > m → wks (n - m) ≡ wks (pred (n - m)) · ↑
wer {suc n} (s≤s p) rewrite minus-prop p = refl

wup : ∀{Δ Γ A w} → Γ ⊢ A → Δ ⊢ᵣ w ∶ (Γ # A) → Δ ⊢ₛ ↑ · w ∼ w · ↑ ∶ Γ
wup a (rId x) = ∼trans (∼IdR (⊢↑ a)) (∼symm (∼IdL (⊢↑ a)))
wup a (rUp x w) = ∼trans (∼symm (∼Assoc (⊢↑ x) (renIsSub w) (⊢↑ a))) (∼comp2 h (∼refl (⊢↑ x)))
  where h = wup a w
wup a (rUp' x) = ∼refl (⊢· (⊢↑ a) (⊢↑ x))

postulate
  obv : ∀ n → pred (suc n - n) ≡ 0
  obv2 : ∀ n → suc (suc n) - n ≡ 2

renVar' : ∀{Δ w Γ A} → ⊢ Γ # A → Δ ⊢ᵣ w ∶ (Γ # A) → Δ ⊢ₛ w ∼ wks (pred (clen Δ - clen Γ)) ∶ Γ # A
renVar' {Γ = Γ} c (rId x) rewrite obv (clen Γ) = ∼refl (⊢Id x)
renVar' {Γ = Δ} c (rUp {Γ = Γ} x w) rewrite minus-prop (wk-len w) | wer (wk-len w) = ∼comp2 (renVar' c w) (∼refl (⊢↑ x))
renVar' {Γ = Γ} c (rUp' x) rewrite obv2 (clen Γ) = ∼symm (∼IdL (⊢↑ x))

renVar : ∀{Δ w Γ A} → ⊢ Γ # A → Δ ⊢ᵣ w ∶ (Γ # A) → Δ ⊢ Var [ w ]ₛ ∼ Var [ wks (pred (clen Δ - clen Γ)) ]ₛ ∶ A [ w · ↑ ]ₛ
renVar (⊢# c a) wp = ∼coe (∼Sub (∼refl (var a)) (renVar' (⊢# c a) wp)) (∼trans (∼scomp a (⊢↑ a) (renIsSub wp)) (∼Sub' a (wup a wp)))

mutual

  reify : ℕ → D → Term
  reify n (DNe x) = reifyNe n x
  reify n (Dλ t ρ) = Lam t [ reifyEnv n ρ ]ₛ
  reify n (DΠ A B ρ) = (Π A B) [ reifyEnv n ρ ]ₛ
  reify n DU = U

  reifyNe : ℕ → Dne → Term
  reifyNe n (Lev x) = Var [ wks (n - suc x) ]ₛ
  reifyNe n (NeApp e x) = reifyNe n e · reify n x

  reifyEnv : ℕ → Env → Subst
  reifyEnv n ε = wks n
  reifyEnv n (e , x) = reifyEnv n e , reify n x

mutual

  D-is-Nf : ∀{n} → (d : D) → Nf (reify n d)
  D-is-Nf (DNe x) = nfNe (Dne-is-Ne x)
  D-is-Nf (Dλ x x₁) = nfLam (Env-is-Nfs x₁)
  D-is-Nf (DΠ d x x₁) = nfPi (Env-is-Nfs x₁)
  D-is-Nf DU = nfU
  
  Dne-is-Ne : ∀{n} → (d : Dne) → Ne (reifyNe n d)
  Dne-is-Ne (Lev x) = neVar
  Dne-is-Ne (NeApp d x) = neApp (Dne-is-Ne d) (D-is-Nf x)

  Env-is-Nfs : ∀{n} → (e : Env) → Nfs (reifyEnv n e)
  Env-is-Nfs {zero} ε = nfsId
  Env-is-Nfs {suc n} ε = nfsUp (Env-is-Nfs ε)
  Env-is-Nfs (e , x) = nfsCons (Env-is-Nfs e) (D-is-Nf x)

swap-ev : ∀{t σ ρ a ρ'} → ⟦ t [ σ ]ₛ ⟧ ρ ↘ a → ⟦ σ ⟧ₛ ρ ↘ ρ' → ⟦ t ⟧ ρ' ↘ a
swap-ev (eSub x e) e' rewrite Evals-fun x e' = e

