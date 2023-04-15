module Semantics.Completeness.Type where

open import Function
open import Syntax hiding (_,_)
open import Semantics.Domain
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Product renaming (_,_ to _,,_)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality hiding ([_])

infix 4 _∈ₜ_
_∈ₜ_ : D → (D → Set) → Set
d ∈ₜ T = T d

record SemTy : Set₁ where
  field
    P : D → Set
    hasNe : (e : Dne) → P (DNe e)
open SemTy

_∈_ : D → SemTy → Set
a ∈ T = a ∈ₜ P T

hasLev : ∀{A x} → DNe (Lev x) ∈ₜ P A
hasLev {A} = hasNe A (Lev _)

record _●_∈ₜ_ (f a : D) (P : D → Set) : Set where
  constructor ⟨_∣_⟩
  field
    {res} : D
    ●∈tm   : res ∈ₜ P
    ↘ap  : f ● a ↘ res
open _●_∈ₜ_

_●_∈_ : (f a : D) (B : SemTy) → Set
f ● a ∈ T = f ● a ∈ₜ P T

infix 4 ⟦_⟧_∈ₜ_
record ⟦_⟧_∈ₜ_ (t : Term) (ρ : Env) (Uv : D → Set) : Set where
  field
    {res} : D
    ev : ⟦ t ⟧ ρ ↘ res
    ∈t : res ∈ₜ Uv
open ⟦_⟧_∈ₜ_

SemPi : (A : SemTy) → (∀{a} → a ∈ A → SemTy) → SemTy
SemPi Ah Bh = 
  record { P = λ f → ∀{a} → (p : a ∈ Ah) → f ● a ∈ Bh p 
         ; hasNe = λ e p → ⟨ hasNe (Bh p) _ ∣ ●Ne ⟩ }

--------------------------------------------------------------------------------
-- Semantic universe of small types

mutual

  data 𝒰 : D → Set where
    uNe  : (e : Dne) → 𝒰 (DNe e)

  El𝒰 : ∀{T} → T ∈ₜ 𝒰 → SemTy
  El𝒰 (uNe x) = record { P = isDne ; hasNe = λ e → tt }

𝒰Ty : SemTy
𝒰Ty = record { P = 𝒰 ; hasNe = uNe }

--------------------------------------------------------------------------------
-- Semantic universe of types

mutual

  data 𝒯 : D → Set where
    𝒰⊆𝒯 : ∀{T} → T ∈ₜ 𝒰 → 𝒯 T
    tU   : 𝒯 DU
    tPi  : {A B : Term} {ρ : Env}
         → (pA : ⟦ A ⟧ ρ ∈ₜ 𝒯)
         → (∀{a} → a ∈ El𝒯 (∈t pA) → ⟦ B ⟧ ρ , a ∈ₜ 𝒯)
         → 𝒯 (DΠ A B ρ)

  El𝒯 : ∀{T} → T ∈ₜ 𝒯 →  SemTy
  El𝒯 (𝒰⊆𝒯 x) = El𝒰 x
  El𝒯 tU = record { P = 𝒰 ; hasNe = uNe }
  El𝒯 (tPi Ah Bh) = SemPi (El𝒯 (∈t Ah)) λ x → El𝒯 (∈t (Bh x))

𝒯Ty : SemTy
𝒯Ty = record { P = 𝒯 ; hasNe = 𝒰⊆𝒯 ∘ uNe }

--------------------------------------------------------------------------------

record ⟦_⟧ₜ (A : Term) (ρ : Env) (d : D) : Set where
  constructor ⟨_∣_∣_⟩
  field
    {T} : D
    ev : ⟦ A ⟧ ρ ↘ T
    inT : T ∈ₜ 𝒯
    nn : d ∈ₜ P (El𝒯 inT)
open ⟦_⟧ₜ

infix 4 ⟦_⟧≃⟦_⟧_∈ₜ_
record ⟦_⟧≃⟦_⟧_∈ₜ_ (A B : Term) (ρ : Env) (T : D → Set) : Set where
  constructor ⟨_∣_∣_⟩
  field
    {res} : D
    ∈ty : res ∈ₜ T
    ↘t1 : ⟦ A ⟧ ρ ↘ res
    ↘t2 : ⟦ B ⟧ ρ ↘ res
open ⟦_⟧≃⟦_⟧_∈ₜ_

onlyOne : ∀{t T ρ} → ⟦ t ⟧≃⟦ t ⟧ ρ ∈ₜ T → ⟦_⟧_∈ₜ_ t ρ T
onlyOne ⟨ ∈ty₁ ∣ ↘t3 ∣ ↘t4 ⟩ = record { ev = ↘t4 ; ∈t = ∈ty₁ }

_∈ₛ_ : Env → (Env → Set) → Set
ρ ∈ₛ S = S ρ

data ⟦_⟧ₛ : Ctxt → Env → Set where
  cEmpty : ⟦ ◇ ⟧ₛ ε
  cExt   : ∀{Γ A ρ a} → ρ ∈ₛ ⟦ Γ ⟧ₛ → a ∈ₜ ⟦ A ⟧ₜ ρ → ⟦ Γ # A ⟧ₛ (ρ , a)

idenv : Ctxt → Env
idenv ◇ = ε
idenv (Γ # A) = idenv Γ , DNe (Lev (clen Γ))

infix 4 ⟦_⟧≃⟦_⟧_∈ₛ_
record ⟦_⟧≃⟦_⟧_∈ₛ_ (σ τ : Subst) (ρ : Env) (T : Env → Set) : Set where
  constructor ⟨_∣_∣_⟩
  field
    {res} : Env
    ∈s : res ∈ₛ T
    ↘s1 : ⟦ σ ⟧ₛ ρ ↘ res
    ↘s2 : ⟦ τ ⟧ₛ ρ ↘ res
open ⟦_⟧≃⟦_⟧_∈ₜ_

infix 4 ⟦_⟧≃⟦_⟧_∈tm⟦_⟧
⟦_⟧≃⟦_⟧_∈tm⟦_⟧ : Term → Term → Env → Term → Set
⟦ t ⟧≃⟦ t' ⟧ ρ ∈tm⟦ A ⟧ = ⟦ t ⟧≃⟦ t' ⟧ ρ ∈ₜ ⟦ A ⟧ₜ ρ

⟦_⟧≃⟦_⟧_∈_ : Term → Term → Env → SemTy → Set
⟦ t ⟧≃⟦ t' ⟧ ρ ∈ T = ⟦ t ⟧≃⟦ t' ⟧ ρ ∈ₜ P T

∈ty' : ∀{t t' A ρ} → (p : ⟦ t ⟧≃⟦ t' ⟧ ρ ∈tm⟦ A ⟧) → T (∈ty p) ∈ₜ 𝒯
∈ty' p = inT (∈ty p)

∈tm : ∀{t t' A ρ} → (p : ⟦ t ⟧≃⟦ t' ⟧ ρ ∈tm⟦ A ⟧) → res p ∈ₜ P (El𝒯 (∈ty' p))
∈tm p = nn (∈ty p)

resT : ∀{t t' A ρ} → ⟦ t ⟧≃⟦ t' ⟧ ρ ∈tm⟦ A ⟧ → D
resT p = T (∈ty p)

↘ty : ∀{t t' ρ A} → (p : ⟦ t ⟧≃⟦ t' ⟧ ρ ∈tm⟦ A ⟧) → ⟦ A ⟧ ρ ↘ T (∈ty p)
↘ty ⟨ ⟨ ev ∣ inT ∣ nn ⟩ ∣ ↘t1 ∣ ↘t2 ⟩ = ev

↘tm1 : ∀{t t' ρ A} → (p : ⟦ t ⟧≃⟦ t' ⟧ ρ ∈tm⟦ A ⟧) → ⟦ t ⟧ ρ ↘ res p
↘tm1 ⟨ _ ∣ e ∣ _ ⟩ = e

↘tm2 : ∀{t t' ρ A} → (p : ⟦ t ⟧≃⟦ t' ⟧ ρ ∈tm⟦ A ⟧) → ⟦ t' ⟧ ρ ↘ res p
↘tm2 ⟨ _ ∣ _ ∣ e ⟩ = e
