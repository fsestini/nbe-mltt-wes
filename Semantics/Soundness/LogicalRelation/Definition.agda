module Semantics.Soundness.LogicalRelation.Definition where

open import Semantics.Completeness.Lemmata

open import Syntax
open import Semantics.Domain
open import Semantics.Completeness
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality

open ⟦_⟧_∈ₜ_
open _●_∈ₜ_
open SemTy
open ⟦_⟧ₜ
open ⟦_⟧≃⟦_⟧_∈ₜ_
open ⟦_⟧≃⟦_⟧_∈ₛ_


data SemFun (ρ : Env) : D → Set where
  semLam : (t : Term) → SemFun ρ (Dλ t ρ)
  semNe  : (e : Dne) → SemFun ρ (DNe e)

theDne : ∀{a} → isDne a → D
theDne {a} _ = a

mutual

  _⊢_®𝒰_ : ∀{A} → Ctxt → Term → A ∈ₜ 𝒰 → Set
  Γ ⊢ T ®𝒰 uNe e = ⊢ Γ × ∀{Δ w} → Δ ⊢ᵣ w ∶ Γ → Δ ⊢ T [ w ]ₛ ∼ reifyNe (clen Δ) e

  _⊢_®_ : ∀{A} → Ctxt → Term → A ∈ₜ 𝒯 → Set
  Γ ⊢ T ® 𝒰⊆𝒯 x = Γ ⊢ T ®𝒰 x
  Γ ⊢ T ® tU = Γ ⊢ T ∼ U
  Γ ⊢ R ® (tPi {A} {B} {ρ} h1 h2) =
    Σ (Ctxt × Subst) λ { (Δ ,, σ)
    → Δ # A ⊢ B × (Γ ⊢ R ∼ (Π A B) [ σ ]ₛ)
    × (∀{∇ w} → ∇ ⊢ᵣ w ∶ Γ → ∇ ⊢ₛ σ · w ∼ reifyEnv (clen ∇) ρ ∶ Δ)
    × (∀{w ∇ s a} → ∇ ⊢ᵣ w ∶ Γ → (p : a ∈ El𝒯 (∈t h1)) 
              → ∇ ⊢ s ∶ A [ σ · w ]ₛ ® ∈t h1 ∋ p 
              → ∇ ⊢ B [ (σ · w) , s ]ₛ ® ∈t (h2 p) ) }

  _⊢_∶_®𝒰_∋_ : ∀{A a} → Ctxt → Term → Term
               → (ty : A ∈ₜ 𝒰) → a ∈ El𝒰 ty → Set
  _⊢_∶_®𝒰_∋_ {_} {a} Γ t T (uNe e) p = ⊢ Γ
     × (∀{Δ w} → Δ ⊢ᵣ w ∶ Γ → Δ ⊢ T [ w ]ₛ ∼ reifyNe (clen Δ) e) 
     × (∀{Δ w} → Δ ⊢ᵣ w ∶ Γ → Δ ⊢ t [ w ]ₛ ∼ reify (clen Δ) a ∶ T [ w ]ₛ)

  _⊢_∶_®_∋_ : ∀{a A} → Ctxt → Term → Term → (ty : A ∈ₜ 𝒯) → a ∈ El𝒯 ty → Set
  Γ ⊢ t ∶ T ® 𝒰⊆𝒯 x ∋ p = Γ ⊢ t ∶ T ®𝒰 x ∋ p
  _⊢_∶_®_∋_ {a} {A} Γ t T tU p = Γ ⊢ T ∼ U × (Γ ⊢ t ®𝒰 p) × (∀{Δ w} → Δ ⊢ᵣ w ∶ Γ → Δ ⊢ t [ w ]ₛ ∼ reify (clen Δ) a ∶ U)
  _⊢_∶_®_∋_ {a} Γ r R (tPi {A} {B} {ρ} h1 h2) p = Σ (SemFun ρ a) aux
    where
      aux : SemFun ρ a → Set
      aux (semLam t) = Σ (Ctxt × Subst) λ { (Δ ,, σ) → 
          Γ ⊢ R ∼ (Π A B) [ σ ]ₛ
        × (Δ # A ⊢ t ∶ B)
        × (Γ ⊢ r ∼ (Lam t) [ σ ]ₛ ∶ R)
        × (∀{∇ w} → ∇ ⊢ᵣ w ∶ Γ → ∇ ⊢ₛ σ · w ∼ reifyEnv (clen ∇) ρ ∶ Δ)
        × ((∀{s a ∇ w} → ∇ ⊢ᵣ w ∶ Γ → (q : a ∈ El𝒯 (∈t h1)) 
              → ∇ ⊢ s ∶ A [ σ · w ]ₛ ® ∈t h1 ∋ q
              → ∇ ⊢ t [ (σ · w) , s ]ₛ ∶ B [ (σ · w) , s ]ₛ ® ∈t (h2 q) ∋ ●∈tm (p q) )) }
      aux (semNe e) = (∀{Δ w} → Δ ⊢ᵣ w ∶ Γ → Δ ⊢ r [ w ]ₛ ∼ reifyNe (clen Δ) e ∶ R [ w ]ₛ) × ⊢ Γ

infix 4 _⊢ₛ_∶_®_
data _⊢ₛ_∶_®_ : Ctxt → ∀{ρ} → Subst → (Δ : Ctxt) → ρ ∈ₛ ⟦ Δ ⟧ₛ → Set where
  ◇® : ◇ ⊢ₛ Id ∶ ◇ ® cEmpty
  #® : ∀{Γ Δ t T σ ρ a} {ρp : ρ ∈ₛ ⟦ Δ ⟧ₛ} {p : a ∈ₜ ⟦ T ⟧ₜ ρ}
     → Δ ⊢ T
     → Γ ⊢ₛ σ ∶ Δ ® ρp → Γ ⊢ t ∶ T [ σ ]ₛ ® inT p ∋ nn p
     → Γ ⊢ₛ (σ , t) ∶ Δ # T ® cExt ρp p
  ↑® : ∀{Γ Δ ∇ w σ ρ} {p : ρ ∈ₛ ⟦ Δ ⟧ₛ} → Γ ⊢ₛ σ ∶ Δ ® p → ∇ ⊢ᵣ w ∶ Γ → ∇ ⊢ₛ σ · w ∶ Δ ® p
  ∼® : ∀{Γ σ τ Δ ρ} {ρp : ρ ∈ₛ ⟦ Δ ⟧ₛ}
     → Γ ⊢ₛ τ ∶ Δ
     → Γ ⊢ₛ σ ∶ Δ ® ρp → Γ ⊢ₛ τ ∼ σ ∶ Δ → Γ ⊢ₛ τ ∶ Δ ® ρp

allNe𝒰 : ∀{Γ t T e X} (ty : X ∈ₜ 𝒰) → ⊢ Γ
       → (∀{Δ w} → Δ ⊢ᵣ w ∶ Γ → Δ ⊢ T [ w ]ₛ ∼ reify (clen Δ) X)
       → (∀{Δ w} → Δ ⊢ᵣ w ∶ Γ → Δ ⊢ t [ w ]ₛ ∼ reifyNe (clen Δ) e ∶ T [ w ]ₛ)
       → Γ ⊢ t ∶ T ®𝒰 ty ∋ hasNe (El𝒰 ty) e
allNe𝒰 (uNe e) c eq eq' = c ,, eq ,, eq'

id-left-ty : ∀{Γ T A} → Γ ⊢ T [ Id ]ₛ ∼ A → Γ ⊢ T
id-left-ty eq = invert-idsub-ty (proj₁ (eq-lemma-ty eq))

id-left-tm : ∀{Γ t T s} → Γ ⊢ t [ Id ]ₛ ∼ s ∶ T [ Id ]ₛ → Γ ⊢ t ∶ T
id-left-tm eq = invert-idsub-tm (proj₁ (eq-lemma-tm (∼coe eq 
           (∼Id (invert-idsub-ty (invert-ty (proj₁ (eq-lemma-tm eq))))))))

allNe : ∀{Γ t T e X} (ty : X ∈ₜ 𝒯) → ⊢ Γ
      → (∀{Δ w} → Δ ⊢ᵣ w ∶ Γ → Δ ⊢ T [ w ]ₛ ∼ reify (clen Δ) X)
      → (∀{Δ w} → Δ ⊢ᵣ w ∶ Γ → Δ ⊢ t [ w ]ₛ ∼ reifyNe (clen Δ) e ∶ T [ w ]ₛ)
      → Γ ⊢ t ∶ T ® ty ∋ hasNe (El𝒯 ty) e
allNe (𝒰⊆𝒯 x) c eq eq' = allNe𝒰 x c eq eq'
allNe tU c eq eq' = ∼trans (∼symm (∼Id tee)) h ,, 
      (c ,, λ z → ∼El (∼coe (eq' z) (eq z))) ,, (λ z → ∼coe (eq' z) (eq z))
  where h = eq (rId c) ; tee = id-left-ty h
allNe (tPi pA x) c eq eq' = (semNe _) ,, (λ x₁ → eq' x₁) ,, c --  ,, id-left-tm (eq' (rId c))

derₜ𝒰 : ∀{Γ t T A a} (p : A ∈ₜ 𝒰) (q : a ∈ El𝒰 p) 
      → Γ ⊢ t ∶ T ®𝒰 p ∋ q → Γ ⊢ t ∶ T
derₜ𝒰 (uNe e) q rel = id-left-tm (proj₂ (proj₂ rel) (rId c))
  where c = proj₁ rel

derty𝒰 : ∀{Γ T A} (p : A ∈ₜ 𝒰) → Γ ⊢ T ®𝒰 p → Γ ⊢ T
derty𝒰 (uNe e) rel = id-left-ty (proj₂ rel (rId c))
  where c = proj₁ rel

dertyₜ : ∀{Γ T A} (p : A ∈ₜ 𝒯) → Γ ⊢ T ® p → Γ ⊢ T
dertyₜ (𝒰⊆𝒯 x) rel = derty𝒰 x rel
dertyₜ tU rel = proj₁ (eq-lemma-ty rel)
dertyₜ (tPi pA x) (_ ,, _ ,, k ,, _ ,, _) = proj₁ (eq-lemma-ty k)

derₜ : ∀{Γ t T A a} (p : A ∈ₜ 𝒯) (q : a ∈ El𝒯 p) 
     → Γ ⊢ t ∶ T ® p ∋ q → Γ ⊢ t ∶ T
derₜ (𝒰⊆𝒯 x) q rel = derₜ𝒰 x q rel
derₜ tU q (h ,, _ ,, h') = coe (invert-idsub-tm (proj₁ (eq-lemma-tm (h' (rId c))))) (∼symm h)
  where c = invert-ctx-ty (proj₁ (eq-lemma-ty h))
derₜ (tPi pA x) q (semLam t ,, (_ ,, _) ,, _ ,, _ ,, k ,, _ ,, _) = proj₁ (eq-lemma-tm k)
derₜ (tPi pA x) q (semNe e ,, eq' ,, c) = id-left-tm (eq' (rId c)) --  ,, id-left-tm (eq' (rId c))

derₛ : ∀{Γ Δ σ ρ} {p : ρ ∈ₛ ⟦ Γ ⟧ₛ} → Δ ⊢ₛ σ ∶ Γ ® p → Δ ⊢ₛ σ ∶ Γ
derₛ ◇® = (⊢Id ⊢◇)
derₛ (#® {p = p} Td rel x) = ⊢, (derₛ rel) Td (derₜ (inT p) (nn p) x)
derₛ (∼® sd rel x) = sd
derₛ (↑® rel w) = ⊢· (derₛ rel) (renIsSub w)

_⊧_[_] : (Γ : Ctxt) → (T : Term) → Γ ⊢ T → Set
Γ ⊧ A [ d ] = ∀{Δ σ ρ} {ρp : ρ ∈ₛ ⟦ Γ ⟧ₛ}→ Δ ⊢ₛ σ ∶ Γ ® ρp
     → let h = proj₂ (models-ty d) ρp in Δ ⊢ A [ σ ]ₛ ® ∈ty h

_⊧_∶_[_] : (Γ : Ctxt) → (t : Term) → (T : Term) → Γ ⊢ t ∶ T → Set
Γ ⊧ t ∶ T [ d ] = ∀{Δ σ ρ} {ρp : ρ ∈ₛ ⟦ Γ ⟧ₛ}→ Δ ⊢ₛ σ ∶ Γ ® ρp
     → let h = proj₂ (models-tm d) ρp
       in Δ ⊢ t [ σ ]ₛ ∶ T [ σ ]ₛ ® ∈ty' h ∋ ∈tm h

_⊧ₛ_∶_[_] : (Γ : Ctxt) → (σ : Subst) → (Δ : Ctxt) → Γ ⊢ₛ σ ∶ Δ → Set
Γ ⊧ₛ τ ∶ Γ' [ d ] = ∀{Δ σ ρ} {ρp : ρ ∈ₛ ⟦ Γ ⟧ₛ} 
     → Δ ⊢ₛ σ ∶ Γ ® ρp → Δ ⊢ₛ τ · σ ∶ Γ' ® ∈s (proj₂ (proj₂ (models-sub d)) ρp)
