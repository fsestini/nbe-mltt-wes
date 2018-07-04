module Semantics.Completeness.Lemmata where

open import Function
open import Syntax
open import Semantics.Domain
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Product renaming (_,_ to _,,_)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Semantics.Completeness.Type
open import Data.Sum
open import Function

open SemTy
open _●_∈ₜ_
open ⟦_⟧ₜ
open ⟦_⟧≃⟦_⟧_∈ₜ_
open ⟦_⟧_∈ₜ_
open ⟦_⟧≃⟦_⟧_∈ₛ_

sameTerm𝒯≃ : ∀{A B a} → A ≡ B → (p : A ∈ₜ 𝒯) (q : B ∈ₜ 𝒯) → P (El𝒯 p) a → P (El𝒯 q) a
sameTerm𝒯≃ refl (𝒰⊆𝒯 (uNe e)) (𝒰⊆𝒯 (uNe .e)) z = z
sameTerm𝒯≃ refl tU (𝒰⊆𝒯 ())
sameTerm𝒯≃ refl tU tU z = z
sameTerm𝒯≃ refl (tPi pA x) (𝒰⊆𝒯 ()) pa
sameTerm𝒯≃ refl (tPi h1 h2) (tPi h1' h2') pa aa = 
  ⟨ sameTerm𝒯≃ (Eval-fun (ev (h2 aa')) (ev (h2' aa))) (∈t (h2 aa')) (∈t (h2' aa)) (●∈tm h) ∣ ↘ap h ⟩
  where aa' = sameTerm𝒯≃ (Eval-fun (ev h1') (ev h1)) (∈t h1') (∈t h1) aa ; h = pa aa'

coerceLemma : ∀{ρ t s A B} → ⟦ t ⟧≃⟦ s ⟧ ρ ∈tm⟦ A ⟧ → ⟦ A ⟧≃⟦ B ⟧ ρ ∈ₜ 𝒯 → ⟦ t ⟧≃⟦ s ⟧ ρ ∈tm⟦ B ⟧
coerceLemma ⟨ ⟨ ev₁ ∣ inT₁ ∣ nn₁ ⟩ ∣ ↘t3 ∣ ↘t4 ⟩ ⟨ ∈ty₂ ∣ ↘t5 ∣ ↘t6 ⟩ =
  ⟨ ⟨ ↘t6 ∣ ∈ty₂ ∣ sameTerm𝒯≃ (Eval-fun ev₁ ↘t5) inT₁ ∈ty₂ nn₁ ⟩ ∣ ↘t3 ∣ ↘t4 ⟩            

∈Symm : ∀{A B T ρ} → ⟦ A ⟧≃⟦ B ⟧ ρ ∈ₜ T → ⟦ B ⟧≃⟦ A ⟧ ρ ∈ₜ T
∈Symm ⟨ ty ∣ t1 ∣ t2 ⟩ = ⟨ ty ∣ t2 ∣ t1 ⟩

∈Trans : ∀{A B C T ρ} → ⟦ A ⟧≃⟦ B ⟧ ρ ∈ₜ T → ⟦ B ⟧≃⟦ C ⟧ ρ ∈ₜ T → ⟦ A ⟧≃⟦ C ⟧ ρ ∈ₜ T
∈Trans ⟨ ty ∣ t1 ∣ t2 ⟩ ⟨ ty' ∣ t1' ∣ t2' ⟩ = ⟨ ty ∣ t1 ∣ ≡Eval t2' (Eval-fun t2 t1') ⟩

∈Right : ∀{A B T ρ} → ⟦ A ⟧≃⟦ B ⟧ ρ ∈ₜ T → ⟦ B ⟧≃⟦ B ⟧ ρ ∈ₜ T
∈Right h = ∈Trans (∈Symm h) h

∈Left : ∀{A B T ρ} → ⟦ A ⟧≃⟦ B ⟧ ρ ∈ₜ T → ⟦ A ⟧≃⟦ A ⟧ ρ ∈ₜ T
∈Left h = ∈Trans h (∈Symm h)

∈ₛSymm : ∀{A B T ρ} → ⟦ A ⟧≃⟦ B ⟧ ρ ∈ₛ T → ⟦ B ⟧≃⟦ A ⟧ ρ ∈ₛ T
∈ₛSymm ⟨ ty ∣ t1 ∣ t2 ⟩ = ⟨ ty ∣ t2 ∣ t1 ⟩

∈ₛTrans : ∀{A B C T ρ} → ⟦ A ⟧≃⟦ B ⟧ ρ ∈ₛ T → ⟦ B ⟧≃⟦ C ⟧ ρ ∈ₛ T → ⟦ A ⟧≃⟦ C ⟧ ρ ∈ₛ T
∈ₛTrans ⟨ ty ∣ t1 ∣ t2 ⟩ ⟨ ty' ∣ t1' ∣ t2' ⟩ = ⟨ ty ∣ t1 ∣ ≡Evals t2' (Evals-fun t2 t1') ⟩

∈ₛRight : ∀{A B T ρ} → ⟦ A ⟧≃⟦ B ⟧ ρ ∈ₜ T → ⟦ B ⟧≃⟦ B ⟧ ρ ∈ₜ T
∈ₛRight h = ∈Trans (∈Symm h) h

∈ₛLeft : ∀{A B T ρ} → ⟦ A ⟧≃⟦ B ⟧ ρ ∈ₛ T → ⟦ A ⟧≃⟦ A ⟧ ρ ∈ₛ T
∈ₛLeft h = ∈ₛTrans h (∈ₛSymm h)

sem-invert-ty : ∀{t s A ρ} → ⟦ t ⟧≃⟦ s ⟧ ρ ∈tm⟦ A ⟧ → ⟦ A ⟧≃⟦ A ⟧ ρ ∈ₜ 𝒯
sem-invert-ty ⟨ ⟨ ev ∣ inT ∣ _ ⟩ ∣ _ ∣ _ ⟩ = ⟨ inT ∣ ev ∣ ev ⟩

tmAppLemma : ∀{t t' s s' A B σ ρ} 
           → ⟦ t ⟧≃⟦ t' ⟧ ρ ∈tm⟦ (Π A B) [ σ ]ₛ ⟧ → ⟦ s ⟧≃⟦ s' ⟧ ρ ∈tm⟦ A [ σ ]ₛ ⟧
           → ⟦ t · s ⟧≃⟦ t' · s' ⟧ ρ ∈tm⟦ B [ σ , s ]ₛ ⟧
tmAppLemma ⟨ ⟨ eSub x ePi ∣ 𝒰⊆𝒯 () ∣ _ ⟩ ∣ _ ∣ _ ⟩ _
tmAppLemma ⟨ ⟨ eSub x ePi ∣ tPi pA x₁ ∣ nn₁ ⟩ ∣ ↘t3 ∣ ↘t4 ⟩ hs = 
  ⟨ ⟨ eSub (sCons x (↘t1 hs)) (ev (x₁ pp)) ∣ ∈t (x₁ pp) ∣ ●∈tm (nn₁ pp) ⟩ 
  ∣ eApp ↘t3 (↘t1 hs) (↘ap (nn₁ pp)) ∣ eApp ↘t4 (↘t2 hs) (↘ap (nn₁ pp)) ⟩
  where pp = sameTerm𝒯≃ (Eval-fun (↘ty hs) (eSub x (ev pA))) (∈ty' hs) (∈t pA) (∈tm hs)

piLemma : ∀{A B ρ} → ⟦ A ⟧≃⟦ A ⟧ ρ ∈ₜ 𝒯
        → (∀{a} → a ∈ₜ ⟦ A ⟧ₜ ρ → ⟦ B ⟧≃⟦ B ⟧ (ρ , a) ∈ₜ 𝒯)
        → ⟦ Π A B ⟧≃⟦ Π A B ⟧ ρ ∈ₜ 𝒯
piLemma hA hB = ⟨ tPi (record { ev = ↘t1 hA ; ∈t = ∈ty hA })
  (λ x → let aux = ⟨ ↘t1 hA ∣ ∈ty hA ∣ x ⟩ in record { ev = ↘t1 (hB aux) ; ∈t = ∈ty (hB aux) })
  ∣ ePi ∣ ePi ⟩

lamLemma : ∀{A B t ρ} → ⟦ A ⟧≃⟦ A ⟧ ρ ∈ₜ 𝒯
         → (∀{a} → a ∈ₜ ⟦ A ⟧ₜ ρ → ⟦ t ⟧≃⟦ t ⟧ (ρ , a) ∈tm⟦ B ⟧)
         → ⟦ Lam t ⟧≃⟦ Lam t ⟧ ρ ∈tm⟦ Π A B ⟧
lamLemma hA ht = 
  ⟨ ⟨ ePi ∣ tPi (onlyOne hA) 
  (λ a → let aux = (ht ⟨ ↘t1 hA ∣ ∈ty hA ∣ a ⟩) in onlyOne (sem-invert-ty aux)) 
  ∣ (λ p → let aux = (ht ⟨ ↘t1 hA ∣ ∈ty hA ∣ p ⟩) in ⟨ ∈tm aux ∣ (●β (↘t1 aux)) ⟩) ⟩ 
  ∣ eLam ∣ eLam ⟩

UtoT : ∀{A B ρ} → ⟦ A ⟧≃⟦ B ⟧ ρ ∈ₜ ⟦ U ⟧ₜ ρ → ⟦ A ⟧≃⟦ B ⟧ ρ ∈ₜ 𝒯
UtoT ⟨ ⟨ eU ∣ 𝒰⊆𝒯 () ∣ nn₁ ⟩ ∣ ↘t3 ∣ ↘t4 ⟩
UtoT ⟨ ⟨ eU ∣ tU ∣ nn₁ ⟩ ∣ ↘t3 ∣ ↘t4 ⟩ = ⟨ (𝒰⊆𝒯 nn₁) ∣ ↘t3 ∣ ↘t4 ⟩
