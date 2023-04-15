module Semantics.Completeness.Rule where

open import Function
open import Data.Nat
open import Data.Maybe
open import Syntax
open import Semantics.Domain
open import Semantics.Completeness.Type
open import Semantics.Completeness.Lemmata
open import Data.Unit hiding (_≤_ ; _≟_)
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_ ; proj₁ to p1 ; proj₂ to p2)
open import Data.Sum hiding ([_,_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Syntax.Typed

open SemTy
open ⟦_⟧≃⟦_⟧_∈ₜ_
open ⟦_⟧≃⟦_⟧_∈ₛ_
open ⟦_⟧ₜ
open ⟦_⟧_∈ₜ_

private

  mutual

    ⊧_ : Ctxt → Set
    ⊧ ◇ = ⊤
    ⊧ (Γ # A) = ⊧ Γ × (Γ ⊧ A)

    _⊧_ : Ctxt → Term → Set
    Γ ⊧ A = ⊧ Γ × (∀{ρ} → ρ ∈ₛ ⟦ Γ ⟧ₛ → ⟦ A ⟧≃⟦ A ⟧ ρ ∈ₜ 𝒯)

    _⊧_∶_ : Ctxt → Term → Term → Set
    Γ ⊧ t ∶ A = Γ ⊧ A × (∀{ρ} → ρ ∈ₛ ⟦ Γ ⟧ₛ → ⟦ t ⟧≃⟦ t ⟧ ρ ∈tm⟦ A ⟧)

    _⊧_∼_ : Ctxt → Term → Term → Set
    Γ ⊧ A ∼ B = ∀{ρ} → ρ ∈ₛ ⟦ Γ ⟧ₛ → ⟦ A ⟧≃⟦ B ⟧ ρ ∈ₜ 𝒯

    _⊧_∼_∶_ : Ctxt → Term → Term → Term → Set
    Γ ⊧ t ∼ s ∶ A = Γ ⊧ A × (∀{ρ} → ρ ∈ₛ ⟦ Γ ⟧ₛ → ⟦ t ⟧≃⟦ s ⟧ ρ ∈tm⟦ A ⟧)

    _⊧ₛ_∶_ : Ctxt → Subst → Ctxt → Set
    Δ ⊧ₛ σ ∶ Γ = ⊧ Δ × ⊧ Γ × ∀{ρ} → ρ ∈ₛ ⟦ Δ ⟧ₛ → ⟦ σ ⟧≃⟦ σ ⟧ ρ ∈ₛ ⟦ Γ ⟧ₛ

    _⊧ₛ_∼_∶_ : Ctxt → Subst → Subst → Ctxt → Set
    Δ ⊧ₛ σ ∼ τ ∶ Γ = ⊧ Δ × (∀{ρ} → ρ ∈ₛ ⟦ Δ ⟧ₛ → ⟦ σ ⟧≃⟦ τ ⟧ ρ ∈ₛ ⟦ Γ ⟧ₛ)

infix 4 ⊧_
infix 4 _⊧_
infix 4 _⊧_∶_
infix 4 _⊧_∼_
infix 4 _⊧_∼_∶_
infix 4 _⊧ₛ_∼_∶_

piLemma3 : ∀{Γ A B σ s} → Γ ⊧ (Π A B) [ σ ]ₛ → Γ ⊧ s ∶ A [ σ ]ₛ → Γ ⊧ B [ σ , s ]ₛ
piLemma3 p q = (p1 p) ,, goal
  where goal : ∀{ρ} → ρ ∈ₛ ⟦ _ ⟧ₛ → ⟦ _ [ _ , _ ]ₛ ⟧≃⟦ _ [ _ , _ ]ₛ ⟧ ρ ∈ₜ 𝒯
        goal ρ with p2 p ρ
        goal ρ | ⟨ 𝒰⊆𝒯 () ∣ eSub x ePi ∣ ↘t4 ⟩
        goal ρ | ⟨ tPi H1 h2 ∣ eSub x ePi ∣ eSub x₁ ePi ⟩ = 
          ⟨ ∈t (h2 aa) ∣ aux ∣ aux ⟩
          where aa = (sameTerm𝒯≃ (Eval-fun (↘ty (p2 q ρ)) (eSub x (ev H1))) (∈ty' (p2 q ρ)) (∈t H1) (∈tm (p2 q ρ)))
                aux = (eSub (sCons x (↘t1 (p2 q ρ))) (ev (h2 aa)))

piLemma2 : ∀{Γ A B} → Γ ⊧ A → Γ # A ⊧ B → Γ ⊧ Π A B
piLemma2 Ah Bh = (p1 Ah) ,, λ x → piLemma (p2 Ah x) λ x₁ → p2 Bh (cExt x x₁)

subLemma : ∀{Γ Δ A σ} → Δ ⊧ A → Γ ⊧ₛ σ ∶ Δ → Γ ⊧ A [ σ ]ₛ
subLemma Ah sh = (p1 sh) ,, λ x → let h1 = p2 (p2 sh) x ; h2 = p2 Ah (∈s h1) 
         in ⟨ (∈ty h2) ∣ (eSub (↘s1 h1) (↘t1 h2)) ∣ (eSub (↘s2 h1) (↘t2 h2)) ⟩

mutual
  models-ctx : ∀{Γ} → ⊢ Γ → ⊧ Γ
  models-ctx ⊢◇ = tt
  models-ctx (⊢# c x) = models-ctx c ,, models-ty x

  models-ty : ∀{Γ A} → Γ ⊢ A → Γ ⊧ A
  models-ty (U x) = models-ctx x ,, λ x₁ → ⟨ tU ∣ eU ∣ eU ⟩
  models-ty (Π ty) = (p1 (p1 h)) ,, λ x → piLemma (p2 (p2 (p1 h)) x) λ x₁ → p2 h (cExt x x₁)
    where h = models-ty ty
  models-ty (El x) = (p1 (p1 h)) ,, λ x₁ → UtoT (p2 h x₁)
    where h = models-tm x
  models-ty (sub ty x) = p1 hs ,, λ x₁ → 
    let z = p2 (p2 hs) x₁ ; w = p2 h (∈s z) ; y = eSub (↘s1 z) (↘t1 w) 
    in ⟨ ∈ty w ∣ y ∣ y ⟩
    where h = models-ty ty ; hs = models-sub x

  models-ty-eq : ∀{Γ A B} → Γ ⊢ A ∼ B → Γ ⊧ A ∼ B
  models-ty-eq (∼refl x) ρ = let h = models-ty x in p2 h ρ
  models-ty-eq (∼symm eq) ρ = ∈Symm (models-ty-eq eq ρ)
  models-ty-eq (∼trans eq eq₁) ρ = ∈Trans (models-ty-eq eq ρ) (models-ty-eq eq₁ ρ)
  models-ty-eq (∼El x) ρ = UtoT (p2 (models-tm-eq x) ρ)
  models-ty-eq (∼Us s) ρ = ⟨ tU ∣ (eSub (↘s1 h) eU) ∣ eU ⟩
    where h = p2 (p2 (models-sub s)) ρ
  models-ty-eq (∼Sub eq x) ρ = ⟨ ∈ty h2 ∣ (eSub (↘s1 h) (↘t1 h2)) ∣ (eSub (↘s2 h) (↘t2 h2)) ⟩ 
    where h = (p2 $ models-sub-eq x) ρ ; h2 = models-ty-eq eq (∈s h)
  models-ty-eq (∼Id x) ρ = ⟨ ∈ty h ∣ eSub sId (↘t1 h) ∣ ↘t1 h ⟩
    where h = p2 (models-ty x) ρ
  models-ty-eq (∼scomp x x₁ x₂) ρ =
    ⟨ ∈ty h3 ∣ (eSub (↘s1 h) (eSub (↘s1 h2) (↘t1 h3))) ∣ (eSub (sComp (↘s1 h) (↘s1 h2)) (↘t1 h3)) ⟩
    where h = p2 (p2 (models-sub x₂)) ρ ; h2 = p2 (p2 (models-sub x₁)) (∈s h) ; h3 = p2 (models-ty x) (∈s h2)

  models-tm : ∀{Γ t A} → Γ ⊢ t ∶ A → Γ ⊧ t ∶ A
  models-tm (var x) = ((p1 h ,, h) ,, λ { (cExt x₁ x₂) → ⟨ (inT x₂) ∣ (eSub sUp (ev x₂)) ∣ (eSub sUp (ev x₂)) ⟩ }) ,, 
    λ { (cExt x₁ x₂) → ⟨ ⟨ (eSub sUp (ev x₂)) ∣ (inT x₂) ∣ (nn x₂) ⟩ ∣ eVar ∣ eVar ⟩ }
    where h = models-ty x
  models-tm (lam tm) = piLemma2 Ah (p1 h) ,, λ x → lamLemma (p2 Ah x) λ x₁ → p2 h (cExt x x₁)
    where h = models-tm tm ; Ah = p2 (p1 (p1 h))
  models-tm (app sd Bd t s) = piLemma3 (p1 ht) hs ,, λ x → tmAppLemma (p2 ht x) (p2 hs x)
    where h = models-sub sd ; hB = models-ty Bd ; Ah = p2 (p1 hB) ; ht = models-tm t ; hs = models-tm s
  models-tm (coe tm x) = ((p1 (p1 h)) ,, λ y → ⟨ ∈ty (hs y) ∣ ↘t2 (hs y) ∣ ↘t2 (hs y) ⟩) ,, 
            λ y → coerceLemma (p2 h y) (hs y)
    where h = models-tm tm ; hs = models-ty-eq x
  models-tm (sub tm x) = subLemma (p1 h) hs ,, λ x₁ → 
    let y = p2 (p2 hs) x₁ ; w = p2 h (∈s y) 
      in ⟨ ⟨ (eSub (↘s1 y) (↘ty w)) ∣ ∈ty' w ∣ ∈tm w ⟩ ∣ eSub (↘s1 y) (↘t1 w) ∣ eSub (↘s1 y) (↘t1 w) ⟩
    where h = models-tm tm ; hs = models-sub x

  models-tm-eq : ∀{Γ t s A} → Γ ⊢ t ∼ s ∶ A → Γ ⊧ t ∼ s ∶ A
  models-tm-eq (∼refl x) = models-tm x
  models-tm-eq (∼symm eq) = p1 (models-tm-eq eq) ,, λ x → ∈Symm (p2 (models-tm-eq eq) x)
  models-tm-eq (∼trans eq eq₁) = (p1 (models-tm-eq eq)) ,, λ x →
    ∈Trans (p2 (models-tm-eq eq) x) (p2 (models-tm-eq eq₁) x)
  models-tm-eq (∼β {Δ} {Γ} {A} {B} {t} {s} {σ} td sb sd) = (p1 (models-sub sb) ,, goal') ,, goal -- goal' ,, goal
    where
      goal' : ∀{ρ} → ⟦ Δ ⟧ₛ ρ → ⟦ B [ σ , s ]ₛ ⟧≃⟦ B [ σ , s ]ₛ ⟧ ρ ∈ₜ 𝒯
      goal' ρ = ⟨ ∈ty (sem-invert-ty hts) ∣ (eSub (sCons (↘s1 hs) (↘t1 hss)) (↘t1 (sem-invert-ty hts))) 
                     ∣ eSub (sCons (↘s2 hs) (↘t2 hss)) (↘t2 (sem-invert-ty hts)) ⟩
        where
          Ah = p2 (p1 (p1 (models-tm td))) 
          hs = p2 (p2 (models-sub sb)) ρ
          hA = p2 Ah (∈s hs)
          hss = p2 (models-tm sd) ρ
          hts = p2 (models-tm td) (cExt (∈s hs) ⟨ (↘t1 hA) ∣ ∈ty hA 
            ∣ sameTerm𝒯≃ (Eval-fun (↘ty hss) (eSub (↘s1 hs) (↘t1 hA))) (∈ty' hss) (∈ty hA) (∈tm hss) ⟩)
      goal : ∀{ρ} → ρ ∈ₛ ⟦ Δ ⟧ₛ → ⟦ (Lam t [ σ ]ₛ) · s ⟧≃⟦ t [ σ , s ]ₛ ⟧ ρ ∈tm⟦ B [ σ , s ]ₛ ⟧
      goal ρ = ⟨ ⟨ (eSub (sCons (↘s1 hs) (↘t1 hss)) (↘t1 (sem-invert-ty hts))) ∣ ∈ty (sem-invert-ty hts) 
               ∣ ∈tm hts ⟩ ∣ eApp (eSub (↘s1 hs) eLam) (↘t1 hss) (●β (↘t1 hts)) ∣ (eSub (sCons (↘s1 hs) (↘t1 hss)) (↘t1 hts)) ⟩
        where
          Ah = p2 (p1 (p1 (models-tm td))) 
          hs = p2 (p2 (models-sub sb)) ρ
          hA = p2 Ah (∈s hs)
          hss = p2 (models-tm sd) ρ
          hts = p2 (models-tm td) (cExt (∈s hs) ⟨ (↘t1 hA) ∣ ∈ty hA 
            ∣ sameTerm𝒯≃ (Eval-fun (↘ty hss) (eSub (↘s1 hs) (↘t1 hA))) (∈ty' hss) (∈ty hA) (∈tm hss) ⟩)

  models-tm-eq (∼app eq eq₁ sd Bd) = ((p1 $ models-sub sd) ,, tygoal) ,, goal
    where
      tygoal : {ρ : Env} → ρ ∈ₛ ⟦ _ ⟧ₛ → ⟦ _ [ _ , _ ]ₛ ⟧≃⟦ _ [ _ , _ ]ₛ ⟧ ρ ∈ₜ 𝒯
      tygoal ρ = sem-invert-ty (tmAppLemma h h')
        where h = p2 (models-tm-eq eq) ρ ; h' = p2 (models-tm-eq eq₁) ρ
      goal : {ρ : Env} → ρ ∈ₛ ⟦ _ ⟧ₛ → ⟦ _ · _ ⟧≃⟦ _ · _ ⟧ ρ ∈tm⟦ _ [ _ , _ ]ₛ ⟧
      goal ρ = tmAppLemma h h'
        where h = p2 (models-tm-eq eq) ρ ; h' = p2 (models-tm-eq eq₁) ρ

  models-tm-eq (∼sapp x x₁ x₂ x₃ Bd) = ((p1 $ models-sub x₃) ,, goal) ,, goal'
    where goal : ∀{ρ} → ρ ∈ₛ ⟦ _ ⟧ₛ → ⟦ _ [ (_ · _) , (_ [ _ ]ₛ) ]ₛ ⟧≃⟦ _ [ (_ · _) , (_ [ _ ]ₛ) ]ₛ ⟧ ρ ∈ₜ 𝒯
          goal ρp with p2 (p1 (models-tm x)) (∈s ((p2 $ p2 $ models-sub x₃) ρp)) | p2 (models-tm x₁) (∈s ((p2 $ p2 $ models-sub x₃) ρp))
          goal ρp | ⟨ 𝒰⊆𝒯 () ∣ eSub x₄ ePi ∣ ↘t4 ⟩ | ⟨ ∈ty₂ ∣ ↘t5 ∣ ↘t6 ⟩
          goal ρp | ⟨ tPi pA x₅ ∣ eSub x₄ ePi ∣ eSub x₆ ePi ⟩ | ⟨ ∈ty₂ ∣ ↘t5 ∣ ↘t6 ⟩ = 
            ⟨ ∈t (x₅ pp) ∣ (eSub (sCons (sComp (↘s1 h) x₄) (eSub (↘s1 h) ↘t5)) (ev (x₅ pp))) 
                   ∣ eSub (sCons ((sComp (↘s1 h) x₄)) (eSub (↘s1 h) ↘t5)) (ev (x₅ pp)) ⟩
            where h = (p2 $ p2 $ models-sub x₃) ρp
                  pp = (sameTerm𝒯≃ (Eval-fun (ev ∈ty₂) (eSub x₄ (ev pA))) (inT ∈ty₂) (∈t pA) (nn ∈ty₂))
          goal' : {ρ : Env} → ρ ∈ₛ ⟦ _ ⟧ₛ 
                → ⟦ (_ · _) [ _ ]ₛ ⟧≃⟦ (_ [ _ ]ₛ) · (_ [ _ ]ₛ) ⟧ ρ ∈tm⟦ _ [ (_ · _) , (_ [ _ ]ₛ) ]ₛ ⟧
          goal' ρp = goal''
            where h = (p2 $ p2 $ models-sub x₃) ρp ; ht = p2 (models-tm x) (∈s h) ; hs = p2 (models-tm x₁) (∈s h)
                  goal'' : ⟦ (_ · _) [ _ ]ₛ ⟧≃⟦ (_ [ _ ]ₛ) · (_ [ _ ]ₛ) ⟧ _ ∈tm⟦ _ [ (_ · _) , (_ [ _ ]ₛ) ]ₛ ⟧
                  goal'' with tmAppLemma ht hs
                  goal'' | ⟨ ⟨ eSub (sCons x₆ x₇) ev₁ ∣ inT₁ ∣ nn₁ ⟩ ∣ eApp ↘t3 ↘t5 x₄ ∣ eApp ↘t4 ↘t6 x₅ ⟩ = 
                    ⟨ ⟨ (eSub (sCons (sComp (↘s1 h) x₆) (eSub (↘s1 h) ↘t6)) (≡Eval' ev₁ (cong₂ _,_ refl (Eval-fun x₇ ↘t6)))) 
                    ∣ inT₁ ∣ nn₁ ⟩ ∣ (eSub (↘s1 h) (eApp ↘t3 ↘t5 x₄)) ∣ (eApp (eSub (↘s1 h) ↘t4) (eSub (↘s1 h) ↘t6) x₅) ⟩
  models-tm-eq (∼scomp x x₁ x₂) = (p1 (models-sub x₂) ,, goal) ,, goal'
    where
      goal : {ρ : Env} → ρ ∈ₛ ⟦ _ ⟧ₛ → ⟦ _ [ _ · _ ]ₛ ⟧≃⟦ _ [ _ · _ ]ₛ ⟧ ρ ∈ₜ 𝒯
      goal ρp = ⟨ ∈ty h2 ∣ cmp ∣ cmp ⟩
        where h = (p2 $ p2 $ models-sub x₂) ρp ; h' = (p2 $ p2 $ models-sub x₁) (∈s h) ; h2 = p2 (p1 (models-tm x)) (∈s h')
              cmp = (eSub (sComp (↘s1 h) (↘s1 h')) (↘t1 h2))
      goal' : {ρ : Env} → ρ ∈ₛ ⟦ _ ⟧ₛ → ⟦ (_ [ _ ]ₛ) [ _ ]ₛ ⟧≃⟦ _ [ _ · _ ]ₛ ⟧ ρ ∈tm⟦ _ [ _ · _ ]ₛ ⟧
      goal' ρp = ⟨ ⟨ (eSub (sComp (↘s1 h) (↘s1 h')) (↘ty h2)) ∣ (∈ty' h2) ∣ (∈tm h2) ⟩ 
                 ∣ (eSub (↘s1 h) (eSub (↘s1 h') (↘t1 h2))) ∣ (eSub (sComp (↘s1 h) (↘s1 h')) (↘t2 h2)) ⟩
        where h = (p2 $ p2 $ models-sub x₂) ρp ; h' = (p2 $ p2 $ models-sub x₁) (∈s h) ; h2 = p2 (models-tm x) (∈s h')
  models-tm-eq (∼var x x₁ x₂) = (p1 $ models-tm x₂) ,, goal
    where h = p2 $ models-ty x ; hs = p2 $ p2 $ models-sub x₁ ; hss = p2 $ models-tm x₂
          goal : {ρ : Env} → ρ ∈ₛ ⟦ _ ⟧ₛ → ⟦ Var [ _ , _ ]ₛ ⟧≃⟦ _ ⟧ ρ ∈tm⟦ _ [ _ ]ₛ ⟧
          goal ρ = ⟨ ⟨ (eSub (↘s1 $ hs ρ) (swap-ev (↘ty $ hss ρ) (↘s1 $ hs ρ))) 
                   ∣ ∈ty' $ hss ρ ∣ ∈tm $ hss ρ ⟩ 
                   ∣ (eSub (sCons (↘s1 $ hs ρ) (↘t1 $ hss ρ)) eVar) ∣ ↘t2 $ hss ρ ⟩
  models-tm-eq (∼coe eq x) = ((p1 $ p1 (models-tm-eq eq)) ,, ∈Right ∘ models-ty-eq x) ,, λ x₁ → 
                coerceLemma (p2 (models-tm-eq eq) x₁) (models-ty-eq x x₁)
  models-tm-eq (∼Sub eq x) = ((p1 $ models-sub-eq x) ,, goal) ,, goal'
    where
      goal : ∀{ρ} → ρ ∈ₛ ⟦ _ ⟧ₛ → ⟦ _ [ _ ]ₛ ⟧≃⟦ _ [ _ ]ₛ ⟧ ρ ∈ₜ 𝒯
      goal ρp = ⟨ (∈ty' h') ∣ (eSub (↘s1 h) (ev (∈ty h'))) ∣ (eSub (↘s1 h) (↘ty h')) ⟩
        where h = (p2 $ models-sub-eq x) ρp ; h' = p2 (models-tm-eq eq) (∈s h)
      goal' : ∀{ρ} → ρ ∈ₛ ⟦ _ ⟧ₛ → ⟦ _ [ _ ]ₛ ⟧≃⟦ _ [ _ ]ₛ ⟧ ρ ∈tm⟦ _ [ _ ]ₛ ⟧
      goal' ρp = ⟨ ⟨ (eSub (↘s1 h) (↘ty h')) ∣ ∈ty' h' ∣ ∈tm h' ⟩ 
                 ∣ (eSub (↘s1 h) (↘t1 h')) ∣ (eSub (↘s2 h) (↘t2 h')) ⟩
        where h = (p2 $ models-sub-eq x) ρp ; h' = p2 (models-tm-eq eq) (∈s h)
  models-tm-eq (∼Id x) = (p1 (models-tm x)) ,, λ ρ → 
    let h = p2 (models-tm x) ρ in ⟨ ∈ty h ∣ (eSub sId (↘t1 h)) ∣ ↘t2 h ⟩
  
  models-sub : ∀{Δ Γ σ} → Δ ⊢ₛ σ ∶ Γ → Δ ⊧ₛ σ ∶ Γ
  models-sub (⊢Id c) = models-ctx c ,, models-ctx c ,, λ ρ → ⟨ ρ ∣ sId ∣ sId ⟩
  models-sub (⊢, s Ad x) = (p1 $ p1 $ models-tm x) ,, (((p1 $ models-ty Ad) ,, (models-ty Ad)) ,, goal)
    where goal : ∀{ρ} → ρ ∈ₛ ⟦ _ ⟧ₛ → ⟦ _ , _ ⟧≃⟦ _ , _ ⟧ ρ ∈ₛ ⟦ _ # _ ⟧ₛ
          goal ρ with (p2 $ models-tm x) ρ
          goal ρ | ⟨ ⟨ eSub x₁ ev₁ ∣ inT₁ ∣ nn₁ ⟩ ∣ ↘t3 ∣ ↘t4 ⟩ = 
            ⟨ cExt (subst (_∈ₛ ⟦ _ ⟧ₛ) (Evals-fun (↘s1 h') x₁) (∈s h')) 
              ⟨ ev₁ ∣ inT₁ ∣ nn₁ ⟩ ∣ cc ∣ cc ⟩
            where h = models-sub s ; h' = (p2 $ p2 $ h) ρ
                  cc = sCons x₁ ↘t3
  models-sub (⊢· s s₁) = (p1 $ models-sub s₁) ,, (p1 $ p2 $ models-sub s) ,,
    λ ρ → let h1 = (p2 $ p2 $ models-sub s₁) ρ ; h2 = (p2 $ p2 $ models-sub s) (∈s h1)
          in ⟨ ∈s h2 ∣ sComp (↘s1 h1) (↘s1 h2) ∣ sComp (↘s1 h1) (↘s1 h2) ⟩
  models-sub (⊢↑ a) = ((p1 h) ,, ((p1 h) ,, (p2 h))) ,, p1 h ,, λ { (cExt x x₁) → ⟨ x ∣ sUp ∣ sUp ⟩ }
    where h = models-ty a

  models-sub-eq : ∀{Δ Γ σ τ} → Δ ⊢ₛ σ ∼ τ ∶ Γ → Δ ⊧ₛ σ ∼ τ ∶ Γ
  models-sub-eq (∼refl x) = (p1 $ models-sub x) ,, λ ρ → (p2 $ p2 $ models-sub x) ρ
  models-sub-eq (∼symm eq) = (p1 $ models-sub-eq eq) ,, λ ρ → ∈ₛSymm ((p2 $ models-sub-eq eq) ρ)
  models-sub-eq (∼trans eq eq₁) = (p1 $ models-sub-eq eq) ,, 
    λ ρ → ∈ₛTrans ((p2 $ models-sub-eq eq) ρ) ((p2 $ models-sub-eq eq₁) ρ)
  models-sub-eq (∼Cons eq x Ad) = (p1 $ models-sub-eq eq) ,, goal
    where
      h = p2 $ models-sub-eq eq ; h' = p2 (models-tm-eq x)
      goal : ∀{ρ} → ρ ∈ₛ ⟦ _ ⟧ₛ → ⟦ _ , _ ⟧≃⟦ _ , _ ⟧ _ ∈ₛ ⟦ _ # _ ⟧ₛ
      goal ρ with h' ρ
      goal ρ | ⟨ ⟨ eSub x₁ ev₁ ∣ inT₁ ∣ nn₁ ⟩ ∣ ↘t3 ∣ ↘t4 ⟩ = 
        ⟨ (cExt (∈s $ h ρ) ⟨ (≡Eval' ev₁ (Evals-fun x₁ (↘s1 $ h ρ))) ∣ inT₁ ∣ nn₁ ⟩) 
        ∣ (sCons (↘s1 $ h ρ) ↘t3) ∣ (sCons (↘s2 $ h ρ) ↘t4) ⟩
  models-sub-eq (∼IdL x) = (p1 $ models-sub x) ,, λ ρ → 
    let h = (p2 $ p2 $ models-sub x) ρ in ⟨ (∈s h) ∣ (sComp (↘s1 h) sId) ∣ (↘s2 h) ⟩
  models-sub-eq (∼IdR x) = (p1 $ models-sub x) ,, λ ρ → 
    let h = (p2 $ p2 $ models-sub x) ρ in ⟨ (∈s h) ∣ sComp sId (↘s1 h) ∣ ↘s2 h ⟩
  models-sub-eq (∼Up x _ x₁) = (p1 $ models-sub x) ,, λ ρ → 
    let h = (p2 $ p2 $ models-sub x) ρ ; h' = p2 (models-tm x₁) ρ  in
      ⟨ (∈s h) ∣ (sComp (sCons (↘s1 h) (↘t1 h')) sUp) ∣ (↘s2 h) ⟩
  models-sub-eq (∼Assoc x x₁ x₂) = (p1 $ models-sub x) ,, λ ρ →
      let h = (p2 $ p2 $ models-sub x) ρ ; h' = (p2 $ p2 $ models-sub x₁) (∈s h) ; h'' = (p2 $ p2 $ models-sub x₂) (∈s h')
      in ⟨ ∈s h'' ∣ (sComp (↘s1 h) (sComp (↘s1 h') (↘s1 h''))) ∣ (sComp (sComp (↘s2 h) (↘s2 h')) (↘s2 h'')) ⟩
  models-sub-eq (∼Dist Ad x x₁ x₂) = (p1 $ models-sub x) ,, goal
    where
      h = (p2 $ p2 $ models-sub x) ; h' = (p2 $ p2 $ models-sub x₁)--  (∈s $ h ρ) 
      h'' = p2 (models-tm x₂) -- (∈s $ h ρ)
      goal : ∀{ρ} → ρ ∈ₛ ⟦ _ ⟧ₛ → ⟦ (_ , _) · _ ⟧≃⟦ (_ · _) , (_ [ _ ]ₛ) ⟧ _ ∈ₛ ⟦ _ # _ ⟧ₛ
      goal ρ with h'' (∈s $ h ρ)
      goal ρ | ⟨ ⟨ eSub x₁ ev₁ ∣ inT₁ ∣ nn₁ ⟩ ∣ ↘t3 ∣ ↘t4 ⟩ = 
        ⟨ cExt (subst (_∈ₛ ⟦ _ ⟧ₛ) (Evals-fun (↘s1 $ h' (∈s $ h ρ)) x₁) (∈s $ h' (∈s $ h ρ))) 
          ⟨ ev₁ ∣ inT₁ ∣ nn₁ ⟩ ∣ (sComp (↘s1 $ h ρ) (sCons x₁ ↘t3)) 
        ∣ (sCons (sComp (↘s2 $ h ρ) x₁) (eSub (↘s2 $ h ρ) ↘t4)) ⟩
  models-sub-eq (∼comp1 Ad eq x) = (p1 $ models-sub-eq eq) ,, goal -- goal
    where
      h = p2 $ models-sub-eq eq ; h' = p2 (models-tm-eq x)
      goal : ∀{ρ} → ρ ∈ₛ ⟦ _ ⟧ₛ → ⟦ _ , _ ⟧≃⟦ _ , _ ⟧ _ ∈ₛ ⟦ _ # _ ⟧ₛ
      goal ρ with h' ρ
      goal ρ | ⟨ ⟨ eSub x₁ ev₁ ∣ inT₁ ∣ nn₁ ⟩ ∣ ↘t3 ∣ ↘t4 ⟩ =
        ⟨ (cExt (∈s $ h ρ) ⟨ (≡Eval' ev₁ (Evals-fun x₁ (↘s1 $ h ρ))) ∣ inT₁ 
        ∣ subst (_∈ El𝒯 inT₁) (Eval-fun ↘t3 (↘t1 $ h' ρ)) nn₁ ⟩) 
        ∣ (sCons (↘s1 $ h ρ) (↘t1 $ h' ρ)) ∣ (sCons (↘s2 $ h ρ) (↘t2 $ h' ρ)) ⟩
  models-sub-eq (∼comp2 eq eq₁) = (p1 $ models-sub-eq eq₁) ,, λ ρ →
    let h = (p2 $ models-sub-eq eq₁) ρ ; h' = (p2 $ models-sub-eq eq) (∈s h)
    in ⟨ ∈s h' ∣ (sComp (↘s1 h) (↘s1 h')) ∣ sComp (↘s2 h) (↘s2 h') ⟩
  models-sub-eq (∼ext c) = ((p1 $ models-ty c) ,, (models-ty c)) ,,
    λ { ρ@(cExt x x₁) → ⟨ ρ ∣ sCons (sComp sUp sId) eVar ∣ sId ⟩ }
