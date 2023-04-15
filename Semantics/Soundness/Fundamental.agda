module Semantics.Soundness.Fundamental where

open import Utils
open import Function
open import Semantics.Soundness.LogicalRelation
open import Semantics.Soundness.LogicalRelation.Conversion
open import Semantics.Soundness.LogicalRelation.Kripke
open import Syntax
open import Semantics.Domain
open import Semantics.Completeness
open import Semantics.Completeness.Lemmata

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

var-aux : ∀{Γ Δ A a σ ρ} → Γ ⊢ A → (p : ρ ∈ₛ ⟦ Γ ⟧ₛ) → (q : ⟦ A ⟧ₜ ρ a)
    → Δ ⊢ₛ σ ∶ Γ # A ® cExt p q
    → Δ ⊢ₛ ↑ · σ ∶ Γ ® p
var-aux _ p q (#® x rel x₁) = ∼® (⊢· (⊢↑ x) (⊢, sd x td)) rel (∼Up sd x td)
  where sd = derₛ rel ; td = derₜ (inT q) (nn q) x₁
var-aux {A = A} Ad p q (↑® rel x) = ∼® (⊢· (⊢↑ Ad) (⊢· sd rr)) (↑® h x) (∼symm (∼Assoc rr sd (⊢↑ Ad)))
  where h = var-aux Ad p q rel ; sd = derₛ rel ; rr = renIsSub x
var-aux Ad p q (∼® gu rel x) = ∼® (⊢· (⊢↑ Ad) gu) h (∼comp2 (∼refl (⊢↑ Ad)) x)
  where h = var-aux Ad p q rel

varFundamental : ∀{∇ Δ Γ σ ρ A w} → (Ad : Γ ⊢ A) → (ρp : ρ ∈ₛ ⟦ Γ # A ⟧ₛ) → Δ ⊢ₛ σ ∶ Γ # A ® ρp
               → ∇ ⊢ᵣ w ∶ Δ
               → let aux = proj₂ (models-tm (var Ad)) ρp
                 in ∇ ⊢ Var [ σ · w ]ₛ ∶ A [ ↑ ]ₛ [ σ · w ]ₛ ® ∈ty' aux ∋ ∈tm aux
varFundamental Ad (cExt x x₁) (#® x₂ rel x₃) wp = 
  ∼preservation-tm (inT x₁) (nn x₁) (∼trans (∼scomp Ad sd rr) 
    (∼symm (∼trans (∼scomp Ad (⊢↑ Ad) (⊢· cns rr)) (∼Sub' Ad (∼trans (∼symm 
    (∼Assoc rr ((⊢, sd Ad td)) (⊢↑ x₂))) (∼comp2 (∼Up sd Ad td) (∼refl rr))))))) 
    (∼symm (∼coe (∼trans (∼Sub (∼refl (var Ad)) (∼Dist Ad rr sd td)) (∼coe (∼var Ad (⊢· sd rr) 
      tmw) (∼symm (∼trans (∼Sub' (sub Ad (⊢↑ x₂)) (∼Dist Ad rr sd td)) 
      (∼trans (∼scomp Ad (⊢↑ Ad) (⊢, cmp Ad tmw)) (∼Sub' Ad (∼Up cmp Ad tmw))))))) 
      (∼trans (∼scomp Ad (⊢↑ Ad) (⊢· cns rr)) (∼symm (∼trans (∼scomp Ad sd rr) 
      (∼symm (∼Sub' Ad (∼trans (∼symm (∼Assoc rr cns (⊢↑ x₂))) (∼comp2 (∼Up sd Ad td) (∼refl rr)))))))))) kkk
  where sd = derₛ rel ; td = (derₜ (inT x₁) (nn x₁) x₃)
        kkk = (kripke-tm wp (inT x₁) (nn x₁) x₃)
        rr = renIsSub wp  ; cmp = ⊢· sd rr ; cns = (⊢, sd Ad td)
        tmw = (coe (sub td rr) (∼scomp Ad sd rr))
varFundamental Ad ρp@(cExt x x₁) (↑® rel x₂) wp = 
  ∼preservation-tm (inT x₁) (nn x₁) (∼symm (∼Sub' (sub Ad (⊢↑ Ad)) (∼trans (∼Assoc rr2 rr sd) 
    (∼comp2 (∼refl sd) (∼symm (proj₂ (proj₂ cmp))))))) (∼Sub (∼refl (var Ad)) 
    (∼trans (∼comp2 (∼refl sd) (proj₂ $ proj₂ $ cmp)) (∼symm (∼Assoc rr2 rr sd)))) h
  where cmp = (renComp wp x₂)
        h = varFundamental Ad ρp rel (proj₁ (proj₂ cmp))
        rr  = renIsSub x₂ ; rr2 = renIsSub wp ; sd = derₛ rel
varFundamental Ad ρp@(cExt x x₁) (∼® x₂ rel x₃) wp =
  ∼preservation-tm (inT x₁) (nn x₁) (∼Sub' (sub Ad (⊢↑ Ad)) eq) 
    (∼Sub (∼refl (var Ad)) eq) h
  where h = varFundamental Ad ρp rel wp
        ww = renIsSub wp ; eq = (∼comp2 (∼symm x₃) (∼refl ww))

mutual

  fundamental-ty : ∀{Γ T} → (p : Γ ⊢ T) → Γ ⊧ T [ p ]
  fundamental-ty (U x) rels = ∼Us (derₛ rels)
  fundamental-ty (Π t) {ρp = ρp} rels = 
    _ ,, t ,, ∼Sub' pi (∼refl sd) ,,
      (λ x → convert-®-sub x ρp rels) ,, (λ x p x₁ → h (#® Ad (↑® rels x) x₁))
    where pi = Π t ; sd = derₛ rels ; h = fundamental-ty t
          Ad = proj₂ (split-ctx (invert-ctx-ty t))
  fundamental-ty {Γ} {T} (El x) {Δ} {σ} {ρ} {ρp = ρp} rels =
    ty-irrel𝒯 refl refl (𝒰⊆𝒯 (proj₁ pp)) (∈ty mm') (
      ty-irrel𝒰 refl (Eval-fun (↘t1 mm) (↘t1 mm')) (proj₂ pp) (proj₁ pp) (proj₁ (proj₂ hh)))
    where h = fundamental-tm x rels ; mm' = proj₂ (models-ty (El x)) ρp 
          mm = proj₂ (models-tm x) ρp ; pp : res mm' ∈ₜ 𝒰 × res mm ∈ₜ 𝒰
          pp with mm
          pp | ⟨ ⟨ eU ∣ 𝒰⊆𝒯 () ∣ _ ⟩ ∣ _ ∣ _ ⟩
          pp | ⟨ ⟨ eU ∣ tU ∣ nn₁ ⟩ ∣ _ ∣ _ ⟩ = nn₁ ,, nn₁
          hh = tm-irrel𝒯 refl refl refl (Eval-fun (↘ty mm) eU) (∈ty' mm) tU (∈tm mm) (proj₂ pp) h
  fundamental-ty (sub {σ = τ} ty x) {Δ} {σ} {ρp = ρp} rels =
    ∼preservation (∈ty mm) (∼symm (∼scomp ty x (derₛ rels))) h
    where
      mm = proj₂ (models-ty (sub ty x)) ρp ; hs = proj₂ (proj₂ (models-sub x)) ρp
      h = fundamental-ty ty (fundamentalₛ ρp (∈s hs) x rels (↘s1 hs))
          
  fundamental-tm : ∀{Γ t T} → (p : Γ ⊢ t ∶ T) → Γ ⊧ t ∶ T [ p ]
  fundamental-tm (var x) {ρp = ρp} rels = 
    ∼preservation-tm (∈ty' mm) (∈tm mm) (∼Sub' (sub x (⊢↑ x)) (∼IdR sd)) 
      (∼Sub (∼refl (var x)) (∼IdR sd)) (varFundamental x ρp rels (rId (invert-ctx-sub sd)))
    where mm = proj₂ (models-tm (var x)) ρp ; sd = (derₛ rels)
  fundamental-tm (lam td) {ρp = ρp} rels =
    (semLam _) ,, _ ,, (∼Sub' pp (∼refl ss) ,, td ,, ((∼refl (sub (lam td) ss)) ,, 
      (λ w → convert-®-sub w ρp rels) ,, λ x q x₁ → 
        h (#® (proj₂ (split-ctx (invert-ctx-tm td))) (↑® rels x) x₁)))
    where ss = derₛ rels ; pp = Π (invert-ty td) ; h = fundamental-tm td
  fundamental-tm (app {A = A} {B} {t} {s} {σ} sd Bd tm tm₁) {σ = τ} {ρp = ρp} rels with proj₂ (models-tm tm) ρp
  fundamental-tm (app {A = A} {B} {t} {s} {σ} sd Bd tm tm₁) {σ = τ} {ρp = ρp} rels | ⟨ ⟨ eSub x ePi ∣ 𝒰⊆𝒯 () ∣ nn₁ ⟩ ∣ ↘t3 ∣ ↘t4 ⟩
  fundamental-tm(app  {Γ = Γ} {Δ = Δ}  {A = A} {B} {t} {s} {σ} sd Bd tm tm₁) {Δ = ∇} {σ = τ} {ρp = ρp} rels | mmm@(⟨ ⟨ eSub {ρ' = ρ2} x ePi ∣ tPi Ah Bh ∣ nn₁ ⟩ ∣ ↘t3 ∣ ↘t4 ⟩) = 
       ∼preservation-tm (∈ty' mah) (∈tm mah) (∼symm (∼compdist-ty Bd tu sd tm₁)) (∼coe (∼Sub (∼refl ap) (∼refl tu)) (∼compdist-ty Bd tu sd tm₁))
         (tm-irrel𝒯 refl (Eval-fun (eApp (↘t1 mm) (↘t2 mm') (↘ap (ff pp))) (↘t1 mah)) refl 
           (Eval-fun (eSub (sCons x (↘t1 mm')) (ev (Bh pp))) (↘ty mah)) (∈t (Bh pp)) (∈ty' mah) (●∈tm (ff pp)) (∈tm mah) hh)
      where
        ht = fundamental-tm tm ; hs = fundamental-tm tm₁ ; hB = fundamental-ty Bd
        ap = app sd Bd tm tm₁
        mm = proj₂ (models-tm tm) ρp ; mm' = proj₂ (models-tm tm₁) ρp
        ms = proj₂ (proj₂ (models-sub sd)) ρp
        meh = proj₂ (models-tm ap) ρp
        mah = tmAppLemma mmm mm'
        pi = Π Bd ; tu = derₛ rels
        cmp = ⊢· sd tu
        h1 = ht rels ; h2 = hs rels
        h1' : ∇ ⊢ t [ τ ]ₛ ∶ (Π A B [ σ · τ ]ₛ) ® tPi Ah Bh ∋ nn₁
        h1' = ∼preservation-tm (tPi Ah Bh) nn₁ (∼scomp pi sd tu) (∼refl (sub tm tu)) 
                (tm-irrel𝒯 refl (Eval-fun (↘t1 mm) ↘t3) refl (Eval-fun (↘ty mm) (eSub (↘s1 ms) 
                  (≡Eval ePi (cong (DΠ A B) (Evals-fun x (↘s1 ms)))))) (∈ty' mm) (tPi Ah Bh) (∈tm mm) nn₁ h1)

        ff : res mm ∈ El𝒯 (tPi Ah Bh)
        ff = sameTerm𝒯≃ (Eval-fun (↘ty mm) (eSub x ePi)) (∈ty' mm) (tPi Ah Bh) (∈tm mm)
        pp : res mm' ∈ El𝒯 (∈t Ah)
        pp = sameTerm𝒯≃ (Eval-fun (↘ty mm') (eSub x (ev Ah))) (∈ty' mm') (∈t Ah) (∈tm mm')
        relcmp : ∇ ⊢ₛ σ · τ ∶ Δ ® ∈s ms
        relcmp = fundamentalₛ ρp (∈s ms) sd rels (↘s1 ms)
        p2p : ρ2 ∈ₛ ⟦ Δ ⟧ₛ
        p2p = subst (_∈ₛ ⟦ _ ⟧ₛ) (Evals-fun (↘s1 ms) x) (∈s ms)
        relcmp' : ∇ ⊢ₛ σ · τ ∶ Δ ® p2p
        relcmp' = fundamentalₛ ρp p2p sd rels x
        Ad = proj₂ (split-ctx (invert-ctx-ty Bd))
        h2' : ∇ ⊢ s [ τ ]ₛ ∶ A [ σ · τ ]ₛ ® ∈t Ah ∋ pp
        h2' = ∼preservation-tm (∈t Ah) pp (∼scomp Ad sd tu) (∼refl (sub tm₁ tu))
                (tm-irrel𝒯 refl refl refl (Eval-fun (↘ty mm') (eSub x (ev Ah))) (∈ty' mm') (∈t Ah) (∈tm mm') pp h2)
        mmB = proj₂ (models-ty Bd) (cExt p2p ⟨ (ev Ah) ∣ (∈t Ah) ∣ pp ⟩)
        BB' : ∇ ⊢ B [ (σ · τ) , (s [ τ ]ₛ) ]ₛ ® ∈ty mmB
        BB' = hB (#® Ad relcmp' h2')
        BB : ∇ ⊢ B [ (σ · τ) , (s [ τ ]ₛ) ]ₛ ® ∈t (Bh pp)
        BB = ty-irrel𝒯 refl (Eval-fun (↘t1 mmB) (ev (Bh pp))) (∈ty mmB) (∈t (Bh pp)) BB'

        hh : ∇ ⊢ ((t · s) [ τ ]ₛ) ∶ (B [ (σ · τ) , (s [ τ ]ₛ) ]ₛ) ® ∈t (Bh pp) ∋ ●∈tm (ff pp)
        hh with h1'
        hh | semLam t' ,, (Γ' ,, γ) ,, (b) ,, tdd ,, tm-conv ,, scv ,, h = 
           ∼preservation-tm (∈t (Bh pp)) (●∈tm (ff pp)) BBconv 
             tconv (tm-irrel𝒯 refl eqq refl refl (∈t (Bh pp)) (∈t (Bh pp)) (●∈tm (nn₁ pp)) (●∈tm (ff pp)) hhh)
          where
            sst : ∇ ⊢ s [ τ ]ₛ ∶ A [ σ · τ ]ₛ
            sst = coe (sub tm₁ tu) (∼scomp Ad sd tu)
            c = invert-ctx-sub tu
            sgg = inverti-idsub-sub (proj₁ (eq-lemma-sub (scv (rId c))))
            eqq = (●-fun (↘ap (nn₁ pp)) (subst (_● res mm' ↘ res (ff pp)) (Eval-fun (↘t1 mm) (↘t1 mmm)) (↘ap (ff pp))))
            Ad' = proj₂ (split-ctx (invert-ctx-tm tdd))
            sbbb = (subst (∇ ⊢ₛ _ ∼_∶ _) (cong (reifyEnv (clen ∇)) 
                     (Evals-fun (↘s1 ms) x)) (convert-®-sub (rId c) (∈s ms) relcmp))
            Aconv : ∇ ⊢ A [ γ · Id ]ₛ ∼ A [ σ · τ ]ₛ
            Aconv = ∼trans (∼Sub (∼refl Ad') (scv (rId c))) (∼Sub (∼refl Ad) (∼symm (∼trans (∼symm (∼IdR cmp)) sbbb)))
            sgsg : ∇ ⊢ s [ τ ]ₛ ∶ (A [ γ ]ₛ)
            sgsg = coe (sub tm₁ tu) (∼trans (∼scomp Ad sd tu) (∼trans (∼symm Aconv) (∼Sub' Ad' (∼IdR sgg))))
            BBconv : ∇ ⊢ B [ (γ · Id) , (s [ τ ]ₛ) ]ₛ ∼ B [ (σ · τ) , (s [ τ ]ₛ) ]ₛ
            BBconv = ∼trans (∼Sub' (invert-ty tdd) (∼comp1 Ad' (scv (rId c)) (∼coe (∼refl (sub tm₁ tu)) (∼trans (∼scomp Ad sd tu) (∼symm Aconv))))) 
                            (∼Sub' Bd (∼comp1 Ad (∼trans (∼symm sbbb) (∼IdR cmp)) (∼coe (∼refl (sub tm₁ tu)) 
                              (∼trans (∼scomp Ad sd tu) (∼Sub' Ad (∼trans (∼symm (∼IdR cmp)) sbbb))))))
            eqg = (∼comp1 Ad' (∼symm (∼IdR sgg)) (∼refl sgsg))
            tconv : ∇ ⊢ t' [ (γ · Id) , (s [ τ ]ₛ) ]ₛ ∼ (t · s) [ τ ]ₛ ∶ (B [ (γ · Id) , (s [ τ ]ₛ) ]ₛ)
            tconv = ∼coe (∼symm (∼trans (∼sapp tm tm₁ sd tu Bd) (∼trans (∼app tm-conv (∼refl sst) (⊢· sd tu) Bd) 
              (∼coe (∼trans (∼β tdd sgg sgsg) (∼Sub (∼refl tdd) eqg)) (∼trans (∼Sub' (invert-ty tdd) eqg) BBconv))))) (∼symm BBconv)
            hhh : ∇ ⊢ t' [ (γ · Id) , (s [ τ ]ₛ) ]ₛ ∶ B [ (γ · Id) , (s [ τ ]ₛ) ]ₛ ® ∈t (Bh pp) ∋ ●∈tm (nn₁ pp)
            hhh = h (rId c) pp (∼preservation-tm (∈t Ah) pp (∼symm Aconv) (∼coe (∼refl (sub tm₁ tu)) (∼scomp Ad sd tu)) h2')
        hh | semNe e ,, h1 ,, h2 = tm-irrel𝒯 refl (●-fun (subst (_● res mm' ↘ DNe (NeApp e (res mm'))) 
                   (Eval-fun (↘t1 mmm) (↘t1 mm)) ●Ne) (↘ap (ff pp))) refl refl (∈t (Bh pp)) (∈t (Bh pp)) el (●∈tm (ff pp)) ane
          where
            el = hasNe (El𝒯 (∈t (Bh pp))) (NeApp e (res mm'))
            ane : ∇ ⊢ ((t · s) [ τ ]ₛ) ∶ (B [ (σ · τ) , (s [ τ ]ₛ) ]ₛ) ® ∈t (Bh pp) ∋ el
            ane = allNe (∈t (Bh pp)) h2 (λ w → convert-® w (∈t (Bh pp)) BB) 
                   λ {Δ'} {w} wp → let rr = renIsSub wp ; turr = ⊢· tu rr
                                       tmt : Δ' ⊢ t [ τ · w ]ₛ ∼ reifyNe (clen Δ') e ∶ Π A B [ (σ · τ) · w ]ₛ
                                       tmt = ∼coe (∼trans (∼symm (∼coe (∼scomp tm tu rr) (∼trans (∼scomp pi sd (⊢· tu rr)) 
                                                  (∼trans (∼Sub' pi (∼symm (∼Assoc rr tu sd))) (∼symm (∼scomp pi cmp rr)))))) 
                                                  (convert-®-tm wp (tPi Ah Bh) nn₁ h1')) (∼scomp pi cmp rr)
                                       tms : Δ' ⊢ s [ τ · w ]ₛ ∼ reify (clen Δ') (res mm') ∶ (A [ (σ · τ) · w ]ₛ)
                                       tms = ∼coe (∼trans (∼symm (∼coe (∼scomp tm₁ tu rr) (∼trans (∼scomp Ad sd (⊢· tu rr)) 
                                             (∼trans (∼Sub' Ad (∼symm (∼Assoc rr tu sd))) (∼symm (∼scomp Ad cmp rr)))))) 
                                             (convert-®-tm wp (∈t Ah) pp h2')) (∼scomp Ad cmp rr)
                                   in ∼coe (∼trans (∼scomp ap tu rr) (∼trans (∼coe (∼sapp tm tm₁ sd (⊢· tu rr) Bd) 
                                           (∼symm (∼compdist-ty Bd turr sd tm₁))) (∼coe (∼app tmt tms (⊢· cmp rr) Bd) 
                                           (∼symm (∼trans (∼compdist-ty Bd turr sd tm₁) (∼Sub' Bd (∼comp1 Ad (∼symm (∼Assoc rr tu sd)) 
                                             (∼coe (∼Sub (∼refl tm₁) (∼refl turr)) (∼scomp Ad sd turr))))))))) 
                                           (∼trans (∼symm (∼scomp (sub Bd (⊢, sd Ad tm₁)) tu rr)) (∼Sub (∼compdist-ty Bd tu sd tm₁) (∼refl rr)))

  fundamental-tm (coe tm x) {ρp = ρp} rels =
    tm-irrel𝒯 refl (Eval-fun (↘t1 mm) (↘t1 mm')) refl (Eval-fun (↘ty mm) 
      (↘t1 (models-ty-eq x ρp))) (∈ty' mm) (∈ty' mm') (∈tm mm) (∈tm mm') hh
    where
      d = derₛ rels ; h = fundamental-tm tm rels
      mm = proj₂ (models-tm tm) ρp ; mm' = proj₂ (models-tm (coe tm x)) ρp
      hh = ∼preservation-tm (∈ty' mm) (∈tm mm) (∼Sub x (∼refl d)) 
        (∼Sub (∼refl tm) (∼refl d)) h

  fundamental-tm (sub tm x) {ρp = ρp} rels = 
    ∼preservation-tm (∈ty' mm') (∈tm mm') (∼symm (∼scomp (invert-ty tm) x (derₛ rels))) 
      (∼symm (∼scomp tm x (derₛ rels)))
      (tm-irrel𝒯 refl (Eval-fun (↘t1 mm) (swap-ev (↘t1 mm') (↘s1 mms))) refl 
        (Eval-fun (↘ty mm) (swap-ev (↘ty mm') (↘s1 mms))) (∈ty' mm) (∈ty' mm') (∈tm mm) (∈tm mm') h')
    where
      mms = proj₂ (proj₂ (models-sub x)) ρp
      mm = proj₂ (models-tm tm) (∈s mms) ; mm' = proj₂ (models-tm (sub tm x)) ρp
      h = fundamentalₛ ρp (∈s mms) x rels (↘s1 mms)
      h' = fundamental-tm tm h
      sd = derₛ rels

  fundamentalₛ : ∀{Γ Δ Θ ρ ρ' γ δ} (ρp : ρ ∈ₛ ⟦ Γ ⟧ₛ) (ρp' : ρ' ∈ₛ ⟦ Θ ⟧ₛ)
               → (γder : Γ ⊢ₛ γ ∶ Θ)
               → Δ ⊢ₛ δ ∶ Γ ® ρp → ⟦ γ ⟧ₛ ρ ↘ ρ'
               → Δ ⊢ₛ γ · δ ∶ Θ ® ρp'
  fundamentalₛ p p' (⊢Id c) rel sId = irrelₛ p p' (∼® (⊢· (⊢Id c) (derₛ rel)) rel (∼IdL (derₛ rel)))
  fundamentalₛ {Γ} {Δ} {Θ # A} {γ = .(σ , t)} {δ} p (cExt x₁ x₂) (⊢, {σ = σ} {t} sd Ad x) rel (sCons e x₃) = 
    ∼® (⊢· (⊢, sd Ad x) dd) (#® Ad (fundamentalₛ p x₁ sd rel e) 
      (∼preservation-tm (inT x₂) (nn x₂) (∼scomp Ad sd dd) (∼refl (sub x dd)) 
       (tm-irrel𝒯 refl (Eval-fun (↘t1 mm) x₃) refl (Eval-fun (swap-ev (↘ty mm) e) (ev x₂)) 
         (∈ty' mm) (inT x₂) (∈tm mm) (nn x₂) h))) (∼Dist Ad dd sd x)
    where dd = derₛ rel ; mm = proj₂ (models-tm x) p ; h = fundamental-tm x rel
  fundamentalₛ p p' (⊢· sd sd₁) rel (sComp e e₁) =
    irrelₛ p' p' (∼® (⊢· (⊢· sd sd₁) (derₛ rel)) (fundamentalₛ boo p' sd 
      (fundamentalₛ p boo sd₁ rel e) e₁) (∼Assoc (derₛ rel) sd₁ sd))
    where eq = Evals-fun (↘s1 (proj₂ (proj₂ (models-sub sd₁)) p)) e
          boo = (subst (_∈ₛ ⟦ _ ⟧ₛ) eq (∈s (proj₂ (proj₂ (models-sub sd₁)) p)))
  fundamentalₛ (cExt x₁ x₂) p' (⊢↑ y) rel sUp = irrelₛ x₁ p' h
    where h = var-aux y x₁ x₂ rel
