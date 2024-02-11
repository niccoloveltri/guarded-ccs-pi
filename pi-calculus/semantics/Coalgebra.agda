{-# OPTIONS --cubical --guarded #-}

open import Cubical.Data.Sum hiding (inl; inr) 
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (lift;act)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Logic
open import Cubical.Relation.Nullary
open import CountablePowerSet
open import Basic
open import AbsNames
open import LaterPrims hiding (_∙_)

module pi-calculus.semantics.Coalgebra (ns : Names) where

open Names ns
open OpNames ns
open import Cubical.Data.Sigma
open import pi-calculus.Syntax ns
open import pi-calculus.Algebra ns
open import pi-calculus.semantics.Algebra ns
open import pi-calculus.semantics.Dynamics ns
open import pi-calculus.semantics.StructuralCongruence ns
open import pi-calculus.semantics.Model ns

-- F'-coalgebra structure on Pi, the functional variant of the
-- operational semantics.
module CoalgebraPi where

  open StepLemmata Pi (λ _ n → InitPi-alg n) mapPi

  step : ∀ {n} → Pi n → F' n (next Pi)
  step end      = ø
  step (out ch z · p) = η ((`out ch z (\ _ →  p)))
  step (inp ch · p) =
    (bind enum \ v → η (`inp ch v (next (mapPi (for-fresh v) p)))) ∪ η (`binp ch (next p))
  step (τ · p) = η (`τ \ _ → p)
  step (p ⊕ q)  = step p ∪ step q
  step (p ∣∣ q) = par p (step p) q (step q)
  step (ν p)    = stepνF (step p)
  step (guard x y p) = stepguard x y (step p)
  step (! p)    = stepL' (step p ∪ synchF (step p) (step p)) (\ _ → ! p)

-- F-coalgebra structure on Pi
module CoalgebraPi' where

  module SLPi = StepLemmataPi
  open SLPi

  step : ∀ {n} → Pi n → F n Pi
  step end      = ø
  step (out ch z · p) = η ((`out ch z p))
  step (inp ch · p) = (bind enum \ v → η ((`inp ch v (mapPi (for-fresh v) p)))) ∪ η (`binp ch p)
  step (τ · p) = η (`τ p)
  step (p ⊕ q)  = step p ∪ step q
  step (p ∣∣ q) = par p (step p) q (step q)
  step (ν p)    = stepνF (step p)
  step (guard x y p) = stepguard x y (step p)
  step (! p)    = stepL' (step p ∪ synchF (step p) (step p)) (! p)


  module O = CoalgebraPi
  module SL = StepLemmata Pi (λ _ n → InitPi-alg n) mapPi


-- The releationship between the F-coalgebra and the F'-coalgebra on
-- Pi.
  stepν-eq : ∀ {n} (v : Step Pi (suc n))
    → SL.stepν (v .theLabel , next (v .theX))
          ≡ mapP∞ (λ x → x .theLabel , next (x .theX)) (stepν v)
  stepν-eq (a , Q) with canNu? a
  stepν-eq (._ , Q) | out ch x = refl
  stepν-eq (._ , Q) | out2 ch x = refl
  stepν-eq (._ , Q) | bout ch = refl
  stepν-eq (._ , Q) | inp ch x = refl
  stepν-eq (._ , Q) | binp ch = refl
  stepν-eq (.τ , Q) | τ = refl
  stepν-eq (a , Q) | nope x = refl

  synch'-eq : ∀ {n} {x1 x2 : Step Pi n}
    → (f : ∀ {n} → Pi n → Pi n → Pi n) 
    → SL.Synch'.synch' (λ _ → f) (λ _ → ν) (x1 .theLabel , next (x1 .theX)) (x2 .theLabel , next (x2 .theX))
                ≡ mapP∞ ((λ x → x .theLabel , next (x .theX))) (SLPi.Synch'.synch' f ν x1 x2)
  synch'-eq {_} {(a , x1)} {(b , x2)} f with canSynchL? a b
  ... | local x _ = refl
  ... | bound _ = refl
  ... | nope = refl

  stepL-eq : ∀ {n} (v : F n Pi) (P : Pi n)
    → SL.stepL (mapP∞ (λ x → x .theLabel , next (x .theX)) v) P
              ≡ mapP∞ (λ x → x .theLabel , next (x .theX)) (stepL v P)
  stepL-eq v P = mapmapP∞ _ _ v ∙ sym (mapmapP∞ _ _ v)

  synchF-eq : ∀ {n} (v1 v2 : F n Pi)
    → SL.synchF (mapP∞ (λ x → x .theLabel , next (x .theX)) v1) (mapP∞ (λ x → x .theLabel , next (x .theX)) v2)
        ≡ mapP∞ (λ x → x .theLabel , next (x .theX)) (synchF v1 v2)
  synchF-eq v1 v2 = bind-map v1 _ _ ∙ cong (bind v1) (funExt \ v → bind-map v2 _ _)
                   ∙ cong (bind v1) (funExt \ x1 → cong (bind v2) (funExt \ x2 → cong₂ _∪_ (synch'-eq _) (synch'-eq _)))
                  ∙ sym (map-bind v1 _ _ ∙ cong (bind v1) (funExt (\ _ → map-bind v2 _ _)))

  step-eq : ∀ {n} (P : Pi n) → O.step P ≡ mapF (λ _ _ → next) (step P)
  step-eq end = refl
  step-eq (out ch x · P) = refl
  step-eq (inp ch · P) = cong₂ _∪_ (sym (map-bind enum _ _)) refl
  step-eq (τ · P) = refl
  step-eq (P ⊕ P₁) = cong₂ _∪_ (step-eq P) (step-eq P₁)
  step-eq (P ∣∣ P₁) = cong₂ _∪_ (cong₂ _∪_ (cong₂ mapP∞ refl (step-eq P) ∙ stepL-eq (step P) P₁)
                                                    (cong₂ mapP∞ refl (step-eq P₁) ∙ mapmapP∞ _ _ (step P₁) ∙ sym (mapmapP∞ _ _ (step P₁))))
                                         (cong₂ bind (step-eq P) (funExt \ _ → cong₂ bind (step-eq P₁) refl)
                                         ∙ synchF-eq (step P) (step P₁) )
  step-eq (ν P) = sym (map-bind (step P) _ _ ∙ sym (cong₂ bind (step-eq P) refl ∙ bind-map (step P) _ _ ∙ cong (bind (step P))
          (funExt \ v → stepν-eq v)))
  step-eq (! P) =
    (cong SL.stepL (cong₂ _∪_ (step-eq P) (cong₂ SL.synchF (step-eq P) (step-eq P))) <* (! P))
    ∙ (cong SL.stepL (cong (_∪_ (mapP∞ (λ x → x .theLabel , next (x .theX)) (step P))) (synchF-eq (step P) (step P))) <* (! P))
    ∙ stepL-eq (step P ∪ synchF (step P) (step P)) (! P)
  step-eq (guard x y P) with decName x y
  step-eq (guard x y P) | yes p = step-eq P
  step-eq (guard x y P) | no ¬p = refl


-- The relationship between the coalgebra structure on Pi and the
-- operational semantics:
--  ∥ P [ a ]↦ P' ∥₁  ≃  ∃ Q Q'. P ≈ Q  ×  P' ≈ Q'  ×  ⟨ (a , Q') ∈ step Q ⟩
module _ where

  open StepLemmataPi
  open StepLemmata2Pi
  open CoalgebraPi'

  out∈stepν : ∀ {n} (ch v : Name n) {P}
    → ⟨ `out ch v ((ν P)) ∈ stepν (`out (ι ch) (ι v) (P)) ⟩ 
  out∈stepν ch v with canNu? (out (ι ch) (ι v))
  out∈stepν ch v {P} | out p q = ∣ (λ i → (out (ι-inj _ _ p i) (ι-inj _ _ q i) , ν P)) ∣₁
  out∈stepν ch v | out2 _ p = ⊥-rec (fresh-ι p)
  out∈stepν ch v | nope (out p) = ⊥-rec (fresh-ι p)

  bout∈stepν : ∀ {n} (ch : Name n) {P}
    → ⟨ `bout ch ((ν (mapPi swap P))) ∈ stepν (`bout (ι ch) (P)) ⟩
  bout∈stepν ch with canNu? (bout (ι ch))
  bout∈stepν ch | bout p = ∣ StepPath refl (congS bout (ι-inj _ _ p)) refl ∣₁
  bout∈stepν ch | nope (bout x) = ⊥-rec (fresh-ι x)

  bout∈stepν2 : ∀ {n} (ch : Name n) {P}
    → ⟨ `bout ch (P) ∈ stepν (`out (ι ch) (fresh n) (P)) ⟩
  bout∈stepν2 ch  with canNu? (out (ι ch) (fresh _))
  bout∈stepν2 ch | out x x₁ = ⊥-rec (fresh-ι (sym x₁))
  bout∈stepν2 ch | out2 p q = ∣ StepPath refl (congS bout (ι-inj _ _ p)) refl ∣₁
  bout∈stepν2 ch | nope (out x) = ⊥-rec (fresh-ι x)

  inp∈stepν : ∀ {n} (ch v : Name n) {P}
    → ⟨ `inp ch v ((ν P)) ∈ stepν (`inp (ι ch) (ι v) (P)) ⟩
  inp∈stepν ch v with canNu? (inp (ι ch) (ι v))
  inp∈stepν ch v | inp p q = ∣ StepPath refl (λ i → inp (ι-inj _ _ p i) (ι-inj _ _ q i)) refl ∣₁
  inp∈stepν ch v | nope (inp (_⊎_.inl x)) = ⊥-rec (fresh-ι x)
  inp∈stepν ch v | nope (inp (_⊎_.inr x)) = ⊥-rec (fresh-ι x)

  binp∈stepν : ∀ {n} (ch : Name n) {P}
    → ⟨ `binp ch ((ν (mapPi swap P))) ∈ stepν (`binp (ι ch) (P)) ⟩
  binp∈stepν ch with canNu? (binp (ι ch))
  binp∈stepν ch | binp p = ∣ StepPath refl (congS binp (ι-inj _ _ p)) refl ∣₁
  binp∈stepν ch | nope (binp x) = ⊥-rec (fresh-ι x)

  out-ν-opsem : ∀ {n} (ch v : Name (suc n)) {aQ : Step Pi n} {P}
    → ⟨ aQ ∈ stepν (`out ch v (P)) ⟩
    → ∥ Σ (Name n) (λ ch' → Σ (Name n) (λ v' → (ch ≡ ι ch') × (v ≡ ι v') × (aQ ≡ `out ch' v' ((ν P)))))
        ⊎
        Σ (Name n) (λ ch' → (ch ≡ ι ch') × (v ≡ fresh _) × (aQ ≡ `bout ch' (P))) ∥₁
  out-ν-opsem ch v m with canNu? (out ch v)
  out-ν-opsem ch v m | out r r' = PT.map (λ eq → _⊎_.inl (_ , _ , r , r' , eq)) m
  out-ν-opsem ch v m | out2 r r' = PT.map (λ eq → _⊎_.inr (_ , r , r' ,  eq)) m

  bout-ν-opsem : ∀ {n} (ch : Name (suc n)) {aQ : Step Pi n} {P}
    → ⟨ aQ ∈ stepν (`bout ch (P)) ⟩
    → ∥ Σ (Name n) (λ ch' → (ch ≡ ι ch') × (aQ ≡ `bout ch' ((ν (mapPi swap P))))) ∥₁
  bout-ν-opsem ch m with canNu? (bout ch)
  bout-ν-opsem ch m | bout r = PT.map (λ eq → _ , r ,  eq) m

  inp-ν-opsem : ∀ {n} (ch v : Name (suc n)) {aQ : Step Pi n} {P}
    → ⟨ aQ ∈ stepν (`inp ch v (P)) ⟩
    → ∥ Σ (Name n) (λ ch' → Σ (Name n) (λ v' → (ch ≡ ι ch') × (v ≡ ι v') × (aQ ≡ `inp ch' v' ((ν P))))) ∥₁
  inp-ν-opsem ch v m with canNu? (inp ch v)
  inp-ν-opsem ch v m | inp r r' = PT.map (λ eq → _ , _ , r , r' ,  eq) m

  binp-ν-opsem : ∀ {n} (ch : Name (suc n)) {aQ : Step Pi n} {P}
    → ⟨ aQ ∈ stepν (`binp ch (P)) ⟩
    → ∥ Σ (Name n) (λ ch' → (ch ≡ ι ch') × (aQ ≡ `binp ch' ((ν (mapPi swap P))))) ∥₁
  binp-ν-opsem ch m with canNu? (binp ch)
  binp-ν-opsem ch m | binp r = PT.map (λ eq → _ , r ,  eq) m

  _≈∈≈step_ : ∀ {n} → Step Pi n → Pi n → Set
  (a , Q) ≈∈≈step P = ∥ Σ _ (λ P' → Σ _ (λ Q' → P ≈ P' × Q ≈ Q' × ⟨ (a , Q') ∈ step P' ⟩)) ∥₁

  opsem→∈step : ∀ {n m} (P : Pi n) a (P' : Pi m)
    → P [ a ]↦ P' →  (a , P') ≈∈≈step P
  opsem→∈step .(out ch v · P') .(out ch v) P' (out ch v) =  ∣ _ , _ , refl≈ , refl≈ , ∣ refl ∣₁ ∣₁
  opsem→∈step .(inp ch · _) .(inp ch v) .(mapPi (for-fresh v) _) (inp ch v) = ∣ _ , _ , refl≈ , refl≈ , inl (bind-in _ _ enum (_ , (enum-in v , ∣ refl ∣₁))) ∣₁
  opsem→∈step .(τ · P') .τ P' τ =  ∣ _ , _ , refl≈ , refl≈ , ∣ refl ∣₁ ∣₁
  opsem→∈step .(_ ⊕ _) a P' (sumtr t) = (opsem→∈step _ _ _ t) >>PT \ { (Q , Q' , Qc , Q'c , m) →
              ∣ _ , _ , cong⊕ Qc refl≈ , Q'c , inl m ∣₁ }
  opsem→∈step (P ∣∣ P2) a .(_ ∣∣ mapPi (labelInj a .fst) _) (partr t) = opsem→∈step _ _ _ t >>PT \ where
    (Q , _ , Qc , Q'c , m) →  ∣ (_ , _ , cong∣∣ Qc refl≈ , cong∣∣ Q'c refl≈  ,  inl (inl (lemma-4·1-part1 (mapStep (λ m i x → x ∣∣ mapPi (fst i) P2)) _ (step Q) m))) ∣₁
  opsem→∈step (P ∣∣ P2) .τ (P' ∣∣ Q') (com {ch = ch}{v} t t₁) = opsem→∈step _ _ _ t >>PT \ where
    (Q , _ , Qc , Q'c , m) → opsem→∈step _ _ _ t₁ >>PT \ where
     (Q1 , _ , Qc1 , Q'c1 , m1) →
       ∣ (_ , _ , cong∣∣ Qc Qc1  , cong∣∣ Q'c Q'c1 ,
       inr (0 , bind-in _ _ (step Q)
       (_ , m , bind-in _ _ (step Q1)
       (_ , m1 , inl ( (( (synch'-in-s (_∣∣_) _ ∣ (_ , _ , _ , _ , refl , refl , refl) ∣₁) )) ))))) ∣₁
  opsem→∈step (P ∣∣ P2) .τ (ν (P' ∣∣ Q')) (close {ch = ch} t t₁) = opsem→∈step _ _ _ t >>PT \ where
    (Q , _ , Qc , Q'c , m) → opsem→∈step _ _ _ t₁ >>PT \ where
     (Q1 , _ , Qc1 , Q'c1 , m1) → ∣ (_ , _ , cong∣∣ Qc Qc1 , congν (cong∣∣ Q'c Q'c1) ,
       inr (0 , bind-in _ _ (step Q)
       (_ , m , bind-in _ _ (step Q1)
       (_ , m1 , inl ( ((synch'-in-f (_∣∣_) _ ∣ (_ , _ , _ , refl , refl , refl) ∣₁)) ))))) ∣₁
  opsem→∈step (ν P) (out ch v) ._ (res t) = opsem→∈step _ _ _ t >>PT \ where
    (Q , _ , Qc , Q'c , m) → ∣ (_ , _ , congν Qc , congν Q'c , bind-in stepν _ (step Q) (_ , m , out∈stepν ch v)) ∣₁
  opsem→∈step (ν P) (bout ch) ._ (res t) = opsem→∈step _ _ _ t >>PT \ where
    (Q , _ , Qc , Q'c , m) → ∣ (_ , _ , congν Qc , congν (map≈ swap Q'c) ,  bind-in stepν _ (step Q) (_ , m , bout∈stepν ch)) ∣₁
  opsem→∈step (ν P) (inp ch v) ._ (res t) = opsem→∈step _ _ _ t >>PT \ where
    (Q , _ , Qc , Q'c , m) → ∣ (_ , _ , congν Qc , congν Q'c , bind-in stepν _ (step Q) (_ , m , inp∈stepν ch v)) ∣₁
  opsem→∈step (ν P) (binp ch) ._ (res t) = opsem→∈step _ _ _ t >>PT \ where
    (Q , _ , Qc , Q'c , m) →  ∣ (_ , _ , congν Qc  , congν (map≈ swap Q'c) , bind-in stepν _ (step Q) (_ , m , binp∈stepν ch)) ∣₁
  opsem→∈step (ν P) τ ._ (res t) = opsem→∈step _ _ _ t >>PT \ where
    (Q , _ , Qc , Q'c , m) → ∣ _  , _ , congν Qc , congν Q'c , bind-in stepν _ (step Q) (_ , m , ∣ refl ∣₁) ∣₁
  opsem→∈step (ν P) .(bout _) P' (opn {ch = ch} t) = opsem→∈step _ _ _ t >>PT \ where
    (Q , _ , Qc , Q'c , m) → ∣ _  , _ , congν Qc , Q'c , bind-in stepν _ (step Q) (_ , m , bout∈stepν2 ch) ∣₁
  opsem→∈step P a P' (conv t x x₁) = opsem→∈step _ _ _ t >>PT \ { (Q , Q' , Qc , Q'c , m ) → ∣ Q , _ , (sym≈ x ∙≈ Qc) , (sym≈ x₁ ∙≈ Q'c) , m ∣₁ }
  opsem→∈step .(inp ch · P') .(binp ch) P' (binp ch) = ∣ _ , _ , refl≈ , refl≈ , inr (0 , ∣ refl ∣₁) ∣₁

  subst↦ : {n : ℕ} {P : Pi n} {aq br : Step Pi n} → aq ≡ br
    → P [ theLabel aq ]↦ theX aq → P [ theLabel br ]↦ theX br
  subst↦ {P = P} {aq} =
    J (\ br eq → P [ theLabel aq ]↦ theX aq → P [ theLabel br ]↦ theX br) \ x -> x 

  ∈step→opsem : ∀ {n m} (P : Pi n) a (P' : Pi m)
    → ⟨ (a , P') ∈ step P ⟩ → ∥ P [ a ]↦ P' ∥₁
  ∈step→opsem (out ch x · P) a P' mem =
   PT.map (λ r → subst↦ (sym r) (out ch x)) mem
  ∈step→opsem (inp ch · P) a Q mem = mem >>PT
    λ { (_⊎_.inl x) → bind-out (λ v → η (`inp ch v (mapPi (for-fresh v) P))) _ enum x >>PT
                 λ { (v , _ , eq) → PT.map (λ r → subst↦ (sym r) (inp ch v)) eq } 
    ; (_⊎_.inr x) → PT.map (λ r → subst↦ (sym r) (binp ch)) (x .snd) }
  ∈step→opsem (τ · P) a Q mem =
    PT.map (λ r → subst↦ (sym r) τ) mem
  ∈step→opsem (P₁ ⊕ P₂) a Q mem =
    mem >>PT λ { (_⊎_.inl aP'∈P₁) → PT.map (λ { (tr) → sumtr tr }) (∈step→opsem P₁ a Q aP'∈P₁)
              ; (_⊎_.inr aP'∈P₂) → PT.map (λ { (tr) → conv (sumtr tr) comm⊕ refl≈}) (∈step→opsem P₂ a Q (aP'∈P₂ .snd)) }
  ∈step→opsem (P₁ ∣∣ P₂) a Q mem =
    mem >>PT λ { (_⊎_.inl x) → x >>PT λ {
                            (_⊎_.inl aP'∈stepL) → mapP∞-out (mapStep (λ m i x → x ∣∣ mapPi (fst i) P₂)) (a , Q) (step P₁) aP'∈stepL >>PT
                            λ { ((_ , Q') , aQ'∈ , r) → PT.map (λ tr → subst↦ (sym r) (partr tr)) (∈step→opsem P₁ _ _ aQ'∈) }
                         ; (_⊎_.inr aP'∈stepR) → mapP∞-out (mapStep (λ m i x → mapPi (fst i) P₁ ∣∣ x)) (a , Q) (step P₂) (aP'∈stepR .snd) >>PT
                         λ { ((_ , Q') ,  aQ'∈ , r) → PT.map (λ tr → subst↦ (sym r) (conv (partr tr) comm∣∣ comm∣∣)) (∈step→opsem P₂ _ _ aQ'∈)}}
                ; (_⊎_.inr (_ , aP'∈synchF)) → bind-out (λ sp → bind (step P₂) (synch sp)) _ (step P₁) aP'∈synchF >>PT
                           λ { (aQ' , aQ'∈ , aQ∈) → bind-out (synch aQ') _  (step P₂) aQ∈ >>PT
                           λ { (aR , aR∈ , x) → x >>PT
                             λ { (_⊎_.inl x) → synch'-out' (_∣∣_) ν {P1 = aQ'}{aR} ( x) >>PT
                               λ { (synch'-s P1' P2' p q r) → ∈step→opsem P₁ _ _ aQ'∈ >>PT
                                 λ { tr1 → PT.map (λ tr2 → subst↦ (sym r) (com (subst↦ p tr1) (subst↦ q tr2))) (∈step→opsem P₂ _ _ aR∈)} 
                                ; (synch'-f P1' P2' p q r) → ∈step→opsem P₁ _ _ aQ'∈ >>PT
                                  λ tr1 → PT.map (λ tr2 → subst↦ (sym r) (close (subst↦ p tr1) (subst↦ q tr2))) (∈step→opsem P₂ _ _ aR∈) }
                             ; (_⊎_.inr x) → synch'-out' ((λ p q → q ∣∣ p)) ν {P1 = aR}{aQ'} ( (x .snd)) >>PT
                               λ { (synch'-s P1' P2' p q r) → ∈step→opsem P₁ _ _ aQ'∈ >>PT
                                 λ tr1 → PT.map (λ tr2 → subst↦ (sym r) (conv (com (subst↦ p tr2) (subst↦ q tr1)) comm∣∣ comm∣∣)) (∈step→opsem P₂ _ _ aR∈) 
                               ; (synch'-f P1' P2' p q r) → ∈step→opsem P₁ _ _ aQ'∈ >>PT
                                  λ tr1 → PT.map (λ tr2 → subst↦ (sym r) (conv (close (subst↦ p tr2) (subst↦ q tr1)) comm∣∣ (congν comm∣∣))) (∈step→opsem P₂ _ _ aR∈)}}  } }}
  ∈step→opsem (ν P) a Q mem = bind-out stepν _ (step P) mem >>PT
    λ { (`out ch v Q' , aQ'∈ , aQ∈) → ∈step→opsem P _ _ aQ'∈ >>PT λ tr →
      PT.map (λ { (_⊎_.inl (ch' , v' , p , q , r)) → subst↦ (sym r) (res (subst↦ (λ i → (out (p i) (q i) , Q')) tr))
                ; (_⊎_.inr (ch' , p , q , r)) → subst↦ (sym r) (opn (subst↦ (λ i → (out (p i) (q i) , Q')) tr))} ) (out-ν-opsem ch v aQ∈)
      ; (`bout ch Q' , aQ'∈ , aQ∈) → ∈step→opsem P _ _ aQ'∈ >>PT λ {(tr) →
      PT.map (λ { (ch' , p , r) → subst↦ (sym r) (res (subst↦ (λ i → (bout (p i) , Q')) tr)) }) (bout-ν-opsem ch aQ∈) }
      ; (`inp ch v Q' , aQ'∈ , aQ∈) → ∈step→opsem P _ _ aQ'∈ >>PT λ {(tr) →
      PT.map (λ { (ch' , v' , p , q , r) → subst↦ (sym r) (res (subst↦ (λ i → (inp (p i) (q i) , Q')) tr)) }) (inp-ν-opsem ch v aQ∈)}
      ; (`binp ch Q' , aQ'∈ , aQ∈) → ∈step→opsem P _ _ aQ'∈ >>PT λ {(tr) →
      PT.map (λ { (ch' , p , r) → subst↦ (sym r) (res (subst↦ (λ i → (binp (p i) , Q')) tr)) }) (binp-ν-opsem ch aQ∈) }
      ; (`τ Q' , aQ'∈ , aQ∈) → aQ∈ >>PT λ r → PT.map (λ tr → subst↦ (sym r) (res tr)) (∈step→opsem P _ _ aQ'∈)  }
  ∈step→opsem (guard x y P) a Q mem with decName x y
  ∈step→opsem (guard x y P) a Q mem | yes p =
    PT.map (λ { (tr) → conv tr (sym≈ (subst (λ z → guard x z P ≈ P) p guardrefl)) refl≈ }) (∈step→opsem P a Q mem)
  ∈step→opsem (! P) a Q mem = mem >>PT
    λ { (_⊎_.inl x) → mapP∞-out (mapStep (λ m₁ i x₁ → x₁ ∣∣ ! mapPi (fst i) P)) _ (step P) x >>PT
        λ { ((_ , Q') , aQ'∈ , r) → PT.map (λ tr → conv (subst↦ (sym r) (partr tr)) (sym≈ repl) refl≈) (∈step→opsem P _ _ aQ'∈)}
    ; (_⊎_.inr x) → mapP∞-out (mapStep (λ m₁ i x₁ → x₁ ∣∣ ! mapPi (fst i) P)) _ (synchF (step P) (step P)) (x .snd) >>PT
      λ { ((_ , Q') , aQ'∈ , r') → synchF-out' (step P) (step P) ( aQ'∈) >>PT
        λ { (con {P' = P'} {Q''} P'∈ Q''∈ aQ'∈) →  aQ'∈ >>PT
          λ { (_⊎_.inl x) → synch'-out' (_∣∣_) ν {P1 = P'}{Q''} ( x) >>PT
            λ { (synch'-s P1' P2' p q r) →  ∈step→opsem P _ _ P'∈ >>PT
              λ tr1 → PT.map (λ tr2 → conv (subst↦ (sym r') (partr (subst↦ (sym r) (com (subst↦ p tr1) (subst↦ q tr2))))) ((assoc∣∣ ∙≈ cong∣∣ refl≈ (sym≈ repl)) ∙≈ sym≈ repl) refl≈) 
                    (∈step→opsem P _ _ Q''∈) ;
            (synch'-f P1' P2' p q r) → ∈step→opsem P _ _ P'∈ >>PT
              λ tr1 → PT.map (λ tr2 → subst↦ (sym r') (conv (partr (subst↦ (sym r) (close (subst↦ p tr1) (subst↦ q tr2)))) ((assoc∣∣ ∙≈ cong∣∣ refl≈ (sym≈ repl)) ∙≈ sym≈ repl) refl≈))
                    (∈step→opsem P _ _ Q''∈) }
          ; (_⊎_.inr x) → synch'-out' ((λ p q → q ∣∣ p)) ν {P1 = Q''}{P'} ( (x .snd)) >>PT
            λ { (synch'-s P1' P2' p q r) → ∈step→opsem P _ _ P'∈ >>PT
              λ tr1 → PT.map (λ tr2 → subst↦ (sym (r' ∙ λ i → (r i .theLabel , r i .theX ∣∣ ! mapPi (fst (labelInj (r i .theLabel))) P)))
                                                (conv (partr (com (subst↦ p tr2) (subst↦ q tr1))) ((assoc∣∣ ∙≈ cong∣∣ refl≈ (sym≈ repl)) ∙≈ sym≈ repl) (cong∣∣ comm∣∣ refl≈)))
                    (∈step→opsem P _ _ Q''∈) 
            ; (synch'-f P1' P2' p q r) → ∈step→opsem P _ _ P'∈ >>PT
              λ tr1 → PT.map (λ tr2 → subst↦ (sym (r' ∙ λ i → (r i .theLabel , (r i .theX ∣∣ ! mapPi (fst (labelInj (r i .theLabel))) P))))
                                                (conv (partr (close (subst↦ p tr2) (subst↦ q tr1))) ((assoc∣∣ ∙≈ cong∣∣ refl≈ (sym≈ repl)) ∙≈ sym≈ repl) (cong∣∣ (congν comm∣∣) refl≈)))
                    (∈step→opsem P _ _ Q''∈)  }} } }}



  opsem-eq' : ∀ {n m} (P : Pi n) (a : Label n m) (P' : Pi m)
    → _≡_ {A = hProp₀} (∥ P [ a ]↦ P' ∥₁ , isPropPropTrunc) ((a , P') ≈∈≈step P , isPropPropTrunc)
  opsem-eq' P a P' =
    ⇔toPath (PT.rec isPropPropTrunc (opsem→∈step P a P'))
             (PT.rec isPropPropTrunc
                     (λ { (Q , Q' , eq , eq' , m) →
                       ∈step→opsem Q a Q' m >>PT λ m' → ∣ conv m' (sym≈ eq) (sym≈ eq') ∣₁}))

  opsem-eq : ∀ {n m} (P : Pi n) a (P' : Pi m)
    → ∥ P [ a ]↦ P' ∥₁ ≡ (a , P') ≈∈≈step P
  opsem-eq P a P' = cong fst (opsem-eq' P a P')

-- stepRel and piRel are two variants of the operational semantics
-- relations where the new processes P' is of the form "next Q".
-- They are equivalent relations.
  stepRel : ∀ {n m} (P : Pi n) a (P' : ▹ (Pi m)) → Set
  stepRel P a P' =
    ∥ (Σ _ \ Q → Σ _ \ Q1 → Σ _ \ Q2
      → P ≈ Q × (P' ≡ next Q1) × (Q1 ≈ Q2) × ⟨ (a , Q2) ∈ step Q ⟩) ∥₁

  stepRel' : ∀ {n m} (P : Pi n) a (P' : ▹ (Pi m)) → Set
  stepRel' P a P' = Σ _ \ Q' → (next Q' ≡ P') × ⟨ (a , Q') ∈ step P ⟩

  piRel : ∀ {n m} (P : Pi n) a (P' : ▹ (Pi m)) → Set
  piRel P a P' = ∥ Σ (Pi _) (λ Q' → (P' ≡ next Q') × P [ a ]↦ Q') ∥₁

  ∈step→opsem2 : ∀ {n m} (P : Pi n) a P' → stepRel {n}{m} P a P' → piRel P a P'
  ∈step→opsem2 P a P' x =
    x >>PT \ { (Q , Q1 , Q2 , Qc , refl' , Q'c , m) → ∈step→opsem Q _ _ m >>PT \ tr → ∣ Q1 , (refl' , (conv tr (sym≈ Qc) (sym≈ Q'c))) ∣₁  }

  opsem→∈step2 : ∀ {n m} (P : Pi n) a (P' : ▹ (Pi m)) → piRel P a P' → stepRel P a P'
  opsem→∈step2 P a P' =
    PT.rec squash₁
      (\ { (Q' , refl' , tr) →
          opsem→∈step _ _ _ tr >>PT \ { (Q , Q'' , Qc , Q''c , m) → ∣ Q , Q' , Q'' , Qc , refl' , Q''c , m ∣₁ }})

-- Since Proc n and PiMod n are Pi-algebras, there are maps
-- evalG : Pi n → Proc n
-- and
-- evalGM : Pi n → PiMod n
-- given by the initiality of Pi.
evalG = evalX ProcPi-alg 
evalGM = evalX PiMod-alg

-- But we know that Pi n is a F-coalgebra, so there exist an
-- evaluation typed Pi n → Proc n defined by guarded recursion (and
-- similarly an evaluation with the same type coming from the
-- F'-coalgebra structure of Pi).
module Eval where

  open CoalgebraPi

  eval-fun : ▹ (∀ n → Pi n → Proc n) → ∀ n → Pi n → Proc n
  eval-fun ih n p = Fold (mapF (λ m i q α → ih α m (q α)) (step p))

  eval : ∀ n → Pi n → Proc n
  eval = fix eval-fun

module Eval' where

  open CoalgebraPi'
  eval-fun : ▹ (∀ n → Pi n → Proc n) → ∀ n → Pi n → Proc n
  eval-fun ih n p = Fold (mapF (λ m i q α → ih α m q) (step p))

  eval : ∀ n → Pi n → Proc n
  eval = fix eval-fun

-- The two inductively-defined evaluation maps are equal.
  eval-eq' : ∀ {n} (P : Pi n) → Eval.eval _ P ≡ eval _ P
  eval-eq' {n} P =
    cong fix (funExt \ r → funExt \ n → funExt \ p →
      cong (Fold {n}) (cong (mapF (λ m i q α → r α m (q α))) (step-eq p)
                      ∙ mapmapP∞ _ _ (step p)))
           <* n <* P

open PiMod
open isPi-model

-- The inductively-defined evaluation map (arising from the
-- Pi-algebra structure on Proc) is equivalent to the
-- guarded-recursive one (arising from the F-coalgebra structure on
-- Pi). This is proved by guarded recursion.
module _ (ih : ▹ ∀ {n} (P : Pi n) → Eval.eval _ P ≡  evalGM P .elem _ (λ x → x)) where

  open Eval
  open CoalgebraPi
  module SL = StepLemmata Pi (λ _ → InitPi-alg) mapPi
  module SL' = StepLemmata Proc (λ _ → ProcPi-alg) (mapProc _ _)

  eval-lift-id : ∀ {n} (q : ▹ Pi (suc n)) → (@tick α : Tick)
    → evalGM (q α) .elem (suc n) (lift (λ x → x)) ≡ eval _ (q α)
  eval-lift-id q α =
    sym (ih α (q α) ∙ cong (evalX PiMod-alg (q α) .elem _) (sym (funExt lift-id)))

  eval-map : ∀ {n m} (q : ▹ Pi n) (f : Inj n m) → (@tick α : Tick)
    → evalGM (mapPi (fst f) (q α)) .elem _ (λ x → x) ≡ mapProc _ _ (fst f) (eval _ (q α))
  eval-map q f α =
    (λ i → PiMod-model .map-evalX (fst f) (q α) i .elem _ (λ x → x))
    ∙ sym (evalGM (q α) .elem-nat f (\ x → x))
    ∙ cong (mapProc _ _ (fst f)) (sym (ih α (q α)))

  guard-step : ∀ {n} x y P
    → eval-fun (next (fix eval-fun)) n (guard x y P) ≡
               Fold (SL'.stepguard x y (Unfold (eval n P)))
  guard-step x y P with decName x y
  guard-step x y P | yes p = sym (fix-eq eval-fun <* _ <* P)
  guard-step x y P | no ¬p = refl

  nu-step : ∀ {n} (v : _)
    → mapF' {n = n} (\ α m i x → eval m x) (SL.stepν v)
        ≡ SL'.stepν (mapStep (\ m i x α → eval _ (x α)) v)
  nu-step (a , Q) with canNu? a
  nu-step (.(out _ _) , Q) | out x x₁ = cong η (StepPath refl refl (later-ext \ α → ih α (ν (Q α)) ∙ cong νProc (eval-lift-id Q α)))
  nu-step (.(out _ _) , Q) | out2 x x₁ = cong η (StepPath refl refl refl)
  nu-step (.(inp _ _) , Q) | inp x x₁ = cong η (StepPath refl refl (later-ext \ α → ih α (ν (Q α)) ∙ cong νProc (eval-lift-id Q α)))
  nu-step (.(bout _) , Q) | bout x = cong η (StepPath refl refl (later-ext \ α → ih α (ν (mapPi swap (Q α)))
    ∙ cong νProc (cong (evalX PiMod-alg (mapPi _ (Q α)) .elem _) (funExt lift-id) ∙ eval-map Q (_ , swap-inj) α)))
  nu-step (.(binp _) , Q) | binp x = cong η (StepPath refl refl (later-ext \ α → ih α (ν (mapPi swap (Q α)))
    ∙ cong νProc (cong (evalX PiMod-alg (mapPi _ (Q α)) .elem _) (funExt lift-id) ∙ eval-map Q (_ , swap-inj) α)))
  nu-step (.τ , Q) | τ = cong η (StepPath refl refl ((later-ext \ α → ih α (ν ((Q α))) ∙ cong νProc (eval-lift-id Q α))))
  nu-step (a , Q) | nope x = refl

  nu-stepF : ∀ {n} P
    → eval-fun (next (fix eval-fun)) n (ν P) ≡ Fold (SL'.stepνF (Unfold (eval (suc n) P)))
  nu-stepF P =
    cong Fold (map-bind (step P) _ _
              ∙ cong (bind (step P)) (funExt \ v → nu-step v))
    ∙ cong Fold (sym (bind-map (step P) _ _))
    ∙ sym (cong Fold (cong SL'.stepνF (cong Unfold (fix-eq eval-fun <* _ <* P))))

  synch'-step : ∀ {n} ap bq
    → mapF' {n = n} (\ α m i x → eval m x) (SL.Synch'.synch' (λ _ → _∣∣_) (λ _ → ν) ap bq)
        ≡ SL'.Synch'.synch' (\ _ → parProc) (λ _ → νProc)
                            (mapStep (\ m i x α → eval _ (x α)) ap)
                            (mapStep (\ m i x α → eval _ (x α)) bq)
  synch'-step (a , p) (b , q) with canSynchL? a b
  synch'-step (.(out _ _) , p) (.(inp _ _) , q) | local r r' = cong η (StepPath refl refl (later-ext \ α → ih α (p α ∣∣ q α)
              ∙ cong₂ parProc (sym (ih α (p α))) (sym (ih α (q α)))))
  synch'-step (.(bout _) , p)  (.(binp _)   , q) | bound r = cong η (StepPath refl refl (later-ext \ α → ih α (ν (p α ∣∣ q α))
    ∙ cong νProc (cong₂ parProc (eval-lift-id p α) (eval-lift-id q α))))
  synch'-step (a , p) (b , q) | nope = refl

  synch'-flip-step : ∀ {n} ap bq
    → mapF' {n = n} (\ α m i x → eval m x) (SL.Synch'.synch' (λ α p q → q ∣∣ p) (λ _ → ν) ap bq)
        ≡ SL'.Synch'.synch' (\ _ p q → parProc q p) (λ _ → νProc)
                            (mapStep (\ m i x α → eval _ (x α)) ap)
                            (mapStep (\ m i x α → eval _ (x α)) bq)
  synch'-flip-step (a , p) (b , q) with canSynchL? a b
  synch'-flip-step (.(out _ _) , q) (.(inp _ _) , p) | local r r' = cong η (StepPath refl refl (later-ext \ α → ih α (p α ∣∣ q α)
              ∙ cong₂ parProc (sym (ih α (p α))) (sym (ih α (q α)))))
  synch'-flip-step (.(bout _) , q)  (.(binp _)   , p) | bound r = cong η (StepPath refl refl (later-ext \ α → ih α (ν (p α ∣∣ q α))
    ∙ cong νProc (cong₂ parProc (eval-lift-id p α) (eval-lift-id q α))))
  synch'-flip-step (a , p) (b , q) | nope = refl

  synchF-step : ∀ {n} P Q
    → mapF' {n = n} (\ α m i x → eval m x) (SL.synchF (step P) (step Q))
        ≡ SL'.synchF (Unfold (eval n P)) (Unfold (eval n Q))
  synchF-step P Q = 
    map-bind (step P) _ _ ∙ cong (bind (step P)) (funExt \ v → map-bind (step Q) _ _ ) ∙
                     (cong (bind (step P)) (funExt \ ap → cong (bind (step Q)) (funExt \ bq →
                                                               cong₂ _∪_ (synch'-step ap bq)
                                                                         (synch'-flip-step bq ap) )) 
                                                             ∙ sym (bind-map (step P) _ _ ∙ cong (bind (step P)) (funExt \ _ → bind-map (step Q) _ _)))
                                                             ∙ sym (cong₂ SL'.synchF
                                                               (cong Proc.Unfold (fix-eq eval-fun <* _ <* P)) (cong Proc.Unfold (fix-eq eval-fun <* _ <* Q)))

  stepL'-step-g : ∀ {n} P Q
    → mapF' {n = n} (λ α m i x → eval m x) (SL.stepL' P Q)
        ≡ SL'.stepL' (mapF' {n = n} (λ α m i x → eval m x) P) (\ α → eval n (Q α))
  stepL'-step-g P Q = (mapmapP∞ _ _ P ∙ (cong mapP∞ (funExt \ { (a , p) → StepPath refl refl (later-ext \ α → ih α (p α ∣∣ mapPi _ (Q α))
                ∙ cong₂ parProc (sym (ih α (p α))) (eval-map Q (labelInj a) α)) }) <* P)
    ∙ sym (mapmapP∞ _ _ P))

  stepL'-step : ∀ {n} P Q
    → mapF' {n = n} (λ α m i x → eval m x) (SL.stepL' (step P) Q)
        ≡ SL'.stepL' (Unfold (eval n P)) (\ α → eval n (Q α))
  stepL'-step P Q = stepL'-step-g (step P) Q ∙ (congS SL'.stepL' (sym (cong Unfold (fix-eq eval-fun <* _ <* P))) <* λ α → eval _ (Q α))

  nu-par : ∀ {n} P Q 
    → eval-fun (next (fix eval-fun)) n (P ∣∣ Q)
        ≡ Fold (SL'.par (eval n P) (Unfold (eval n P)) (eval n Q) (Unfold (eval n Q)))
  nu-par P Q = cong Fold (cong₂ _∪_ (cong₂ _∪_
    (stepL'-step P (next Q))
    ((mapmapP∞ _ _ (step Q) ∙ cong (\ f → mapP∞ f (step Q)) (funExt \ bq → StepPath refl refl (later-ext \ α → ih α (mapPi _ P ∣∣ bq .theX α)
      ∙ cong₂ parProc (eval-map (next P) (labelInj (bq .theLabel)) α) (sym (ih α (bq .theX α))))))
    ∙ sym (cong (SL'.stepR (eval _ P)) (cong Unfold (fix-eq eval-fun <* _ <* Q)) ∙ mapmapP∞ _ _ (step Q))))
         (synchF-step P Q))

  evalGM-eq' : ∀ {n} (P : Pi n) → eval _ P ≡ evalGM P .elem _ (\ x → x)
  evalGM-eq' end = refl 
  evalGM-eq' {n} (P ⊕ P₁) =
    ((fix-eq eval-fun <* n) <* (P ⊕ P₁))
    ∙ cong Fold (cong₂ _∪_
                       (sym (cong Unfold (fix-eq eval-fun <* n <* P)))
                       (sym (cong Unfold (fix-eq eval-fun <* n <* P₁))))
    ∙ sym (cong isPi-alg.sumX (fix-eq ProcPi-algF <* _) <* _ <* _)
    ∙ cong₂ sumProc (evalGM-eq' P) (evalGM-eq' P₁)
  evalGM-eq' {n} (P ∣∣ Q) =
    (fix-eq eval-fun <* n <* (P ∣∣ Q))
    ∙ nu-par P Q
    ∙ sym (cong isPi-alg.parX (fix-eq ProcPi-algF <* _) <* _ <* (eval n Q))
    ∙ cong₂ parProc (evalGM-eq' P) (evalGM-eq' Q)
  evalGM-eq' {n} (ν P) =
    (fix-eq eval-fun <* n <* (ν P))
    ∙ nu-stepF P
    ∙ sym (cong isPi-alg.νX (fix-eq ProcPi-algF <* _) <* (eval (suc n) P))
    ∙ cong (isPi-alg.νX (ProcPi-alg _)) (evalGM-eq' P ∙ cong (evalX PiMod-alg P .elem _) (sym (funExt lift-id)))
  evalGM-eq' {n} (guard x y P) =
    (fix-eq eval-fun  <* n <* (guard x y P))
    ∙ guard-step x y P
    ∙ sym (cong isPi-alg.guardX (fix-eq ProcPi-algF <* _) <* _ <* _ <* eval n P)
    ∙ cong (guardProc _ _) (evalGM-eq' P)
  evalGM-eq' {n} (! P) =
    (fix-eq eval-fun <* n <* (! P))
    ∙ cong Fold (cong₂ _∪_ (stepL'-step P _
                            ∙ congS (SL'.stepL' (Unfold (eval _ P)))
                                    (later-ext \ α → ih α (! P)
                                                      ∙ cong !Proc (sym (ih α P))
                                                      ∙ (cong isPi-alg.!X (fix-eq ProcPi-algF <* _) <* eval n P)))
                           (stepL'-step-g (SL.synchF (step P) (step P)) _
                           ∙ cong₂ SL'.stepL'
                                   (synchF-step P P)
                                   (later-ext \ α → ih α (! P)
                                                     ∙ cong !Proc (sym (ih α P))
                                                     ∙ (cong isPi-alg.!X (fix-eq ProcPi-algF <* _) <* eval n P)))
                ∙ sym (fix-eq (!F (next (fix ProcPi-algF)) (eval n P))))
    ∙ sym (cong isPi-alg.!X (fix-eq ProcPi-algF <* _) <* eval n P)
    ∙ cong (isPi-alg.!X (ProcPi-alg _)) (evalGM-eq' P)
  evalGM-eq' {n} (out ch x · P) =
    ((fix-eq eval-fun <* n) <* (out ch x · P))
    ∙ cong Fold (cong η (StepPath refl refl (cong next (evalGM-eq' P))))
  evalGM-eq' {n} (inp ch · P) =
    ((fix-eq eval-fun <* n) <* (inp ch · P))
    ∙ cong Fold (cong₂ _∪_ (map-bind enum _ _
                            ∙ cong (bind enum)
                                   (funExt \ v → cong η (StepPath refl refl (later-ext \ α → ih α (mapPi (for-fresh _) P)
                                                                                               ∙ ((cong elem (PiMod-model .map-evalX _ P) <* _) <* (\ x → x))
                                                                                               ∙ cong (evalX PiMod-alg P .elem _) (funExt (snoc-for-fresh _))))))
                            (cong η (StepPath refl refl (cong next ((evalGM-eq' P) ∙ cong (evalX PiMod-alg P .elem _) (sym (funExt lift-id)))))))
  evalGM-eq' {n} (τ · P) =
    ((fix-eq eval-fun <* n) <* (τ · P))
    ∙ cong Fold (cong η (StepPath refl refl (cong next (evalGM-eq' P))))

evalGM-eq : ∀ {n} (P : Pi n) {m} (ρ : Name n → Name m)
  → Eval.eval _ (mapPi ρ P) ≡ evalGM P .elem _ ρ
evalGM-eq P ρ =
  fix evalGM-eq' (mapPi ρ P)
  ∙ ((cong elem (PiMod-model .map-evalX ρ P) <* _) <* (\ x → x))

-- Structurally-congruent terms have the same evaluation.
eval-≈ : ∀ {n} {P Q : Pi n} → P ≈ Q → Eval'.eval _ P ≡ Eval'.eval _ Q
eval-≈ {n}{P}{Q} c =
  sym (Eval'.eval-eq' P)
  ∙ congS (Eval.eval n) (sym (mapPi-id P))
  ∙ evalGM-eq P (λ x → x)
  ∙ (cong elem (evalX≈ PiMod-model c) <* _ <* (\ x → x))
  ∙ sym (evalGM-eq Q (λ x → x))
  ∙ congS (Eval.eval n) (mapPi-id Q)
  ∙ Eval'.eval-eq' Q

