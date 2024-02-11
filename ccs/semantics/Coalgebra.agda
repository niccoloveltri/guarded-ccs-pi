{-# OPTIONS --cubical --guarded -WnoUnsupportedIndexedMatch #-}

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

module ccs.semantics.Coalgebra (ns : Names) where

open Names ns
open OpNames ns
open import Cubical.Data.Sigma
open import ccs.Syntax ns
open import ccs.Algebra ns
open import ccs.semantics.Algebra ns
open import ccs.semantics.Dynamics ns
open import ccs.semantics.StructuralCongruence ns
open import ccs.semantics.Model ns

-- F'-coalgebra structure on CCS, the functional variant of the
-- operational semantics.
module CoalgebraCCS where

  open StepLemmata CCS (λ _ n → InitCCS-alg n) mapCCS

  step : ∀ {n} → CCS n → F' n (\ _ → CCS)
  step end      = ø
  step (a · p) = η (a , (λ _ → p))
  step (p ⊕ q)  = step p ∪ step q
  step (p ∣∣ q) = par p (step p) q (step q)
  step (ν p)    = stepνF (step p)
  step (! p)    = stepL' (step p ∪ synchF (step p) (step p)) (\ _ → ! p)

-- F-coalgebra structure on CCS
module CoalgebraCCS' where

  module SLCCS = StepLemmataCCS
  open SLCCS

  step : ∀ {n} → CCS n → F n CCS
  step end      = ø
  step (a · p) = η (a , p)
  step (p ⊕ q)  = step p ∪ step q
  step (p ∣∣ q) = par p (step p) q (step q)
  step (ν p)    = stepνF (step p)
  step (! p)    = stepL (step p ∪ synchF (step p) (step p)) (! p)

  module O = CoalgebraCCS
  module SL = StepLemmata CCS (λ _ n → InitCCS-alg n) mapCCS


-- The releationship between the F-coalgebra and the F'-coalgebra on
-- CCS.
  stepν-eq : ∀ {n} (v : Step CCS (suc n))
    → SL.stepν (v .theLabel , next (v .theX))
          ≡ mapP∞ (λ x → x .theLabel , next (x .theX)) (stepν v)
  stepν-eq (a , Q) with canNu? a
  stepν-eq (.(out _) , Q) | out x = refl
  stepν-eq (.(inp _) , Q) | inp x = refl
  stepν-eq (.τ , Q) | τ = refl
  stepν-eq (a , Q) | nope x = refl

  synch'-eq : ∀ {n} {x1 x2 : Step CCS n} (f : ∀ {n} → CCS n → CCS n → CCS n)
    → SL.Synch'.synch' (λ _ → f) (x1 .theLabel , next (x1 .theX)) (x2 .theLabel , next (x2 .theX))
                ≡ mapP∞ ((λ x → x .theLabel , next (x .theX))) (SLCCS.Synch'.synch' f x1 x2)
  synch'-eq {_} {(a , x1)} {(b , x2)} f with canSynchL? a b
  ... | local x = refl
  ... | nope = refl

  stepL-eq : ∀ {n} (v : F n CCS) (P : CCS n)
    → SL.stepL (mapP∞ (λ x → x .theLabel , next (x .theX)) v) P
              ≡ mapP∞ (λ x → x .theLabel , next (x .theX)) (stepL v P)
  stepL-eq v P = mapmapP∞ _ _ v ∙ sym (mapmapP∞ _ _ v)

  synchF-eq : ∀ {n} (v1 v2 : F n CCS)
    → SL.synchF (mapP∞ (λ x → x .theLabel , next (x .theX)) v1) (mapP∞ (λ x → x .theLabel , next (x .theX)) v2)
        ≡ mapP∞ (λ x → x .theLabel , next (x .theX)) (synchF v1 v2)
  synchF-eq v1 v2 = bind-map v1 _ _ ∙ cong (bind v1) (funExt \ v → bind-map v2 _ _)
                   ∙ cong (bind v1) (funExt \ x1 → cong (bind v2) (funExt \ x2 → cong₂ _∪_ (synch'-eq _) (synch'-eq _)))
                  ∙ sym (map-bind v1 _ _ ∙ cong (bind v1) (funExt (\ _ → map-bind v2 _ _)))

  step-eq : ∀ {n} (P : CCS n) → O.step P ≡ mapP∞ (λ x → x .theLabel , next (x .theX)) (step P)
  step-eq end = refl
  step-eq (a · P) = refl
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


-- The relationship between the coalgebra structure on CCS and the
-- operational semantics:
--  ∥ P [ a ]↦ P' ∥₁  ≃  ∃ Q Q'. P ≈ Q  ×  P' ≈ Q'  ×  ⟨ (a , Q') ∈ step Q ⟩
module _ where

  open StepLemmataCCS
  open StepLemmata2CCS
  open CoalgebraCCS'

  ∈stepν : ∀ {n} (a : Act n) P
     → ⟨ (a , ν P) ∈ stepν (mapAct ι a , P) ⟩
  ∈stepν (out x) P with canNu? (out (ι x))
  ∈stepν (out x) P | out r = ∣ (λ i → out (ι-inj _ _ r i) , ν P) ∣₁
  ∈stepν (out x) P | nope (out r) = ⊥-rec (fresh-ι r)
  ∈stepν (inp x) P with canNu? (inp (ι x))
  ∈stepν (inp x) P | inp r = ∣ (λ i → inp (ι-inj _ _ r i) , ν P) ∣₁ 
  ∈stepν (inp x) P | nope (inp r) = ⊥-rec (fresh-ι r)
  ∈stepν τ P = ∣ refl ∣₁

  ν-opsem : ∀ {n} (a' : Act (suc n)) {aQ : Step CCS n} {P}
    → ⟨ aQ ∈ stepν (a' , P) ⟩
    → ∥ Σ (Act n) (λ a'' → (a' ≡ mapAct ι a'') × (aQ ≡ (a'' , ν P))) ∥₁
  ν-opsem (out x) m with canNu? (out x)
  ... | out {a = a} r = PT.map (λ eq → out a , cong out r , eq) m
  ν-opsem (inp x) m with canNu? (inp x)
  ... | inp {a = a} r = PT.map (λ eq → inp a , cong inp r , eq) m 
  ν-opsem τ m = PT.map (λ eq → _ , refl , eq) m

  _≈∈≈step_ : ∀ {n} → Step CCS n → CCS n → Set
  (a , Q) ≈∈≈step P = ∥ Σ _ (λ P' → Σ _ (λ Q' → P ≈ P' × Q ≈ Q' × ⟨ (a , Q') ∈ step P' ⟩)) ∥₁

  opsem→∈step : ∀ {n} (P : CCS n) a (P' : CCS n)
    → P [ a ]↦ P' → (a , P') ≈∈≈step P
  opsem→∈step ._ ._ P' (act a) =  ∣ _ , _ , refl≈ , refl≈ , ∣ refl ∣₁ ∣₁
  opsem→∈step .(_ ⊕ _) a P' (sumtr t) = (opsem→∈step _ _ _ t) >>PT \ { (Q , Q' , Qc , Q'c , m) →
              ∣ _ , _ , cong⊕ Qc refl≈ , Q'c , inl m ∣₁ } 
  opsem→∈step (P ∣∣ P2) a .(_ ∣∣ _) (partr t) = opsem→∈step _ _ _ t >>PT \ where
    (Q , _ , Qc , Q'c , m) →  ∣ (_ , _ , cong∣∣ Qc refl≈ , cong∣∣ Q'c refl≈  ,  inl (inl (mapP∞-in _ _ (step Q) m)) ) ∣₁
  opsem→∈step (P ∣∣ P2) .τ (P' ∣∣ Q') (com {a = a} t t₁) = opsem→∈step _ _ _ t >>PT \ where
    (Q , R , Qc , Q'c , m) → opsem→∈step _ _ _ t₁ >>PT \ where
     (Q1 , R1 , Qc1 , Q'c1 , m1) →
      ∣ (_ , _ , cong∣∣ Qc Qc1  , cong∣∣ Q'c Q'c1 ,
      inr (0 , bind-in _ _ (step Q)
      (_ , m , bind-in _ _ (step Q1)
      (_ , m1 , inl (synch'-in-s _∣∣_ ∣ (_ , _ , _ , refl , refl , refl) ∣₁))))) ∣₁
  opsem→∈step (ν P) a ._ (res t) = opsem→∈step _ _ _ t >>PT \ where
    (Q , _ , Qc , Q'c , m) → ∣ _  , _ , congν Qc , congν Q'c , bind-in stepν _ (step Q) (_ , m , ∈stepν a _) ∣₁
  opsem→∈step P a P' (conv t x x₁) = opsem→∈step _ _ _ t >>PT \ { (Q , Q' , Qc , Q'c , m ) → ∣ Q , _ , (sym≈ x ∙≈ Qc) , (sym≈ x₁ ∙≈ Q'c) , m ∣₁ }

  ∈step→opsem : ∀ {n} (P : CCS n) a (P' : CCS n)
    → ⟨ (a , P') ∈ step P ⟩ → ∥ P [ a ]↦ P' ∥₁
  ∈step→opsem (a' · P) a P' mem =
    PT.map (λ eq → subst2 (λ x y → (x · y) [ a ]↦ P') (λ i → eq i .theLabel) (λ i → eq i .theX) (act a)) mem
  ∈step→opsem (P₁ ⊕ P₂) a Q mem =
    mem >>PT λ { (_⊎_.inl aP'∈P₁) → PT.map (λ { (tr) → sumtr tr }) (∈step→opsem P₁ a Q aP'∈P₁)
              ; (_⊎_.inr aP'∈P₂) → PT.map (λ { (tr) → conv (sumtr tr) comm⊕ refl≈}) (∈step→opsem P₂ a Q (aP'∈P₂ .snd)) }
  ∈step→opsem (P₁ ∣∣ P₂) a Q mem =
   mem >>PT λ { (_⊎_.inl x) → x >>PT λ {
                           (_⊎_.inl aP'∈stepL) → mapP∞-out _ (a , Q) (step P₁) aP'∈stepL >>PT
                           λ { ((_ , Q') , aQ'∈ , r) → 
                             subst2 (λ x y → ∥ P₁ ∣∣ P₂ [ x ]↦ y ∥₁)
                                    (cong theLabel (sym r))
                                    (cong theX (sym r))
                                    (PT.map partr (∈step→opsem P₁ _ Q' aQ'∈)) } 
                        ; (_⊎_.inr aP'∈stepR) → mapP∞-out _ (a , Q) (step P₂) (aP'∈stepR .snd) >>PT
                        λ { ((_ , Q') ,  aQ'∈ , r) →
                             subst2 (λ x y → ∥ P₁ ∣∣ P₂ [ x ]↦ y ∥₁)
                                    (cong theLabel (sym r))
                                    (cong theX (sym r))
                                    (PT.map (λ tr → conv (partr tr) comm∣∣ comm∣∣) (∈step→opsem P₂ _ Q' aQ'∈)) }}
               ; (_⊎_.inr (_ , aP'∈synchF)) → bind-out (λ sp → bind (step P₂) (synch sp)) _ (step P₁) aP'∈synchF >>PT
                          λ { (aQ' , aQ'∈ , aQ∈) → bind-out (synch aQ') _  (step P₂) aQ∈ >>PT
                          λ { (aR , aR∈ , x) → x >>PT
                            λ { (_⊎_.inl x) → synch'-out' (_∣∣_) {P1 = aQ'}{aR} (x) >>PT
                              λ { (synch'-s P1' P2' p q r) → 
                                subst2 (λ x y → ∥ P₁ ∣∣ P₂ [ x ]↦ y ∥₁)
                                       (cong theLabel (sym r))
                                       (cong theX (sym r))
                                       (subst2 (λ x y → ∥ P₁ [ x ]↦ y ∥₁) (cong theLabel p) (cong theX p) (∈step→opsem P₁ _ _ aQ'∈) >>PT
                                         λ tr1 →
                                           PT.map (com tr1)
                                                 (subst2 (λ x y → ∥ P₂ [ x ]↦ y ∥₁) (cong theLabel q) (cong theX q) (∈step→opsem P₂ _ _ aR∈))) }
                            ; (_⊎_.inr x) → synch'-out' ((λ p q → q ∣∣ p)) {P1 = aR}{aQ'} ((x .snd)) >>PT
                              λ { (synch'-s P1' P2' p q r) → 
                                subst2 (λ x y → ∥ P₁ ∣∣ P₂ [ x ]↦ y ∥₁)
                                       (cong theLabel (sym r))
                                       (cong theX (sym r))
                                       (subst2 (λ x y → ∥ P₁ [ x ]↦ y ∥₁) (cong theLabel q) (cong theX q) (∈step→opsem P₁ _ _ aQ'∈) >>PT
                                         λ tr1 →
                                         PT.map (λ tr2 → conv (com tr2 tr1) comm∣∣ comm∣∣)
                                                (subst2 (λ x y → ∥ P₂ [ x ]↦ y ∥₁) (cong theLabel p) (cong theX p) (∈step→opsem P₂ _ _ aR∈))) }}}}}
  ∈step→opsem (ν P) a Q mem = bind-out stepν _ (step P) mem >>PT
     λ { ((a' , Q') , aQ'∈ , aQ∈) → ∈step→opsem P _ _ aQ'∈ >>PT  λ { tr →
       PT.map (λ { (a'' , q , r) → subst2 (λ x y → ν P [ x ]↦ y)
                                           (cong theLabel (sym r))
                                           (cong theX (sym r))
                                           (res (subst (λ x → P [ x ]↦ Q') q tr)) } )
              (ν-opsem a' aQ∈) } }
  ∈step→opsem (! P) a Q mem = mem >>PT
   λ { (_⊎_.inl x) → mapP∞-out _ _ (step P) x >>PT
       λ { ((_ , Q') , aQ'∈ , r) → subst2 (λ x y → ∥ ! P [ x ]↦ y ∥₁)
                                          (cong theLabel (sym r))
                                          (cong theX (sym r))
                                          (PT.map (λ tr → conv (partr tr) (sym≈ repl) refl≈) (∈step→opsem P _ Q' aQ'∈)) }
   ; (_⊎_.inr x) → mapP∞-out _ _ (synchF (step P) (step P)) (x .snd) >>PT
     λ { ((_ , Q') , aQ'∈ , r') → synchF-out' (step P) (step P) (aQ'∈) >>PT
       λ { (con {P' = P'} {Q''} P'∈ Q''∈ aQ'∈) → aQ'∈ >>PT
         λ { (_⊎_.inl x) → synch'-out' (_∣∣_) {P1 = P'}{Q''} (x) >>PT
           λ { (synch'-s P1' P2' p q r) →
             subst2 (λ x y → ∥ P [ x ]↦ y ∥₁) (cong theLabel p) (cong theX p) (∈step→opsem P _ _ P'∈) >>PT
                  λ tr1 → PT.map (λ tr2 → subst2 (λ x y → ! P [ x ]↦ y) (cong theLabel (sym r')) (cong theX (sym r'))
                                   (subst2 (λ x y → ! P [ x ]↦ (y ∣∣ (! P))) (cong theLabel (sym r)) (cong theX (sym r))
                                     (conv (partr (com tr1 tr2)) ((assoc∣∣ ∙≈ cong∣∣ refl≈ (sym≈ repl)) ∙≈ sym≈ repl) refl≈)))
                                 (subst2 (λ x y → ∥ P [ x ]↦ y ∥₁) (cong theLabel q) (cong theX q) (∈step→opsem P _ _ Q''∈)) } 
         ; (_⊎_.inr x) → synch'-out' ((λ p q → q ∣∣ p)) {P1 = Q''}{P'} ((x .snd)) >>PT
           λ { (synch'-s P1' P2' p q r) →
             subst2 (λ x y → ∥ ! P [ x ]↦ y ∥₁) (cong theLabel (sym r')) (cong theX (sym r'))
                    (subst2 (λ x y → ∥ P [ x ]↦ y ∥₁) (cong theLabel q) (cong theX q) (∈step→opsem P _ _ P'∈) >>PT
                      λ tr1 → PT.map (λ tr2 →
                                         subst2 (λ x y → ! P [ x ]↦ (y ∣∣ (! P)))
                                                (cong theLabel (sym r))
                                                (cong theX (sym r))
                                                (conv (partr (com tr2 tr1)) ((assoc∣∣ ∙≈ cong∣∣ refl≈ (sym≈ repl)) ∙≈ sym≈ repl) (cong∣∣ comm∣∣ refl≈)))
                                      (subst2 (λ x y → ∥ P [ x ]↦ y ∥₁) (cong theLabel p) (cong theX p) (∈step→opsem P _ _ Q''∈))) }}}}} 


  opsem-eq' : ∀ {n} (P : CCS n) (a : Act n) (P' : CCS n)
    → _≡_ {A = hProp₀} (∥ P [ a ]↦ P' ∥₁ , isPropPropTrunc) ((a , P') ≈∈≈step P , isPropPropTrunc)
  opsem-eq' P a P' =
    ⇔toPath (PT.rec isPropPropTrunc (opsem→∈step P a P'))
             (PT.rec isPropPropTrunc
                     (λ { (Q , Q' , eq , eq' , m) →
                       ∈step→opsem Q a Q' m >>PT λ m' → ∣ conv m' (sym≈ eq) (sym≈ eq') ∣₁}))

  opsem-eq : ∀ {n} (P : CCS n) a (P' : CCS n)
    → ∥ P [ a ]↦ P' ∥₁ ≡ (a , P') ≈∈≈step P
  opsem-eq P a P' = cong fst (opsem-eq' P a P')

-- stepRel and piRel are two variants of the operational semantics
-- relations where the new processes P' is of the form "next Q".
-- They are equivalent relations.
  stepRel : ∀ {n} (P : CCS n) a (P' : ▹ (CCS n)) → Set
  stepRel P a P' =
    ∥ (Σ _ \ Q → Σ _ \ Q1 → Σ _ \ Q2
      → P ≈ Q × (P' ≡ next Q1) × (Q1 ≈ Q2) × ⟨ (a , Q2) ∈ step Q ⟩) ∥₁

  stepRel' : ∀ {n} (P : CCS n) a (P' : ▹ (CCS n)) → Set
  stepRel' P a P' = Σ _ \ Q' → (next Q' ≡ P') × ⟨ (a , Q') ∈ step P ⟩

  piRel : ∀ {n} (P : CCS n) a (P' : ▹ (CCS n)) → Set
  piRel P a P' = ∥ Σ (CCS _) (λ Q' → (P' ≡ next Q') × P [ a ]↦ Q') ∥₁

  ∈step→opsem2 : ∀ {n} (P : CCS n) a P' → stepRel {n} P a P' → piRel P a P'
  ∈step→opsem2 P a P' x =
    x >>PT \ { (Q , Q1 , Q2 , Qc , refl' , Q'c , m) → ∈step→opsem Q _ _ m >>PT \ tr → ∣ Q1 , (refl' , (conv tr (sym≈ Qc) (sym≈ Q'c))) ∣₁  }

  opsem→∈step2 : ∀ {n} (P : CCS n) a (P' : ▹ (CCS n)) → piRel P a P' → stepRel P a P'
  opsem→∈step2 P a P' =
    PT.rec squash₁
      (\ { (Q' , refl' , tr) →
          opsem→∈step _ _ _ tr >>PT \ { (Q , Q'' , Qc , Q''c , m) → ∣ Q , Q' , Q'' , Qc , refl' , Q''c , m ∣₁ }})

-- Since Proc n is a CCS-algebra, there is a map evalG : CCS n → Proc n given by the initiality of CCS.
evalG = evalX ProcCCS-alg 

-- But we know that CCS n is a F-coalgebra, so there exist an
-- evaluation typed CCS n → Proc n defined by guarded recursion (and
-- similarly an evaluation with the same type coming from the
-- F'-coalgebra structure of CCS).  below). But Proc
module Eval where

  open CoalgebraCCS

  eval-fun : ▹ (∀ n → CCS n → Proc n) → ∀ n → CCS n → Proc n
  eval-fun r n p = Fold (mapP∞ (λ x → (x .theLabel , λ α → r α n (x .theX α))) (step p))

  eval : ∀ n → CCS n → Proc n
  eval = fix eval-fun

module Eval' where

  open CoalgebraCCS'
  eval-fun : ▹ (∀ n → CCS n → Proc n) → ∀ n → CCS n → Proc n
  eval-fun r n p = Fold (mapP∞ (λ x → (x .theLabel , λ α → r α n (x .theX))) (step p))

  eval : ∀ n → CCS n → Proc n
  eval = fix eval-fun

-- The two inductively-defined evaluation maps are equal.
  eval-eq' : ∀ {n} (P : CCS n) → Eval.eval _ P ≡ eval _ P
  eval-eq' {n} P =
    cong fix (funExt \ r → funExt \ n → funExt \ p →
      cong (Fold {n}) (cong (mapP∞ (λ x → x .theLabel , λ α → r α n (x .theX α))) (step-eq p)
                      ∙ mapmapP∞ _ _ (step p)))
           <* n <* P

-- The inductively-defined evaluation map (arising from the
-- CCS-algebra structure on Proc) is equivalent to the
-- guarded-recursive one (arising from the F-coalgebra structure on
-- CCS). This is proved by guarded recursion.
module _ (ih : ▹ ∀ {n} (P : CCS n) → Eval.eval _ P ≡  evalG P) where

  open Eval

  open CoalgebraCCS
  module SL = StepLemmata CCS (λ _ → InitCCS-alg) mapCCS
  module SL' = StepLemmata Proc (λ _ → ProcCCS-alg) (mapProc _ _)

  eval-lift-id : ∀ {n} (q : ▹ CCS (suc n)) → (@tick α : Tick) → evalG (q α) ≡ eval _ (q α)
  eval-lift-id q α = sym (ih α (q α)) --sym (ih α (q α) ∙ cong (evalX CCSMod-alg (q α) .elem _) (sym (funExt liftS-id)))

  nu-step : ∀ {n} v
          → mapP∞ (λ x → x .theLabel , λ α → eval n (x .theX α)) (SL.stepν v)
           ≡ SL'.stepν (v .theLabel , λ α → eval _ (v .theX α))
  nu-step (a , Q) with canNu? a
  nu-step (.(out _) , Q) | out x = cong η (StepPath refl (later-ext (λ α → ih α (ν (Q α)) ∙ cong νProc (eval-lift-id Q α))))
  nu-step (.(inp _) , Q) | inp x = cong η (StepPath refl (later-ext (λ α → ih α (ν (Q α)) ∙ cong νProc (eval-lift-id Q α))))
  nu-step (.τ , Q) | τ = cong η (StepPath refl (later-ext (λ α → ih α (ν (Q α)) ∙ cong νProc (eval-lift-id Q α))))
  nu-step (a , Q) | nope x = refl

  nu-stepF : ∀ {n} P → eval-fun (next (fix eval-fun)) n (ν P) ≡ Fold (SL'.stepνF (Unfold (eval (suc n) P)))
  nu-stepF P = (cong Fold (map-bind (step P) _ _  ∙ cong (bind (step P)) (funExt \ v → nu-step v))
             ∙ cong Fold (sym (bind-map (step P) _ _))) ∙ sym (cong Fold (cong SL'.stepνF (cong Proc.Unfold (fix-eq eval-fun <* _ <* P))))

  synch'-step : ∀ {n} ap bq →
               mapP∞ (λ x → x .theLabel , λ α → eval n (x .theX α)) (SL.Synch'.synch' (λ α → _∣∣_) ap bq)
               ≡ SL'.Synch'.synch' (\ _ → parProc) (ap .theLabel , λ α → eval _ (ap .theX α)) (bq .theLabel , λ α → eval _ (bq .theX α))
  synch'-step (a , p) (b , q) with canSynchL? a b
  synch'-step (.(out _) , p) (.(inp _) , q) | local refl' = cong η (StepPath refl (later-ext \ α → ih α (p α ∣∣ q α)
              ∙ cong₂ parProc (sym (ih α (p α))) (sym (ih α (q α)))))
  synch'-step (a , p) (b , q) | nope = refl

  synch'-flip-step : ∀ {n} ap bq →
            mapP∞ (λ x → x .theLabel , λ α → eval n (x .theX α)) (SL.Synch'.synch' (λ α p q → q ∣∣ p) ap bq)
             ≡ SL'.Synch'.synch' (\ _ x y → parProc y x) (ap .theLabel , λ α → eval _ (ap .theX α)) (bq .theLabel , λ α → eval _ (bq .theX α))
  synch'-flip-step (a , p) (b , q) with canSynchL? a b
  synch'-flip-step (.(out _) , q) (.(inp _) , p) | local _ =
    cong η (StepPath refl (later-ext \ α → ih α (p α ∣∣ q α) ∙ cong₂ parProc (sym (ih α (p α))) (sym (ih α (q α)))))
  synch'-flip-step (a , p) (b , q) | nope = refl

  synchF-step : ∀ {n} P Q → mapP∞ (λ x → x .theLabel , λ α → eval n (x .theX α)) (SL.synchF (step P) (step Q)) ≡
                SL'.synchF (Unfold (eval n P)) (Unfold (eval n Q))
  synchF-step P Q = 
    map-bind (step P) _ _ ∙ cong (bind (step P)) (funExt \ v → map-bind (step Q) _ _ ) ∙
                     (cong (bind (step P)) (funExt \ ap → cong (bind (step Q)) (funExt \ bq →
                                                               cong₂ _∪_ (synch'-step ap bq)
                                                                         (synch'-flip-step bq ap) )) 
                                                             ∙ sym (bind-map (step P) _ _ ∙ cong (bind (step P)) (funExt \ _ → bind-map (step Q) _ _)))
                                                             ∙ sym (cong₂ SL'.synchF
                                                               (cong Proc.Unfold (fix-eq eval-fun <* _ <* P)) (cong Proc.Unfold (fix-eq eval-fun <* _ <* Q)))

  stepL'-step-g : ∀ {n} P Q →
     mapP∞ (λ x → x .theLabel , λ α → eval n (x .theX α)) (SL.stepL' P Q)
     ≡
     SL'.stepL' (mapP∞ (λ x → x .theLabel , λ α → eval n (x .theX α)) P) (\ α → eval n (Q α))
  stepL'-step-g P Q = mapmapP∞ _ _ P ∙
                (cong mapP∞ (funExt \ { (a , p) → StepPath refl (later-ext (λ α → ih α (p α ∣∣ Q α) ∙ cong₂ parProc (sym (ih α (p α))) (sym (ih α (Q α)))))}) <* P) ∙
                sym (mapmapP∞ _ _ P)

  stepL'-step : ∀ {n} P Q →
     mapP∞ (λ x → x .theLabel , λ α → eval n (x .theX α)) (SL.stepL' (step P) Q) 
     ≡
     SL'.stepL' (Unfold (eval n P)) (\ α → eval n (Q α))
  stepL'-step {n} P Q = stepL'-step-g (step P) Q ∙ (congS SL'.stepL' (sym (cong Unfold (fix-eq eval-fun <* n <* P))) <* (λ α → eval n (Q α)))

  nu-par : ∀ {n} P Q → eval-fun (next (fix eval-fun)) n (P ∣∣ Q) ≡ Fold (SL'.par (eval n P) (Unfold (eval n P))
                                                                                                                              (eval n Q) (Unfold (eval n Q)))
  nu-par P Q = cong Fold (cong₂ _∪_ (cong₂ _∪_
    (stepL'-step P (next Q))
    ((mapmapP∞ _ _ (step Q) ∙ cong (\ f → mapP∞ f (step Q)) (funExt \ bq → StepPath refl (later-ext \ α → ih α (P ∣∣ bq .theX α)
      ∙ cong₂ parProc (sym (ih α P)) (sym (ih α (bq .theX α))))))
      ∙ sym (cong (SL'.stepR (eval _ P)) (cong Proc.Unfold (fix-eq eval-fun <* _ <* Q)) ∙ mapmapP∞ _ _ (step Q))))
         (synchF-step P Q))

  evalG-eq' : ∀ {n} (P : CCS n) → eval n P ≡ evalG P 
  evalG-eq' end = refl
  evalG-eq' {n} (a · P) =
    ((fix-eq eval-fun <* n) <* (a · P)) 
     ∙ sym (cong isCCS-alg.actX (fix-eq ProcCCS-algF <* _) <* _ <* _) ∙ congS (isCCS-alg.actX (ProcCCS-alg _) a) (evalG-eq' P) 
  evalG-eq' {n} (P ⊕ P₁) = 
    ((fix-eq eval-fun <* n) <* (P ⊕ P₁)) ∙ cong Fold (cong₂ _∪_
                 (sym ((cong Proc.Unfold (fix-eq eval-fun <* n <* P)) ∙ refl))
                (sym ((cong Proc.Unfold (fix-eq eval-fun <* n <* P₁)) ∙ refl)))
              ∙ sym (cong isCCS-alg.sumX (fix-eq ProcCCS-algF <* _) <* _ <* _) ∙ cong₂ (isCCS-alg.sumX (ProcCCS-alg _)) (evalG-eq' P) (evalG-eq' P₁)
  evalG-eq' {n} (P ∣∣ Q) = 
    (fix-eq eval-fun <* n <* (P ∣∣ Q))
    ∙ nu-par P Q
    ∙ sym (cong isCCS-alg.parX (fix-eq ProcCCS-algF <* _) <* _ <* (eval n Q))
    ∙ cong₂ (isCCS-alg.parX (ProcCCS-alg n)) (evalG-eq' P) (evalG-eq' Q)
  evalG-eq' {n} (ν P) = 
    (fix-eq eval-fun <* n <* ν P)
    ∙ nu-stepF P
    ∙ sym (cong isCCS-alg.νX (fix-eq ProcCCS-algF <* _) <* (eval (suc n) P))
    ∙ congS (isCCS-alg.νX (ProcCCS-alg _)) (evalG-eq' P)
  evalG-eq' {n} (! P) = 
    ((fix-eq eval-fun <* n <* (! P)) ∙ cong Fold (cong₂ _∪_ (stepL'-step P _ ∙ congS (SL'.stepL' (Unfold (eval _ P)))
             (later-ext \ α → ih α (! P) ∙ cong !Proc (sym (ih α P)) ∙ (cong isCCS-alg.!X (fix-eq ProcCCS-algF <* _) <* eval n P)))
             (stepL'-step-g (SL.synchF (step P) (step P)) _ 
               ∙ cong₂ SL'.stepL' (synchF-step P P)
                       (later-ext \ α → ih α (! P) ∙ cong !Proc (sym (ih α P)) ∙ (cong isCCS-alg.!X (fix-eq ProcCCS-algF <* _) <* eval n P)))
               ∙ sym (fix-eq (!F (next (fix ProcCCS-algF)) (eval n P))))
               ∙ sym (cong isCCS-alg.!X (fix-eq ProcCCS-algF <* _) <* eval n P)) ∙ (cong (isCCS-alg.!X (ProcCCS-alg _)) (evalG-eq' P))


evalG-eq : ∀ {n} (P : CCS n) → Eval.eval _ P ≡ evalG P
evalG-eq P = fix evalG-eq' P

-- Structurally-congruent terms have the same evaluation.
eval-≈ : ∀ {n} {P Q : CCS n} → P ≈ Q → Eval'.eval _ P ≡ Eval'.eval _ Q
eval-≈ {P = P}{Q} c =
  sym (Eval'.eval-eq' P)
  ∙ evalG-eq P
  ∙ isCCS-model.evalX≈ ProcModel c
  ∙ sym (evalG-eq Q)
  ∙ Eval'.eval-eq' Q

