{-# OPTIONS --cubical --guarded #-}

open import Cubical.Data.Sum hiding (inl; inr) 
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (lift)
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.Relation.Nullary
open import CountablePowerSet
open import Basic
open import AbsNames
open import LaterPrims hiding (_∙_)

module ccs.semantics.StructuralCongruence (ns : Names) where

open Names ns
open OpNames ns
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import ccs.Syntax ns
open import ccs.Algebra ns
open import ccs.semantics.Algebra ns
open import ccs.semantics.MapProcLemmata ns

open StepLemmata Proc (\ α n → ProcCCS-alg n) (mapProc _ _)
open Synch'

-- Path equality on Proc appropriately models structural congruence on
-- CCS-terms. In other words, we can show that equality is a
-- "StructCong" for the CCS-algebra of processes. This is proved by
-- guarded recursion.

module _ (ih : ▹ StructCong ProcCCS-alg (mapProc-Inj _ _) _≡_) where
  open StructCong

-- Unitality, commutativity and associativity of sumProc.
  unit-sum : ∀ {m P} → sumProc {m} P endProc ≡ P
  unit-sum = cong Fold (unit _)

  comm-sum : ∀ {m P Q} → sumProc {m} P Q ≡ sumProc Q P
  comm-sum = cong Fold (comm _ _)
                    
  assoc-sum : ∀ {m P Q R} → sumProc {m} (sumProc P Q) R ≡ sumProc P (sumProc Q R)
  assoc-sum = cong Fold (sym (assoc _ _ _))

-- Unitality of parProc.
  unit-par : ∀ {n} {P : Proc n} → parProc P endProc ≡ P
  unit-par {n}{P} =
    cong′ (λ x → isCCS-alg.parX (x n) P (isCCS-alg.endX (x n))) (fix-eq ProcCCS-algF)
    ∙ cong Fold (cong₂ _∪_ (unit _) (bind-ø (Unfold P))
                ∙ unit _
                ∙ cong′ (λ x → mapP∞ x (Unfold P)) (funExt (λ {(a , P') → StepPath refl
                  (later-ext (\ α → unit∣∣X (ih α))) }))
                ∙ mapidP∞ _)

-- Commutativity of parProc.
  comm-synchF : ∀ {n} {p q : F' n (next Proc)} → synchF p q ≡ synchF q p
  comm-synchF {n}{P}{Q} =
    cong (bind P) (funExt (λ P' → bind-∪ _ _ Q))
    ∙ bind-∪ _ _ P
    ∙ cong₂ _∪_ (bind-comm _ P Q ∙ cong (bind Q) (funExt (λ Q' →
                  cong (bind P) (funExt (λ P' → 
                    cong (λ (x : ▹ (∀ n → Proc n → Proc n → Proc n)) → synch' (λ α → x α _) P' Q')
                                                     (later-ext (λ α → funExt λ n → funExt (λ q → funExt λ q' → ih α .comm∣∣X {P = q}))))))))
                (sym (bind-comm _ Q P ∙ cong (bind P) (funExt (λ P' →
                  cong (bind Q) (funExt (λ Q' → cong (λ (x : ▹ (∀ n → Proc n → Proc n → Proc n)) → synch' (λ α → x α _) Q' P')
                                                     (later-ext (λ α → funExt λ n → funExt (λ q → funExt λ q' → ih α .comm∣∣X {P = q}))))))))) 
    ∙ comm _ _
    ∙ sym (bind-∪ _ _ Q)
    ∙ sym (cong (bind Q) (funExt (λ Q' → bind-∪ _ _ P)))

  comm-par : ∀ {n} {p q : Proc n} → parProc p q ≡ parProc q p
  comm-par {n}{P}{Q} =
    cong′ (λ x → isCCS-alg.parX (x n) P Q) (fix-eq ProcCCS-algF)
    ∙ cong Fold (cong₂ _∪_
                  (cong₂ _∪_
                    (cong′ (λ f → mapP∞ f (Unfold P)) (funExt (λ _ → StepPath refl (later-ext (\ α → ih α .comm∣∣X {Q = Q}))))) 
                    (cong′ (λ f → mapP∞ f (Unfold Q)) (funExt (λ _ → StepPath refl (later-ext (\ α → ih α .comm∣∣X {P = P})))))
                  ∙ comm _ _)
                  (comm-synchF {_}{Unfold P}{Unfold Q}))
    ∙ cong′ (λ x → isCCS-alg.parX (x n) Q P) (sym (fix-eq ProcCCS-algF))

-- Associativity of parProc.
  step-LR : ∀ {n} P Q R →
    stepL {n} (stepR P Q) R ≡ stepR P (stepL Q R)
  step-LR P Q R =
    mapmapP∞ _ _ Q
    ∙ cong′ (λ f → mapP∞ f Q) (funExt (λ { (a , Q') →
        StepPath refl (later-ext (λ α → ih α .assoc∣∣X {P = P})) })) ∙ sym (mapmapP∞ _ _ Q)

-- Associativity of parProc (which requires many lemmata).
  step-RR : ∀ {n} P Q R →
    stepR {n} P (stepR Q R) ≡ stepR (parProc P Q) R
  step-RR P Q R =
    mapmapP∞ _ _ R
    ∙ sym (cong′ (λ f → mapP∞ f R) (funExt (λ { (a , R') →
        StepPath refl (later-ext (λ α → ih α .assoc∣∣X {P = P}))})))

  stepL-synch'-L : ∀ {n} (aP aQ : Step (\ n → ▹ Proc n) n) R →
    stepL (synch' (λ _ → parProc) aP aQ) R
    ≡ synch' (λ _ → parProc) aP (theLabel aQ , λ α → parProc (theX aQ α) R) 
  stepL-synch'-L P@(a , _) Q@(b , _) R with canSynchL? a b
  stepL-synch'-L {n} (.(out _) , P') (.(inp _) , Q') R | local _
    = cong η (StepPath refl (later-ext (λ α → ih α .assoc∣∣X {P = P' α}))) 
  stepL-synch'-L (a , _) (b , _) R | nope = refl

  stepL-synch'-R : ∀ {n} (aP aQ : Step (\ n → ▹ Proc n) n) R →
    stepL (synch' (λ _ p q → parProc q p) aP aQ) R
    ≡ synch' (λ _ p q → parProc q p) (theLabel aP , λ α → parProc (theX aP α) R) aQ
  stepL-synch'-R (a , P) (b , Q) R with canSynchL? a b
  stepL-synch'-R (.(out _) , P) (.(inp _) , Q) R | local _ =
    cong η (StepPath refl (later-ext (λ α → ih α .assoc∣∣X {P = Q α})))
  stepL-synch'-R (a , P) (b , Q) R | nope = refl

  stepR-synch'-L : ∀ {n} P (aQ aR : Step (\ n → ▹ Proc n) n) →
    stepR P (synch' (λ _ → parProc) aQ aR)
    ≡ synch' (λ _ → parProc) (theLabel aQ , λ α → parProc P (theX aQ α)) aR 
  stepR-synch'-L R (a , P) (b , Q) with canSynchL? a b
  ... | local refl' = cong η (StepPath refl (later-ext (λ α → sym (ih α .assoc∣∣X {P = R}))))
  ... | nope = refl

  stepR-synch'-R : ∀ {n} P (aQ aR : Step (\ n → ▹ Proc n) n) →
    stepR P (synch' (λ _ p q → parProc q p) aQ aR)
    ≡ synch' (λ _ p q → parProc q p) aQ (theLabel aR , λ α → parProc P (theX aR α)) 
  stepR-synch'-R P (a , Q) (b , R) with canSynchL? a b
  ... | local _ = cong η (StepPath refl (later-ext (λ α → sym (ih α .assoc∣∣X {P = P}))))
  ... | nope = refl

  synch'-assoc : ∀ {n} (aP : Step (\ n → ▹ Proc n) n) Q aR →
    synch' (λ _ → parProc) (theLabel aP , λ α → parProc (theX aP α) Q) aR 
    ≡ synch' (λ _ → parProc) aP (theLabel aR , λ α → parProc Q (theX aR α)) 
  synch'-assoc (a , P) Q (b , R) with canSynchL? a b
  ... | local _ = cong η (StepPath refl (later-ext (λ α → ih α .assoc∣∣X {P = P α})))
  ... | nope = refl

  synch'-assoc' : ∀ {n} (aP : Step (\ n → ▹ Proc n) n) aQ aR →
    bind (synch' (λ _ → parProc) aP aQ) (λ z → synch' (λ _ → parProc) z aR)
    ≡ bind (synch' (λ _ → parProc) aQ aR) (synch' (λ _ → parProc) aP)
  synch'-assoc' (a , P) (b , Q) (c , R) with canSynchL? a b
  ... | local refl' = refl
  synch'-assoc' (a , P) (b , Q) (c , R) | nope with canSynchL? b c
  synch'-assoc' (a , P) (b , Q) (c , R) | nope | local refl' with canSynchL? a τ
  synch'-assoc' (a , P) (.(out _) , Q) (.(inp _) , R) | nope | local refl' | nope = refl
  synch'-assoc' (a , P) (b , Q) (c , R) | nope | nope = refl

  synchF-L : ∀ {n} (P Q : F' n (\ _ → Proc)) R →
    stepL (synchF P Q) R ≡ synchF P (stepL Q R)
  synchF-L P Q R =
    map-bind P _ _
    ∙ cong (bind P) (funExt (λ aP' →
        map-bind Q _ _
        ∙ cong (bind Q) (funExt (λ aQ' →
            cong₂ _∪_
              (stepL-synch'-L aP' aQ' R)
              (stepL-synch'-R aQ' aP' R)))
        ∙ sym (bind-map Q _ _)))

  synchF-R : ∀ {n} P (Q R : F' n (\ _ → Proc)) →
    stepR P (synchF Q R) ≡ synchF (stepR P Q) R
  synchF-R P Q R =
    map-bind Q _ _
    ∙ cong (bind Q) (funExt (λ aQ' →
        map-bind R _ _
        ∙ cong (bind R) (funExt (λ aR' → cong₂ _∪_ (stepR-synch'-L P aQ' aR') (stepR-synch'-R P aR' aQ')))))
    ∙ sym (bind-map Q _ _)

  synchF-LR : ∀ {n} (P : F' n (\ _ → Proc)) Q R →
    synchF (stepL P Q) R ≡ synchF P (stepR Q R)
  synchF-LR P Q R =
    bind-map P _ _
    ∙ cong (bind P) (funExt (λ aP' →
        cong (bind R) (funExt (λ aR' →
          cong₂ _∪_
            (synch'-assoc aP' Q aR')
            (cong′ (λ (f : ▹ (∀ n → Proc n → Proc n → Proc n)) → synch' (λ α {n} → f α n) aR' (theLabel aP' , λ α → parProc (theX aP' α) Q)) 
              (later-ext (λ α → funExt (λ _ → funExt (λ p → (funExt (λ q → ih α .comm∣∣X {P = q}))))))
             ∙ cong′ (synch' (λ _ → parProc) aR') (StepPath refl (later-ext (λ α → ih α .comm∣∣X {P = theX aP' α})))
             ∙ sym (synch'-assoc aR' Q aP')
             ∙ cong′ (λ x → synch' (λ _ → parProc) x aP') (StepPath refl (later-ext (λ α → ih α .comm∣∣X {P = theX aR' α})))
             ∙ cong′ (λ (f : ▹ (∀ n → Proc n → Proc n → Proc n)) → synch' (λ α {n} → f α n) (theLabel aR' , λ α → parProc Q (theX aR' α)) aP')
                (later-ext (λ α → funExt (λ _ → funExt (λ p → (funExt (λ q → ih α .comm∣∣X {P = p})))))))))
        ∙ sym (bind-map R _ _)))

  synch'synch'1 : ∀ {n} a b c (f g : ▹ (∀ {n} → Proc n → Proc n → Proc n)) → bind (synch' f {n} b c) (synch' g a) ≡ ø
  synch'synch'1 (a , P) (b , Q) (c , R) f g with canSynchL? b c
  synch'synch'1 (a , P) (.(out _) , Q) (.(inp _) , R) f g | local x with canSynchL? a τ
  ... |  nope = refl
  synch'synch'1 (a , P) (b , Q) (c , R) f g | nope = refl

  synch'synch'2 : ∀ {n} a b c (f g : ▹ (∀ {n} → Proc n → Proc n → Proc n)) → bind (synch' f {n} b c) (\ v → synch' g v a) ≡ ø
  synch'synch'2 (a , P) (b , Q) (c , R) f g with canSynchL? b c
  synch'synch'2 (a , P) (.(out _) , Q) (.(inp _) , R) f g | local x with canSynchL? a τ
  ... |  nope = refl
  synch'synch'2 (a , P) (b , Q) (c , R) f g | nope = refl

  synchsynch : ∀ {n} b' c' a' → bind (synch {n} b' c') (synch a') ≡ ø
  synchsynch b c a = (bind (synch' (λ _ → parProc) b c) (synch a) ∪ bind (synch' _ c b) (synch a) )
                   ≡⟨ bind-∪ _ _ (synch b c)  ⟩
                   (bind (synch' (λ _ → parProc) b c) (synch' (λ _ → parProc) a) ∪ bind (synch' _ c b) (synch' _ a))
                    ∪ (bind (synch' (λ _ → parProc) b c) (\ bc → synch' _ bc a) ∪ bind (synch' _ c b) (\ bc → synch' _ bc a))
                   ≡⟨ cong₂ _∪_ (cong₂ _∪_ (synch'synch'1 a b c _ _) (synch'synch'1 a c b _ _)) (cong₂ _∪_ (synch'synch'2 a b c _ _) (synch'synch'2 a c b _ _)) ⟩
                   idem _ ∙ idem _

  synchsynchF : ∀ {n} (P : F' n (\ _ → Proc)) Q R →
     synchF P (synchF Q R) ≡ ø
  synchsynchF P Q R = cong′ (bind P) (funExt \ a' → bind-bind Q _ _ ∙ cong′ (bind Q) (funExt \ b' → bind-bind R _ _ ∙ cong′ (bind R)
    (funExt \ c' → synchsynch b' c' a') ∙ bind-ø R) ∙ bind-ø Q) ∙ bind-ø P

  step-LL : ∀ {n} P Q R →
    stepL {n} (stepL P Q) R ≡ stepL P (parProc Q R)
  step-LL {n} P Q R =
    mapmapP∞ _ _ P
    ∙ cong′ (λ f → mapP∞ f P) (funExt (λ { (a , P') →
        StepPath refl (later-ext (λ α →  assoc∣∣X (ih α) {P = _}{Q}{R}))}))

  assoc-synchF : ∀ {n} (P : F' n (\ _ → Proc)) Q R →
    synchF (synchF P Q) R ≡ synchF P (synchF Q R)
  assoc-synchF P Q R =
    comm-synchF {p = synchF P Q} {R} ∙ synchsynchF R P Q ∙ sym (synchsynchF P Q R) 

  assoc-par : ∀ {n} {P Q R : Proc n} → parProc (parProc P Q) R ≡ parProc P (parProc Q R)
  assoc-par {n}{P}{Q}{R} =
   cong₂ parProc (cong′ (λ x → isCCS-alg.parX (x n) P Q) (fix-eq ProcCCS-algF)) refl
   ∙ cong′ (λ x → isCCS-alg.parX (x n) (isCCS-alg.parX (fix-eq ProcCCS-algF i1 n) P Q) R) (fix-eq ProcCCS-algF)
   ∙ cong Fold (sym (assoc _ _ _ ∙ assoc _ _ _ ∙ assoc _ _ _)
                ∙ cong₂ _∪_
                    (step-LL (Unfold P) Q R
                     ∙ cong′ (λ f → mapP∞ f (Unfold P)) (funExt (λ P' →
                             StepPath refl (later-ext (λ α → cong₂ parProc refl (cong′ (λ x → isCCS-alg.parX (x n) Q R) (fix-eq ProcCCS-algF)))))))
                    (cong₂ _∪_ (step-LR P (Unfold Q) R)
                      (comm _ _ ∙ sym (assoc _ _ _)
                       ∙ cong₂ _∪_
                           (sym (step-RR P Q (Unfold R)
                            ∙ cong′ (λ f → mapP∞ f (Unfold R)) (funExt (λ R' →
                                    StepPath refl (later-ext (λ α → cong₂ parProc (cong′ (λ x → isCCS-alg.parX (x n) P Q) (fix-eq ProcCCS-algF)) refl))))))
                           (comm _ _
                            ∙ cong₂ _∪_
                                (synchF-L (Unfold P) (Unfold Q) R ∙ sym (bind-comm _ (stepL (Unfold Q) R) (Unfold P)))
                                (sym (assoc _ _ _)
                                 ∙ cong₂ _∪_
                                     (synchF-LR (Unfold P) Q (Unfold R) ∙ sym (bind-comm _ (stepR Q (Unfold R)) (Unfold P)))
                                     (cong₂ _∪_
                                       (sym (synchF-R P (Unfold Q) (Unfold R)))
                                       (assoc-synchF (Unfold P) (Unfold Q) (Unfold R)
                                        ∙ cong (bind (Unfold P)) (funExt (λ P' → bind-bind (Unfold Q) _ _))
                                        ∙ bind-comm _ (Unfold P) (Unfold Q)
                                        ∙ cong (bind (Unfold Q)) (funExt (λ Q' →
                                            cong (bind (Unfold P)) (funExt (λ P' → bind-bind (Unfold R) _ _))
                                            ∙ bind-comm _ (Unfold P) (Unfold R)
                                            ∙ cong (bind (Unfold R)) (funExt (λ R' → bind-comm _ (Unfold P) (synch Q' R')))
                                            ∙ sym (bind-bind (Unfold R) _ _)))
                                        ∙ sym (bind-bind (Unfold Q) _ _))
                                      ∙ comm _ _))
                            ∙ assoc _ _ _ ∙ assoc _ _ _ ∙ comm _ _
                            ∙ cong₂ _∪_ refl (bind-comm _ (Unfold (isCCS-alg.parX (fix-eq ProcCCS-algF i1 n) Q R)) (Unfold P))))
                     ∙ assoc _ _ _ ∙ assoc _ _ _)
                ∙ assoc _ _ _)
   ∙ sym (cong′ (λ x → isCCS-alg.parX (x n) P (isCCS-alg.parX (fix-eq ProcCCS-algF i1 n) Q R)) (fix-eq ProcCCS-algF))
   ∙ sym (cong₂ parProc refl (cong′ (λ x → isCCS-alg.parX (x n) Q R) (fix-eq ProcCCS-algF)))

-- The equation characterizing replication as iterated parallel composition.
  synch-! : ∀ {n} (P : Proc n)
    → stepL (synchF (Unfold P) (Unfold P)) (!Proc P) ≡ synchF (Unfold P) (Unfold (!Proc P))
  synch-! P =
    sym (unit _)
    ∙ cong₂ _∪_ refl (sym (cong′ (λ P' → stepL P' (!Proc P)) (synchsynchF (Unfold P) (Unfold P) (Unfold P))))
    ∙ cong₂ _∪_ (synchF-L (Unfold P) (Unfold P) (!Proc P) ∙ bind-comm _ (Unfold P) (stepL (Unfold P) (!Proc P)))
                (synchF-L (Unfold P) (synchF (Unfold P) (Unfold P)) (!Proc P) ∙ bind-comm _ (Unfold P) (stepL (synchF (Unfold P) (Unfold P)) (!Proc P)))
    ∙ bind-comm _ (stepL (Unfold P) (!Proc P) ∪ stepL (synchF (Unfold P) (Unfold P)) (!Proc P)) (Unfold P)
    ∙ cong′ (synchF (Unfold P)) (cong Unfold (sym (!Proc-eq {_}{P})))

  stepR-! : ∀ {n} {P : Proc n} → stepR P (Unfold (!Proc P)) ≡ Unfold (!Proc P)
  stepR-! {_}{P} =
    cong₂ mapP∞ (funExt (λ aP' → StepPath refl (later-ext (λ α → ih α .comm∣∣X {P = P})))) (refl {x = Unfold (!Proc P)})
    ∙ cong₂ stepL (cong Unfold (!Proc-eq {_}{P})) refl
    ∙ cong₂ _∪_
        (step-LL (Unfold P) (!Proc P) P ∙ cong′ (stepL' (Unfold P)) (later-ext (λ α → ih α .comm∣∣X {P = !Proc P} ∙ sym (ih α .replX {P = P}))))
        (step-LL (synchF (Unfold P) (Unfold P)) (!Proc P) P ∙ cong′ (stepL' (synchF (Unfold P) (Unfold P))) (later-ext (λ α → ih α .comm∣∣X {P = !Proc P} ∙ sym (ih α .replX {P = P}))))
    ∙ cong Unfold (sym (!Proc-eq {P = P}))

  repl-par : ∀ {n} {P : Proc n} → !Proc P ≡ parProc P (!Proc P)
  repl-par {_}{P} =
    cong Fold
      (Unfold (!Proc P)
       ≡⟨ sym (idem _) ⟩
       Unfold (!Proc P) ∪ Unfold (!Proc P)
       ≡⟨ cong₂ _∪_ (sym (stepR-! {P = P})) (cong Unfold (!Proc-eq {P = P})) ⟩
       stepR P (Unfold (!Proc P)) ∪ (stepL (Unfold P) (!Proc P) ∪ stepL (synchF (Unfold P) (Unfold P)) (!Proc P))
       ≡⟨ cong₂ _∪_ refl (cong₂ _∪_ refl (synch-! P)) ⟩
       stepR P (Unfold (!Proc P)) ∪ (stepL (Unfold P) (!Proc P) ∪ synchF (Unfold P) (Unfold (!Proc P)))
       ≡⟨ assoc _ _ _ ⟩
       (stepR P (Unfold (!Proc P)) ∪ stepL (Unfold P) (!Proc P)) ∪ synchF (Unfold P) (Unfold (!Proc P))
       ≡⟨ cong₂ _∪_ (comm _ _) refl ⟩
       (stepL (Unfold P) (!Proc P) ∪ stepR P (Unfold (!Proc P))) ∪ synchF (Unfold P) (Unfold (!Proc P))
       ∎)
    ∙ cong′ (λ x → isCCS-alg.parX (x _) P (isCCS-alg.!X (fix-eq ProcCCS-algF i0 _) P)) (sym (fix-eq ProcCCS-algF))

-- Restriction of the nil process.
  ν-end : ∀ {n} → νProc endProc ≡ endProc {n}
  ν-end {n} = refl

-- The equation relating restriction and parallel composition (plus
-- many required lemmata).
  ν-stepL' : ∀ {n} aP Q →
    stepν (theLabel aP , (λ α → parProc (theX aP α) (mapProc _ _ ι Q)))
      ≡ stepL {n} (stepν aP) Q
  ν-stepL' (a , P) Q with canNu? a
  ... | out x = cong η (StepPath refl (later-ext (λ α → ih α .ν∣∣X)))
  ... | inp x = cong η (StepPath refl (later-ext (λ α → ih α .ν∣∣X)))
  ... | τ = cong η (StepPath refl (later-ext (λ α → ih α .ν∣∣X)))
  ... | nope x = refl

  ν-stepL : ∀ {m P Q} →
    νProc (Fold (stepL (Unfold P) (mapProc m _ ι Q)))
    ≡ Fold (stepL (Unfold (νProc P)) Q)
  ν-stepL {n}{P}{Q} =
    cong′ (λ x → isCCS-alg.νX (x _) (Fold (stepL (Unfold P) (mapProc n _ ι Q)))) (fix-eq ProcCCS-algF)
    ∙ cong Fold
        (bind-map (Unfold P) _ _
         ∙ cong (bind (Unfold P)) (funExt (λ aP' → ν-stepL' aP' Q))
         ∙ sym (map-bind (Unfold P) _ _))
    ∙ cong′ (λ x → Fold (stepL (Unfold (isCCS-alg.νX (x _) P)) Q)) (sym (fix-eq ProcCCS-algF))

  ν-stepR' : ∀ {n} P (aQ : Step (\ n → ▹ Proc n) n) →
    stepν {n} (mapAct ι (theLabel aQ) , (λ α → parProc P (mapProc _ _ ι (theX aQ α))))
    ≡ η (theLabel aQ , (λ α → parProc (νProc P) (theX aQ α)))
  ν-stepR' P (`out a Q) with decName (ι a) (fresh _)
  ... | yes p = ⊥-rec (fresh-ι p)
  ... | no p =
    cong′ η (StepPath (cong′ out (down-ι p)) (later-ext (λ α → ih α .ν∣∣X)))
  ν-stepR' P (`inp a Q) with decName (ι a) (fresh _)
  ... | yes p = ⊥-rec (fresh-ι p)
  ... | no p =
    cong′ η (StepPath (cong′ inp (down-ι p)) (later-ext (λ α → ih α .ν∣∣X)))
  ν-stepR' P (`τ Q) = cong′ η (StepPath refl (later-ext (λ α → ih α .ν∣∣X)))

  ν-stepR : ∀ {m P Q} →
    νProc (Fold (stepR P (Unfold (mapProc m _ ι Q)))) ≡ Fold (stepR (νProc P) (Unfold Q))
  ν-stepR {m} {P} {Q} =
    cong′ νProc (cong′ Fold (cong′ (stepR P) (mapProc'-eq' _ _ _ _)))
    ∙ cong′ (λ x → isCCS-alg.νX (x _) (Fold (stepR P (mapProcF (next mapProc') m (suc m) ι (Unfold Q))))) (fix-eq ProcCCS-algF)
    ∙ cong Fold
        (cong′ (λ x → bind x _) (mapmapP∞ _ _ (Unfold Q))
         ∙ bind-map (Unfold Q) _ _
         ∙ cong′ (bind (Unfold Q)) (funExt (ν-stepR' P))
         ∙ sym (mapP∞-is-bind (Unfold Q)))

  ν-synch' : ∀ {n} aP aQ →
    bind (mapSProc n _ ι aQ) (λ v → bind (synch' (λ _ → parProc) aP v) stepν)
    ≡ bind (stepν aP) (λ z → synch' (λ _ → parProc) z aQ)
  ν-synch' (`out a P) (`out a' Q) with canNu? (out a)
  ... | out x = refl
  ... | nope x = refl
  ν-synch' (`out a P) (`inp a' Q) with  decName a (ι a') | canNu? (out a)
  ν-synch' (`out _ P) (`inp a' Q) | yes eq | out {a} r with decName a a'
  ... | yes eq' = cong η (StepPath refl (later-ext λ α → ih α .ν∣∣X))
  ... | no ¬eq' = ⊥-rec (¬eq' (ι-inj _ _ (sym r ∙ eq))) 
  ν-synch' (`out _ P) (`inp a' Q) | yes eq | nope (out r) =
    ⊥-rec (fresh-ι (sym eq ∙ r))
  ν-synch' (`out _ P) (`inp a' Q) | no ¬eq | out {a} r with decName a a'
  ... | yes eq' = ⊥-rec (¬eq (r ∙ cong ι eq')) 
  ... | no ¬eq' = refl
  ν-synch' (`out _ P) (`inp a' Q) | no ¬eq | nope (out _) = refl
  ν-synch' (`out a P) (`τ Q) with canNu? (out a)
  ... | out refl' = refl
  ... | nope (out _) = refl
  ν-synch' (`inp a P) (a' , Q) with canNu? (inp a)
  ... | inp _ = refl
  ... | nope (inp _) = refl
  ν-synch' (`τ P) (a' , Q) = refl

  ν-synch'2 : ∀ {n} aP aQ →
    bind (mapSProc n _ ι aQ) (λ v → bind (synch' (next \ p q → parProc q p) v aP) stepν)
    ≡ bind (stepν aP) (λ z → synch' (next \ p q → parProc q p) aQ z)
  ν-synch'2 (a , P) (`out a' Q) with canNu? a
  ν-synch'2 (_ , P) (`out a' Q) | out refl' = refl
  ν-synch'2 (_ , P) (`out a' Q) | inp {a}{a''} r with decName a' a | decName (ι a') (ι a)
  ... | yes eq | yes eq' with decName (ι a') a''
  ... | yes p = cong η (StepPath refl (later-ext (λ α → ih α .ν∣∣X)))
  ... | no ¬p = ⊥-rec (¬p (cong ι eq ∙ sym r))
  ν-synch'2 (_ , P) (`out a' Q) | inp {a}{a''} r | yes eq | no ¬eq' = ⊥-rec (¬eq' (cong ι eq))
  ν-synch'2 (_ , P) (`out a' Q) | inp {a}{a''} r | no ¬eq | yes eq' = ⊥-rec (¬eq (ι-inj _ _ eq'))
  ν-synch'2 (_ , P) (`out a' Q) | inp {a}{a''} r | no ¬eq | no ¬eq' with decName (ι a') a''
  ... | yes p = ⊥-rec (¬eq' (p ∙ r))
  ... | no ¬p = refl
  ν-synch'2 (_ , P) (`out a' Q) | τ = refl
  ν-synch'2 (_ , P) (`out a' Q) | nope (inp {a''} r) with decName (ι a') (fresh _)
  ... | yes eq = ⊥-rec (fresh-ι eq)
  ... | no ¬eq with decName (ι a') a''
  ... | yes p = ⊥-rec (fresh-ι (p ∙ r))
  ... | no ¬p = refl
  ν-synch'2 (_ , P) (`out a' Q) | nope (out refl') = refl
  ν-synch'2 (a , P) (`inp a' Q) with canNu? a
  ... | out refl' = refl
  ... | inp refl' = refl
  ... | τ = refl
  ... | nope x = refl
  ν-synch'2 (a , P) (`τ Q) with canNu? a
  ... | out refl' = refl
  ... | inp refl' = refl
  ... | τ = refl
  ... | nope x = refl
  
  ν-synchF : ∀ {m} P Q →
    νProc (Fold (synchF (Unfold P) (Unfold (mapProc m _ ι Q))))
    ≡ Fold (synchF (Unfold (νProc P)) (Unfold Q))
  ν-synchF {n} P Q = 
    cong′ (λ x → isCCS-alg.νX (x _) (Fold (synchF (Unfold P) (Unfold (mapProc _ _ ι Q)))))
          (fix-eq ProcCCS-algF)
    ∙ cong Fold
           (bind-bind (Unfold P) _ _
            ∙ cong (bind (Unfold P)) (funExt (λ aP' →
                bind-bind (mapProc' n (suc n) ι (Unfold Q)) _ _
                ∙ cong₂ bind (mapProc'-eq' _ _ _ (Unfold Q)) refl
                ∙ bind-map (Unfold Q) _ _
                ∙ cong (bind (Unfold Q)) (funExt (λ aQ' →
                     cong₂ _∪_
                           (ν-synch' aP' aQ')
                           (ν-synch'2 aP' aQ')
                    ∙ sym (bind-∪ _ _ (stepν aP'))))
                ∙ bind-comm _ (Unfold Q) (stepν aP')))
            ∙ sym (bind-bind (Unfold P) _ _))
    ∙ cong′ (λ x → Fold (synchF (Unfold (isCCS-alg.νX (x _) P)) (Unfold Q)))
            (sym (fix-eq ProcCCS-algF))      

  ν-par : ∀ {m P Q} → νProc (parProc P (mapProc m _ ι Q)) ≡ parProc (νProc P) Q
  ν-par {n}{P}{Q} =
    cong′ νProc (cong′ (λ x → isCCS-alg.parX (x _) P (mapProc n _ ι Q)) (fix-eq ProcCCS-algF))
    ∙ cong′ (λ x → isCCS-alg.νX (x _) (isCCS-alg.parX (fix-eq ProcCCS-algF i1 _) P (mapProc n _ ι Q))) (fix-eq ProcCCS-algF)
    ∙ cong Fold
        (cong₂ _∪_ (cong₂ _∪_
                      (cong Unfold (cong′ (λ x → isCCS-alg.νX (x _) (Fold (stepL (Unfold P) (mapProc n _ ι Q)))) (sym (fix-eq ProcCCS-algF)) ∙ (ν-stepL {P = P})))
                      (cong Unfold (cong′ (λ x → isCCS-alg.νX (x _) (Fold (stepR P (Unfold (mapProc n _ ι Q))))) (sym (fix-eq ProcCCS-algF)) ∙ ν-stepR)))
                   (cong Unfold (cong′ (λ x → isCCS-alg.νX (x _) (Fold (synchF (Unfold P) (Unfold (mapProc _ _ ι Q))))) (sym (fix-eq ProcCCS-algF)) ∙ ν-synchF P Q)))
    ∙ cong′ (λ x → isCCS-alg.parX (x _) (νProc P) Q) (sym (fix-eq ProcCCS-algF))

-- The equation stating that the order in which a process is
-- restricted twice does not matter (again with some extra lemmata).
  stepν-swap : ∀ {n} (aP : Step (\ n → ▹ Proc n) (suc (suc n))) →
      bind (stepν aP) stepν ≡ bind (stepν (mapSProc' _ _ swap aP)) stepν
  stepν-swap (a , P) with canNu? a
  ... | out {a = a} {a'} eq with canNu? (out (swap a'))
  ... | out {a = b}{b'} eq2 with canNu? (out b) | canNu? (out a)
  ... | out {a = a₁} eq' | out {a = a₂} eq'' =
    cong η (StepPath (λ i → out (p i))
                     (later-ext λ α → ih α .swapνX))
    where        
      p' : ι (ι a₂) ≡ ι (ι a₁)
      p' =
        sym (swap-ιι a₂)
        ∙ (λ i → swap (ι (eq'' (~ i))))
        ∙ (λ i → swap (eq (~ i)))
        ∙ eq2
        ∙ λ i → ι (eq' i)
        
      p : a₂ ≡ a₁
      p = ι-inj _ _ (ι-inj _ _ p')          
  ... | out eq' | nope (out eq'') = ⊥-rec (fresh-ι p)
    where
      p : ι b ≡ fresh (suc _)
      p =
        sym eq2
        ∙ (λ i → swap (eq i))
        ∙ snoc-ι _ _ _
        ∙ (λ i → snoc (λ x → ι (ι x)) (fresh (suc _)) (eq'' i))
        ∙ snoc-fresh _ _
  ... | nope (out eq') | out {a = a₂} eq'' = ⊥-rec (fresh-ι (ι-inj _ _ p))
    where        
      p : ι (ι a₂) ≡ ι (fresh _)
      p = 
        sym (swap-ιι a₂)
        ∙ (λ i → swap (ι (eq'' (~ i))))
        ∙ (λ i → swap (eq (~ i)))
        ∙ eq2
        ∙ λ i → ι (eq' i)
  ... | nope (out _) | nope (out _) = refl
  stepν-swap (._ , P) | out {a = a}{a'} eq | nope (out eq') with canNu? (out a)
  ... | out eq'' = ⊥-rec (fresh-ι (sym p))
    where
      p : fresh (suc _) ≡ ι (ι _)
      p =
        sym eq'
        ∙ (λ i → swap (eq i))
        ∙ snoc-ι _ _ _
        ∙ (λ i → snoc (λ x → ι (ι x)) (fresh (suc _)) (eq'' i))
        ∙ snoc-ι _ _ _
  ... | nope (out eq'') = refl
  stepν-swap (._ , P) | inp {a = a}{a'} eq with canNu? (inp (swap a'))
  ... | inp {a = b}{b'} eq2 with canNu? (inp b) | canNu? (inp a)
  ... | inp eq' | inp eq'' = 
    cong η (StepPath (λ i → inp (p i))
                     (later-ext λ α → ih α .swapνX))
    where        
      p' : ι (ι _) ≡ ι (ι _)
      p' =
        sym (swap-ιι _)
        ∙ (λ i → swap (ι (eq'' (~ i))))
        ∙ (λ i → swap (eq (~ i)))
        ∙ eq2
        ∙ λ i → ι (eq' i)
        
      p : _ ≡ _
      p = ι-inj _ _ (ι-inj _ _ p')          
  ... | inp eq' | nope (inp eq'') = ⊥-rec (fresh-ι p)
    where
      p : ι b ≡ fresh (suc _)
      p =
        sym eq2
        ∙ (λ i → swap (eq i))
        ∙ snoc-ι _ _ _
        ∙ (λ i → snoc (λ x → ι (ι x)) (fresh (suc _)) (eq'' i))
        ∙ snoc-fresh _ _
  ... | nope (inp eq') | inp eq'' = ⊥-rec (fresh-ι (ι-inj _ _ p))
    where        
      p : ι (ι _) ≡ ι (fresh _)
      p = 
        sym (swap-ιι _)
        ∙ (λ i → swap (ι (eq'' (~ i))))
        ∙ (λ i → swap (eq (~ i)))
        ∙ eq2
        ∙ λ i → ι (eq' i)
  ... | nope (inp eq') | nope (inp eq'') = refl
  stepν-swap (._ , P) | inp {a = a}{a'} eq | nope (inp eq') with canNu? (inp a)
  ... | inp eq'' = ⊥-rec (fresh-ι (sym p))
    where
      p : fresh (suc _) ≡ ι (ι _)
      p =
        sym eq'
        ∙ (λ i → swap (eq i))
        ∙ snoc-ι _ _ _
        ∙ (λ i → snoc (λ x → ι (ι x)) (fresh (suc _)) (eq'' i))
        ∙ snoc-ι _ _ _
  ... | nope (inp eq'') = refl
  stepν-swap (._ , P) | τ = cong η (StepPath refl (later-ext λ α → ih α .swapνX))
  stepν-swap (._ , P) | nope (out {a'} eq) with canNu? (out (swap a'))
  ... | nope (out eq') = refl
  ... | out {a = a} eq' with canNu? (out a)
  ... | nope (out eq'') = refl
  ... | out eq'' = ⊥-rec (fresh-ι (ι-inj _ _ (sym p)))
    where
      p : ι (fresh _) ≡ ι (ι _)
      p =
        sym (snoc-fresh _ _)          
        ∙ (λ i → swap (eq (~ i)))
        ∙ eq'
        ∙ λ i → ι (eq'' i)
  stepν-swap (._ , P) | nope (inp {a'} eq) with canNu? (inp (swap a'))
  ... | nope (inp eq') = refl
  ... | inp {a = a} eq' with canNu? (inp a)
  ... | nope (inp eq'') = refl
  ... | inp eq'' = ⊥-rec (fresh-ι (ι-inj _ _ (sym p)))
    where
      p : ι (fresh _) ≡ ι (ι _)
      p =
        sym (snoc-fresh _ _)          
        ∙ (λ i → swap (eq (~ i)))
        ∙ eq'
        ∙ λ i → ι (eq'' i)

  ν-swap : ∀ {n} {P : Proc (suc (suc n))} → νProc (νProc P) ≡ νProc (νProc (mapProc _ _ swap P))
  ν-swap {n} {P} =
    νProc (νProc P)
      ≡⟨ cong (λ x → isCCS-alg.νX (x _) (isCCS-alg.νX (x _) P)) (fix-eq ProcCCS-algF) ⟩
    Fold (bind (bind (Unfold P) stepν) stepν)
      ≡⟨ cong Fold (bind-bind (Unfold P) stepν stepν) ⟩
    Fold (bind (Unfold P) (λ x → bind (stepν x) stepν))
      ≡⟨ cong Fold (cong′ (bind (Unfold P)) (funExt stepν-swap)) ⟩
    Fold (bind (Unfold P) (λ x → bind (stepν (mapSProc' _ _ swap x)) stepν))
      ≡⟨ cong Fold (sym (bind-bind (Unfold P) _ _)) ⟩
    Fold (bind (bind (Unfold P) (λ x → stepν (mapSProc' _ _ swap x))) stepν)
      ≡⟨ cong Fold (cong (λ z → bind z stepν) (sym (bind-map (Unfold P) _ _))) ⟩
    Fold (bind (bind (mapP∞ (mapSProc' _ _ swap) (Unfold P)) stepν) stepν)
      ≡⟨ cong Fold (cong (λ z → bind (bind (Unfold z) stepν) stepν) (sym (mapProc-swap P))) ⟩
    Fold (bind (bind (Unfold (mapProc _ _ swap P)) stepν) stepν)
      ≡⟨ cong (λ x → isCCS-alg.νX (x _) (isCCS-alg.νX (x _) (mapProc _ _ swap P))) (sym (fix-eq ProcCCS-algF)) ⟩
    νProc (νProc (mapProc _ _ swap P))
      ∎

-- Putting everything together.
  ProcStructCongF : StructCong ProcCCS-alg (mapProc-Inj _ _) _≡_
  ProcStructCongF = 
    record
       { refl≈X = refl
       ; sym≈X = sym
       ; _∙≈X_ = _∙_
       ; cong·X = cong′ (actProc _)
       ; cong⊕X = λ eq1 eq2 → cong₂ sumProc eq1 eq2
       ; cong∣∣X = λ eq1 eq2 → cong₂ parProc eq1 eq2
       ; congνX = cong′ νProc
       ; cong!X = cong′ !Proc
       ; unit⊕X = unit-sum
       ; comm⊕X = comm-sum 
       ; assoc⊕X = assoc-sum
       ; unit∣∣X = unit-par
       ; comm∣∣X = λ {_}{P} → comm-par {p = P}
       ; assoc∣∣X = λ {_}{P} → assoc-par {P = P} 
       ; replX = λ {_}{P} → repl-par {P = P}
       ; ν∣∣X = ν-par
       ; swapνX = ν-swap 
       ; νendX = ν-end
       }

ProcStructCong : StructCong ProcCCS-alg (mapProc-Inj _ _) _≡_
ProcStructCong = fix ProcStructCongF


              

