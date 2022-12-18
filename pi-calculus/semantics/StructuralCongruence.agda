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

module pi-calculus.semantics.StructuralCongruence (ns : Names) where

open Names ns
open OpNames ns
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import pi-calculus.Syntax ns
open import pi-calculus.Algebra ns
open import pi-calculus.semantics.Algebra ns
open import pi-calculus.semantics.MapProcLemmata ns

open StepLemmata Proc (\ α n → ProcPi-alg n) (mapProc _ _)
open Synch'

-- Path equality on Proc appropriately models structural congruence on
-- Pi-terms. In other words, we can show that equality is a
-- "StructCong" for the Pi-algebra of processes. This is proved by
-- guarded recursion.

module _ (ih : ▹ StructCong ProcPi-alg (mapProc _ _) _≡_) where
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
    cong′ (λ x → isPi-alg.parX (x n) P (isPi-alg.endX (x n))) (fix-eq ProcPi-algF)
    ∙ cong Fold (cong₂ _∪_ (unit _) (bind-ø (Unfold P))
                ∙ unit _
                ∙ cong′ (λ x → mapP∞ x (Unfold P))
                        (funExt (λ _ → StepPath refl refl
                                                (later-ext (λ α → cong₂ parProc refl (cong′ Fold (mapProc'-eq' _ _ _ _))
                                                 ∙ ih α .unit∣∣X ))))
                ∙ mapidP∞ _)

-- Commutativity of parProc.
  comm-synchF : ∀ {n} {p q : F' n (next Proc)} → synchF p q ≡ synchF q p
  comm-synchF {n}{P}{Q} =
    cong (bind P) (funExt (λ P' → bind-∪ _ _ Q))
    ∙ bind-∪ _ _ P
    ∙ cong₂ _∪_ (bind-comm _ P Q ∙ cong (bind Q) (funExt (λ Q' →
                  cong (bind P) (funExt (λ P' → 
                    cong (λ (x : ▹ (∀ n → Proc n → Proc n → Proc n)) → synch' (λ α → x α _) (λ _ → νProc) P' Q')
                                                     (later-ext (λ α → funExt λ n → funExt (λ q → funExt λ q' → ih α .comm∣∣X {P = q}))))))))
                (sym (bind-comm _ Q P ∙ cong (bind P) (funExt (λ P' →
                  cong (bind Q) (funExt (λ Q' → cong (λ (x : ▹ (∀ n → Proc n → Proc n → Proc n)) → synch' (λ α → x α _) (λ _ → νProc) Q' P')
                                                     (later-ext (λ α → funExt λ n → funExt (λ q → funExt λ q' → ih α .comm∣∣X {P = q}))))))))) 
    ∙ comm _ _
    ∙ sym (bind-∪ _ _ Q)
    ∙ sym (cong (bind Q) (funExt (λ Q' → bind-∪ _ _ P)))

  comm-par : ∀ {n} {p q : Proc n} → parProc p q ≡ parProc q p
  comm-par {n}{P}{Q} =
    cong′ (λ x → isPi-alg.parX (x n) P Q) (fix-eq ProcPi-algF)
    ∙ cong Fold (cong₂ _∪_ ((cong₂ _∪_
        (cong′ (λ f → mapP∞ f (Unfold P)) (funExt (λ x → StepPath refl refl (later-ext (λ α → ih α .comm∣∣X {_}{_}{mapProc _ _ (fst (labelInj (theLabel x))) Q})))))
        (cong′ (λ f → mapP∞ f (Unfold Q)) (funExt (λ x → StepPath refl refl (later-ext (λ α → ih α .comm∣∣X {_}{mapProc _ _ (fst (labelInj (theLabel x))) P})))))) ∙ comm _ _)
        (comm-synchF {_}{Unfold P}{Unfold Q}))
    ∙ cong′ (λ x → isPi-alg.parX (x n) Q P) (sym (fix-eq ProcPi-algF))

-- Associativity of parProc (which requires many lemmata)..
  step-LR : ∀ {n} P Q R →
    stepL {n} (stepR P Q) R ≡ stepR P (stepL Q R)
  step-LR P Q R =
    mapmapP∞ _ _ Q
    ∙ cong′ (λ f → mapP∞ f Q) (funExt (λ { (a , P') →
        StepPath refl refl (later-ext (λ α → ih α .assoc∣∣X {P = Fold (mapProc' _ _ _ _)}))}))
          ∙ sym (mapmapP∞ _ _ Q)

  step-RR : ∀ {n} P Q R →
    stepR {n} P (stepR Q R) ≡ stepR (parProc P Q) R
  step-RR P Q R =
    mapmapP∞ _ _ R
    ∙ sym (cong′ (λ f → mapP∞ f R) (funExt (λ { (a , R') →
        StepPath refl refl (later-ext (λ α → cong₂ parProc (par-map _ _ (labelInj a) _ _) refl
          ∙ ih α .assoc∣∣X {P = Fold (mapProc' _ _ _ _)}))})))

  stepL-synch'-L : ∀ {n} (aP aQ : Step (\ n → ▹ Proc n) n) R →
    stepL (synch' (λ _ → parProc) (λ _ → νProc) aP aQ) R
      ≡ synch' (λ _ → parProc) (λ _ → νProc) aP (mapStep (\ m i Q' α → parProc (Q' α) (mapProc _ _ (i .fst) R)) aQ)
  stepL-synch'-L P@(a , _) Q@(b , _) R with canSynchL? a b
  stepL-synch'-L (.(out _ _) , P') (.(inp _ _) , Q') R | local r r' = 
    cong η (StepPath refl refl (later-ext (λ α → ih α .assoc∣∣X {P = P' α})))
  stepL-synch'-L (.(bout _) , P') (.(binp _) , Q') R | bound refl' =
    cong η (StepPath refl refl (later-ext (λ α → cong₂ parProc refl (mapProc-id _ _)
      ∙ sym (ih α .ν∣∣X) ∙ cong′ νProc (ih α .assoc∣∣X {P = P' α}{Q' α}))))
  stepL-synch'-L (a , _) (b , _) R | nope = refl

  stepL-synch'-R : ∀ {n} (aP aQ : Step (\ n → ▹ Proc n) n) R →
    stepL (synch' (λ _ p q → parProc q p) (λ _ → νProc) aP aQ) R
      ≡ synch' (λ _ p q → parProc q p) (λ _ → νProc) (mapStep (\ m i Q' α → parProc (Q' α) (mapProc _ _ (i .fst) R)) aP) aQ
  stepL-synch'-R (a , P) (b , Q) R with canSynchL? a b
  stepL-synch'-R (.(out _ _) , P) (.(inp _ _) , Q) R | local r r' =
    cong η (StepPath refl refl (later-ext (λ α → ih α .assoc∣∣X {P = Q α})))
  stepL-synch'-R (.(bout _) , P) (.(binp _) , Q) R | bound refl' =
    cong η (StepPath refl refl (later-ext (λ α → cong₂ parProc refl (mapProc-id _ _)
            ∙ sym (ih α .ν∣∣X)
            ∙ cong′ νProc (ih α .assoc∣∣X {P = Q α}{P α}))))
  stepL-synch'-R (a , P) (b , Q) R | nope = refl

  stepR-synch'-L : ∀ {n} P (aQ aR : Step (\ n → ▹ Proc n) n) →
    stepR P (synch' (λ _ → parProc) (λ _ → νProc) aQ aR)
    ≡ synch' (λ _ → parProc) (λ _ → νProc) (mapStep (\ m i Q' α → parProc (mapProc _ _ (i .fst) P) (Q' α)) aQ) aR
  stepR-synch'-L R (a , P) (b , Q) with canSynchL? a b
  ... | local r r' =
    cong η (StepPath refl refl (later-ext (λ α → sym (ih α .assoc∣∣X {P = Fold (mapProc' _ _ _ _)}))))
  ... | bound r =
    cong η (StepPath refl refl (later-ext (λ α → 
                    cong₂ parProc (mapProc-id _ _) refl
                    ∙ ih α .comm∣∣X {P = R}
                    ∙ sym (ih α .ν∣∣X)
                    ∙ cong′ νProc (ih α .comm∣∣X {Q = Fold (mapProc' _ _ _ _)}
                            ∙ sym (ih α .assoc∣∣X {P = Fold (mapProc' _ _ _ _)})))))
  ... | nope = refl

  stepR-synch'-R : ∀ {n} P (aQ aR : Step (\ n → ▹ Proc n) n) →
      stepR P (synch' (λ _ p q → parProc q p) (λ _ → νProc) aQ aR)
      ≡ synch' (λ _ p q → parProc q p) (λ _ → νProc) aQ (mapStep (\ m i Q' α → parProc (mapProc _ _ (i .fst) P) (Q' α)) aR)
  stepR-synch'-R P (a , Q) (b , R) with canSynchL? a b
  ... | local r r' =
    cong η (StepPath refl refl (later-ext (λ α → sym (ih α .assoc∣∣X {P = Fold (mapProc' _ _ _ _)}))))
  ... | bound r =
    cong η (StepPath refl refl (later-ext (λ α →
                    cong₂ parProc (mapProc-id _ _) refl
                    ∙ ih α .comm∣∣X {P = P}
                    ∙ sym (ih α .ν∣∣X)
                    ∙ cong′ νProc (ih α .comm∣∣X {Q = Fold (mapProc' _ _ _ _)}
                            ∙ sym (ih α .assoc∣∣X {P = Fold (mapProc' _ _ _ _)})))))
  ... | nope = refl

  synch'-assoc : ∀ {n} (aP : Step (\ n → ▹ Proc n) n) Q aR →
    synch' (λ _ → parProc) (λ _ → νProc) (mapStep (λ m i P' α → parProc (P' α) (mapProc n m (i .fst) Q)) aP) aR
    ≡ synch' (λ _ → parProc) (λ _ → νProc) aP (mapStep (λ m i R' α → parProc (mapProc n m (i .fst) Q) (R' α)) aR)
  synch'-assoc (a , P) Q (b , R) with canSynchL? a b
  ... | local r r' = cong η (StepPath refl refl (later-ext (λ α → ih α .assoc∣∣X {P = P α})))
  ... | bound r = cong η (StepPath refl refl (later-ext (λ α → cong′ νProc (ih α .assoc∣∣X {P = P α}))))
  ... | nope = refl

  synch'-assoc' : ∀ {n} (aP : Step (\ n → ▹ Proc n) n) aQ aR →
    bind (synch' (λ _ → parProc) (λ _ → νProc) aP aQ)
         (λ z → synch' (λ _ → parProc) (λ _ → νProc) z aR)
    ≡ bind (synch' (λ _ → parProc) (λ _ → νProc) aQ aR)
           (synch' (λ _ → parProc) (λ _ → νProc) aP)
  synch'-assoc' (a , P) (b , Q) (c , R) with canSynchL? a b
  ... | local r r' = refl
  ... | bound r = refl
  synch'-assoc' (a , P) (b , Q) (c , R) | nope with canSynchL? b c
  synch'-assoc' (a , P) (b , Q) (c , R) | nope | local r r' with canSynchL? a τ
  synch'-assoc' (a , P) (.(out _ _) , Q) (.(inp _ _) , R) | nope | local r r' | nope = refl
  synch'-assoc' (a , P) (b , Q) (c , R) | nope | bound r with canSynchL? a τ
  synch'-assoc' (a , P) (b , Q) (c , R) | nope | bound r | nope = refl
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
            (cong′ (λ (f : ▹ (∀ n → Proc n → Proc n → Proc n)) → synch' (λ α {n} → f α n) (λ _ → νProc) aR' (mapStep (λ m i P' α → parProc (P' α) (mapProc _ m (i .fst) Q)) aP'))
              (later-ext (λ α → funExt (λ _ → funExt (λ p → (funExt (λ q → ih α .comm∣∣X {P = q}))))))
             ∙ cong′ (synch' (λ _ → parProc) (λ _ → νProc) aR') (StepPath refl refl (later-ext (λ α → ih α .comm∣∣X {P = theX aP' α})))
             ∙ sym (synch'-assoc aR' Q aP')
             ∙ cong′ (λ x → synch' (λ _ → parProc) (λ _ → νProc) x aP') {y = mapStep (λ m i R' α → parProc (mapProc _ m (i .fst) Q) (R' α)) aR'} (StepPath refl refl (later-ext (λ α → ih α .comm∣∣X {P = theX aR' α})))
             ∙ cong′ (λ (f : ▹ (∀ n → Proc n → Proc n → Proc n)) → synch' (λ α {n} → f α n) (λ _ → νProc) (mapStep (λ m i R' α → parProc (mapProc _ m (i .fst) Q) (R' α)) aR') aP')
                (later-ext (λ α → funExt (λ _ → funExt (λ p → (funExt (λ q → ih α .comm∣∣X {P = p})))))))))
        ∙ sym (bind-map R _ _)))

  synch'synch'1 : ∀ {n} a b c (f g : ▹ (∀ {n} → Proc n → Proc n → Proc n))
    → bind (synch' f (λ _ → νProc) {n} b c) (synch' g (λ _ → νProc) a) ≡ ø
  synch'synch'1 (a , P) (b , Q) (c , R) f g with canSynchL? b c
  synch'synch'1 (a , P) (.(out _ _) , Q) (.(inp _ _) , R) f g | local x x₁ with canSynchL? a τ
  ... |  nope = refl
  synch'synch'1 (a , P) (.(bout _) , Q) (.(binp _) , R) f g | bound x with canSynchL? a τ
  ...| nope = refl
  synch'synch'1 (a , P) (b , Q) (c , R) f g | nope = refl

  synch'synch'2 : ∀ {n} a b c (f g : ▹ (∀ {n} → Proc n → Proc n → Proc n))
    → bind (synch' f (λ _ → νProc) {n} b c) (\ v → synch' g (λ _ → νProc) v a) ≡ ø
  synch'synch'2 (a , P) (b , Q) (c , R) f g with canSynchL? b c
  synch'synch'2 (a , P) (.(out _ _) , Q) (.(inp _ _) , R) f g | local x x₁ with canSynchL? a τ
  ... |  nope = refl
  synch'synch'2 (a , P) (.(bout _) , Q) (.(binp _) , R) f g | bound x with canSynchL? a τ
  ...| nope = refl
  synch'synch'2 (a , P) (b , Q) (c , R) f g | nope = refl

  synchsynch : ∀ {n} b' c' a' → bind (synch {n} b' c') (synch a') ≡ ø
  synchsynch b c a = (bind (synch' (λ _ → parProc) (λ _ → νProc) b c) (synch a) ∪ bind (synch' _ _ c b) (synch a) )
                   ≡⟨ bind-∪ _ _ (synch b c)  ⟩
                   (bind (synch' (λ _ →  parProc) (λ _ → νProc) b c) (synch' (λ _ → parProc) (λ _ → νProc) a) ∪ bind (synch' _ _ c b) (synch' _ _ a))
                    ∪ (bind (synch' (λ _ → parProc) (λ _ → νProc) b c) (\ bc → synch' _ _ bc a) ∪ bind (synch' _ _ c b) (\ bc → synch' _ _ bc a))
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
        StepPath refl refl (later-ext (λ α →  ih α .assoc∣∣X {P = P' α} ∙ cong₂ parProc refl (sym (par-map _ _ (labelInj a) Q R))))}))

  assoc-synchF : ∀ {n} (P : F' n (\ _ → Proc)) Q R →
    synchF (synchF P Q) R ≡ synchF P (synchF Q R)
  assoc-synchF P Q R = comm-synchF {p = synchF P Q} {R} ∙ synchsynchF R P Q ∙ sym (synchsynchF P Q R)

  assoc-par : ∀ {n} {P Q R : Proc n} → parProc (parProc P Q) R ≡ parProc P (parProc Q R)
  assoc-par {n}{P}{Q}{R} =
   cong₂ parProc (cong′ (λ x → isPi-alg.parX (x n) P Q) (fix-eq ProcPi-algF)) refl
   ∙ cong′ (λ x → isPi-alg.parX (x n) (isPi-alg.parX (fix-eq ProcPi-algF i1 n) P Q) R) (fix-eq ProcPi-algF)
   ∙ cong Fold (sym (assoc _ _ _ ∙ assoc _ _ _ ∙ assoc _ _ _)
                ∙ cong₂ _∪_
                    (step-LL (Unfold P) Q R
                     ∙ cong′ (λ f → mapP∞ f (Unfold P)) (funExt (λ P' →
                         StepPath refl refl (later-ext (λ α → cong₂ parProc refl (cong′ (mapProc _ _ _) (cong′ (λ x → isPi-alg.parX (x n) Q R) (fix-eq ProcPi-algF))))))))
                    (cong₂ _∪_ (step-LR P (Unfold Q) R)
                      (comm _ _ ∙ sym (assoc _ _ _)
                       ∙ cong₂ _∪_
                           (sym (step-RR P Q (Unfold R)
                            ∙ cong′ (λ f → mapP∞ f (Unfold R)) (funExt (λ R' →
                             StepPath refl refl (later-ext (λ α → cong₂ parProc (cong′ (mapProc _ _ _) (cong′ (λ x → isPi-alg.parX (x n) P Q) (fix-eq ProcPi-algF))) refl))))))
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
                            ∙ cong₂ _∪_ refl (bind-comm _ (Unfold (isPi-alg.parX (fix-eq ProcPi-algF i1 n) Q R)) (Unfold P))))
                     ∙ assoc _ _ _ ∙ assoc _ _ _)
                ∙ assoc _ _ _)
   ∙ sym (cong′ (λ x → isPi-alg.parX (x n) P (isPi-alg.parX (fix-eq ProcPi-algF i1 n) Q R)) (fix-eq ProcPi-algF))
   ∙ sym (cong₂ parProc refl (cong′ (λ x → isPi-alg.parX (x n) Q R) (fix-eq ProcPi-algF)))

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
    cong₂ mapP∞ (funExt (λ aP' → StepPath refl refl (later-ext (λ α → ih α .comm∣∣X {P = Fold (mapProc' _ _ _ _)})))) (refl {x = Unfold (!Proc P)})
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
    ∙ cong′ (λ x → isPi-alg.parX (x _) P (isPi-alg.!X (fix-eq ProcPi-algF i0 _) P)) (sym (fix-eq ProcPi-algF))

-- Restriction of the nil process.
  ν-end : ∀ {n} → νProc endProc ≡ endProc {n}
  ν-end = refl

-- The equation relating restriction and parallel composition (plus
-- many required lemmata).
  ν-stepL' : ∀ {n} aP Q → stepν (mapStep (λ m i P' α → parProc (P' α) (mapProc _ _ (i .fst) (mapProc _ _ ι Q))) aP) ≡ stepL {n} (stepν aP) Q
  ν-stepL' (a , P) Q with canNu? a
  ν-stepL' (.(out _ _) , P) Q | out x x₁ = cong η (StepPath refl refl (later-ext (λ α →
      cong′ νProc (cong₂ parProc refl (mapProc-id _ _)) ∙ ih α .ν∣∣X ∙ cong₂ parProc refl (sym (mapProc-id _ _)))))

  ν-stepL' (.(out _ _) , P) Q | out2 x x₁ = cong η (StepPath refl refl (later-ext (λ α → cong₂ parProc refl (mapProc-id _ _))))
  ν-stepL' (.(inp _ _) , P) Q | inp x x₁ =
    cong η (StepPath refl refl (later-ext (λ α →
      cong′ νProc (cong₂ parProc refl (mapProc-id _ _)) ∙ ih α .ν∣∣X ∙ cong₂ parProc refl (sym (mapProc-id _ _)))))
  ν-stepL' (.(bout _) , P) Q | bout x =
    cong η (StepPath refl refl (later-ext (λ α →
      cong νProc (par-map _ _ (swap , swap-inj) _ _)
      ∙ cong νProc (cong₂ parProc refl
          (mapmapProc _ _ _ (_ , swap-inj) (_ , ι-inj) _
           ∙ mapmapProc _ _ _ (_ , \ x y p → ι-inj _ _ (swap-inj _ _ p)) (_ , ι-inj) _
           ∙ cong′ (λ x → mapProc _ _ x Q) (funExt swap-ιι)
           ∙ sym (mapmapProc _ _ _ (_ , ι-inj) (_ , ι-inj) _)))
      ∙ ih α .ν∣∣X)))
  ν-stepL' (.(binp _) , P) Q | binp x =
    cong η (StepPath refl refl (later-ext (λ α →
      cong νProc (par-map _ _ (swap , swap-inj) _ _)
      ∙ cong νProc (cong₂ parProc refl
          (mapmapProc _ _ _ (_ , swap-inj) (_ , ι-inj) _
           ∙ mapmapProc _ _ _ (_ , \ x y p → ι-inj _ _ (swap-inj _ _ p)) (_ , ι-inj) _
           ∙ cong′ (λ x → mapProc _ _ x Q) (funExt swap-ιι)
           ∙ sym (mapmapProc _ _ _ (_ , ι-inj) (_ , ι-inj) _)))
      ∙ ih α .ν∣∣X)))
  ν-stepL' (.τ , P) Q | τ = cong η (StepPath refl refl (later-ext (λ α →
    cong′ νProc (cong₂ parProc refl (mapProc-id _ _)) ∙ ih α .ν∣∣X ∙ cong₂ parProc refl (sym (mapProc-id _ _)))))
  ν-stepL' (a , P) Q | nope x = refl

  ν-stepL : ∀ {m P Q} →
    νProc (Fold (stepL (Unfold P) (mapProc m _ ι Q)))
    ≡ Fold (stepL (Unfold (νProc P)) Q)
  ν-stepL {n}{P}{Q} =
    cong′ (λ x → isPi-alg.νX (x _) (Fold (stepL (Unfold P) (mapProc n _ ι Q)))) (fix-eq ProcPi-algF)
    ∙ cong Fold
        (bind-map (Unfold P) _ _
         ∙ cong (bind (Unfold P)) (funExt (λ aP' → ν-stepL' aP' Q))
         ∙ sym (map-bind (Unfold P) _ _))
    ∙ cong′ (λ x → Fold (stepL (Unfold (isPi-alg.νX (x _) P)) Q)) (sym (fix-eq ProcPi-algF))

  ν-stepR' : ∀ {n} P aQ →
    bind (mapSProc n _ ι aQ) (λ v → stepν (mapStep (λ m i x α → parProc (mapProc _ _ (fst i) P) (x α)) v))
    ≡ η (mapStep (λ m i x α → parProc (mapProc _ _ (fst i) (νProc P)) (x α)) aQ)
  ν-stepR' P (`out ch z Q) with decName (ι ch) (fresh _) | decName (ι z) (fresh _)
  ν-stepR' P (`out ch z Q) | yes p | _ = ⊥-rec (fresh-ι p)
  ν-stepR' P (`out ch z Q) | no p | yes q = ⊥-rec (fresh-ι q)
  ν-stepR' P (`out ch z Q) | no p | no q =
    cong η (StepPath refl (λ i → out (down-ι p i) (down-ι q i)) (later-ext (λ α → ih α .ν∣∣X ∙ cong₂ parProc (cong νProc (mapProc-id _ _) ∙ sym (mapProc-id _ _)) refl)))
  ν-stepR' P (`bout ch Q) with decName (ι ch) (fresh _)
  ν-stepR' P (`bout ch Q) | yes p = ⊥-rec (fresh-ι p)
  ν-stepR' P (`bout ch Q) | no p =
    cong η (StepPath refl (cong′ bout (down-ι p))
      (later-ext (λ α → cong′ νProc (par-map _ _ (_ , swap-inj) _ _
                                  ∙ cong₂ parProc (mapmapProc _ _ _ (_ , swap-inj) (_ , ι-inj) _ ∙ cong₂ (mapProc _ _) (funExt swap-ι-lift) refl)
                                               (mapmapProc _ _ _ (_ , swap-inj) (_ , lift-inj (_ , ι-inj)) _ ∙ cong₂ (mapProc _ _) (funExt swap-lift-ι) refl))
                         ∙ ih α .ν∣∣X
                         ∙ cong₂ parProc (sym (ν-map _ _ (_ , ι-inj) P)) refl)))
  ν-stepR' P (`inp ch v Q) with decName (ι ch) (fresh _) | decName (ι v) (fresh _)
  ν-stepR' P (`inp ch v Q) | yes p | _ = ⊥-rec (fresh-ι p)
  ν-stepR' P (`inp ch v Q) | no p | yes q = ⊥-rec (fresh-ι q)
  ν-stepR' P (`inp ch v Q) | no p | no q =
    cong η (StepPath refl (λ i → inp (down-ι p i) (down-ι q i)) (later-ext (λ α → ih α .ν∣∣X ∙ cong₂ parProc (cong′ νProc (mapProc-id _ _) ∙ sym (mapProc-id _ _)) refl)))
  ν-stepR' P (`binp ch Q) with decName (ι ch) (fresh _)
  ν-stepR' P (`binp ch Q) | yes p = ⊥-rec (fresh-ι p)
  ν-stepR' {n} P (`binp ch Q) | no p =
    cong₂ _∪_
      (cong η (StepPath refl (cong′ binp (down-ι p))
        (later-ext (λ α → cong′ νProc (par-map _ _ (_ , swap-inj) _ _
                                    ∙ cong₂ parProc (mapmapProc _ _ _ (_ , swap-inj) (_ , ι-inj) _ ∙ cong₂ (mapProc _ _) (funExt swap-ι-lift) refl)
                                                 (mapmapProc _ _ _ (_ , swap-inj) (_ , lift-inj (_ , ι-inj)) _ ∙ cong₂ (mapProc _ _) (funExt swap-lift-ι) refl))
                           ∙ ih α .ν∣∣X
                           ∙ cong₂ parProc (sym (ν-map _ _ (_ , ι-inj) P)) refl))))
      (cong₂ bind (inps-ι ch Q) refl ∙ aux)
    ∙ unit _
    where
      aux : stepν (`inp (ι ch) (fresh n) λ α → parProc (mapProc _ _ (λ x → x) P) (Fold (mapProc' _ _ (snoc ι (fresh n)) (Unfold (Q α))))) ≡ ø
      aux with canNu? (inp (ι ch) (fresh n))
      aux | inp x x₁ = ⊥-rec (fresh-ι (sym x₁))
      aux | nope x = refl
  ν-stepR' P (`τ Q) =
    cong η (cong′ `τ (later-ext (λ α → ih α .ν∣∣X ∙ cong₂ parProc (cong νProc (mapProc-id _ _) ∙ sym (mapProc-id _ _)) refl)))

  ν-stepR : ∀ {m P Q} → νProc (Fold (stepR P (Unfold (mapProc m _ ι Q)))) ≡ Fold (stepR (νProc P) (Unfold Q))
  ν-stepR {m} {P} {Q} =
    cong′ νProc (cong′ Fold (cong′ (stepR P) (mapProc'-eq' _ _ _ _)))
    ∙ cong′ (λ x → isPi-alg.νX (x _) (Fold (stepR P (mapProcF (next mapProc') m (suc m) ι (Unfold Q))))) (fix-eq ProcPi-algF)
    ∙ cong Fold (bind-map (mapProcF (next mapProc') m (suc m) ι (Unfold Q)) _ _
                 ∙ bind-bind (Unfold Q) _ _
                 ∙ cong (bind (Unfold Q)) (funExt (ν-stepR' P))
                 ∙ sym (mapP∞-is-bind (Unfold Q)))

  no-bout : ∀ {n} {ch : Name (suc n)} {ch'} P Q → bind (inps' (λ _ → mapProc') ι ch' Q) (synch' (λ _ → parProc) (λ _ → νProc) (`bout ch P)) ≡ ø
  no-bout P Q = cong₂ bind (inps'-eq (\ _ → mapProc') ι _ Q) refl ∙ bind-bind (neg (image ι) (image-fn _)) _ _ ∙ bind-ø (neg (image ι) (image-fn _))

  no-out : ∀ {n} {ch' : Name n} {ch : Name (suc n)} {z : Name (suc n)} P Q → (ch ≡ ι ch' → z ≡ fresh n → ⊥)
    → bind (inps' (λ _ → mapProc') ι ch' Q) (synch' (λ _ → parProc) (λ _ → νProc) (`out ch z P)) ≡ ø
  no-out {_} {ch'} {ch} {z} P Q p = cong₂ bind (inps'-eq (\ _ → mapProc') ι _ Q) refl
               ∙ bind-bind (neg (image ι) (image-fn _)) _ _ ∙ cong₂ bind neg-image-ι refl
               ∙ no-synch'-out-inp (λ _ → parProc) (λ _ → νProc) _ _ p

  ν-synch' : ∀ {n} aP aQ
    → bind (mapSProc n _ ι aQ) (λ v → bind (synch' (λ _ → parProc) (λ _ → νProc) aP v) stepν)
         ≡ bind (stepν aP) (λ z → synch' (λ _ → parProc) (λ _ → νProc) z aQ)
  ν-synch' (`out ch z P) (`out ch' z' Q) with canNu? (out ch z)
  ν-synch' (`out ch z P) (`out ch' z' Q) | out _ _ = refl
  ν-synch' (`out ch z P) (`out ch' z' Q) | out2 _ _ = refl
  ν-synch' (`out ch z P) (`out ch' z' Q) | nope _ = refl
  ν-synch' (`out ch z P) (`bout ch' Q) with canNu? (out ch z)
  ν-synch' (`out ch z P) (`bout ch' Q) | out _ _ = refl
  ν-synch' (`out ch z P) (`bout ch' Q) | out2 _ _ = refl
  ν-synch' (`out ch z P) (`bout ch' Q) | nope _ = refl
  ν-synch' (`out ch z P) (`inp ch' v' Q) with decName ch (ι ch') | decName z (ι v') | canNu? (out ch z)
  ν-synch' (`out ch z P) (`inp ch' v' Q) | yes p | yes p₂ | out r r'
    =  cong η (StepPath refl refl (later-ext λ α → ih α .ν∣∣X))
      ∙ sym (synch'-out-inp (λ _ → parProc) (λ _ → νProc) _ Q (ι-inj _ _ (sym r ∙ p)) (ι-inj _ _ (sym r' ∙ p₂)))
  ν-synch' (`out ch z P) (`inp ch' v' Q) | no ¬p | _ | out r r'
    = sym (no-synch'-out-inp (λ _ → parProc) (λ _ → νProc) _ Q λ p p' → ¬p (r ∙ cong ι p))
  ν-synch' (`out ch z P) (`inp ch' v' Q) | yes p | no ¬r | out r r'
    = sym (no-synch'-out-inp (λ _ → parProc) (λ _ → νProc) _ Q \ _ r → ¬r (r' ∙ cong ι r))
  ν-synch' (`out _ _ P) (`inp ch' v' Q) | yes p | yes p₁ | out2 r r' =
    ⊥-rec (fresh-ι (sym p₁ ∙ r')) 
  ν-synch' (`out _ _ P) (`inp ch' v' Q) | yes p | no ¬p | out2 r r' = refl
  ν-synch' (`out _ _ P) (`inp ch' v' Q) | no ¬p | z? | out2 r r' = refl
  ν-synch' (`out _ z P) (`inp ch' v' Q) | yes p | _ | nope (out r) = 
    ⊥-rec (fresh-ι (sym p ∙ r))
  ν-synch' (`out ch z P) (`inp ch' v' Q) | no ¬p | z? | nope x = refl
  ν-synch' (`out ch z P) (`binp ch' Q) with canNu? (out ch z)
  ν-synch' (`out ch z P) (`binp ch' Q) | out r r'
    = comm _ _ ∙ unit _
    ∙ sym (bind-bind (inps' (λ _ → mapProc') ι ch' Q) (synch' (λ _ → parProc) (λ _ → νProc) (`out ch z P)) stepν)
    ∙ cong₂ bind (no-out P Q λ p p' → fresh-ι (sym r' ∙ p')) refl 
  ν-synch' (`out ch z P) (`binp ch' Q) | out2 {ch = dch} r r' with decName dch ch'
  ν-synch' (`out ch z P) (`binp ch' Q) | out2 {ch = dch} r r' | yes p
    = comm _ _ ∙ unit _
    ∙ sym (bind-bind (inps' (λ _ → mapProc') ι ch' Q) (synch' (λ _ → parProc)  (λ _ → νProc)(`out ch z P)) stepν)
    ∙ (cong₂ bind (cong₂ bind (inps-ι ch' Q) refl) refl ∙ cong₂ bind (synch'-out-inp (λ _ → parProc) (λ _ → νProc) P _ (r ∙ cong ι p) r') refl)
    ∙ cong′ η (cong′ `τ (later-ext \ α → cong′ νProc (cong₂ parProc refl (cong₂ (mapProc _ _) (funExt snoc-ι-fresh) refl ∙ mapProc-id _ (Q _)))))
  ν-synch' (`out ch z P) (`binp ch' Q) | out2 {ch = dch} r r' | no ¬p
    = comm _ _ ∙ unit _ ∙ sym (bind-bind (inps' (λ _ → mapProc') ι ch' Q) (synch' (λ _ → parProc) (λ _ → νProc) (`out ch z P)) stepν)
    ∙ cong₂ bind (no-out P Q \ p _ → ¬p (ι-inj _ _ (sym r ∙ p))) refl
  ν-synch' (`out ch z P) (`binp ch' Q) | nope (out r) = comm _ _
                                                           ∙ unit _
                                                           ∙ sym (bind-bind (inps' (λ _ → mapProc') ι ch' Q) (synch' (λ _ → parProc) (λ _ → νProc) (`out ch z P)) stepν)
                                                           ∙ cong₂ bind (no-out P Q \ p _ → fresh-ι (sym p ∙ r)) refl
  ν-synch' (`bout ch P) (`binp ch' Q) with canNu? (bout ch) | decName ch (ι ch')
  ν-synch' (`bout ch P) (`binp ch' Q) | bout {_} {dch} r | yes p with decName dch ch'
  ν-synch' (`bout _ P) (`binp ch' Q) | bout {_} {dch} r | yes p | yes p₁
    = cong₂ _∪_ (cong′ η (cong′ `τ (later-ext \ α → (ih α .swapνX ∙ cong′ νProc (cong′ νProc (par-map _ _ (swap , swap-inj) (P α) _ ∙ cong₂ parProc refl
                       (mapmapProc _ _ _ (_ , swap-inj) (_ , lift-inj (_ , ι-inj)) (Q α)
                        ∙ λ i → mapProc _ _ (funExt swap-lift-ι i) (Q α))))) 
         ∙ cong′ νProc (ih α .ν∣∣X {P = Fold (mapProc' _ _ _ _)}))))
                (sym (bind-bind (inps' (λ _ → mapProc') ι ch' Q) _ _)
                 ∙ cong₂ bind (no-bout P Q) refl)
    ∙ unit _
  ν-synch' (`bout _ P) (`binp ch' Q) | bout {_} {dch} r | yes p | no ¬p = 
    ⊥-rec (¬p (ι-inj _ _ (sym r ∙ p)))
  ν-synch' (`bout ch P) (`binp ch' Q) | bout {_} {dch} r | no ¬p with decName dch ch'
  ν-synch' (`bout _ P) (`binp ch' Q) | bout {_} {dch} r | no ¬p | yes p = 
    ⊥-rec (¬p (r ∙ cong ι p))
  ν-synch' (`bout _ P) (`binp ch' Q) | bout {_} {dch} r | no ¬p | no ¬p₁ =
    comm _ _ ∙ unit _
                  ∙ sym (bind-bind (inps' (λ _ → mapProc') ι ch' Q) _ _)
                  ∙ cong₂ bind (no-bout P Q) refl
  ν-synch' (`bout _ P) (`binp ch' Q) | nope (bout r) | yes p = ⊥-rec (fresh-ι (sym p ∙ r))
  ν-synch' (`bout ch P) (`binp ch' Q) | nope x | no ¬p = comm _ _ ∙ unit _
                  ∙ sym (bind-bind (inps' (λ _ → mapProc') ι ch' Q) _ _)
                  ∙ cong₂ bind (no-bout P Q) refl
  ν-synch' (`out ch z P) (`τ Q) with canNu? (out ch z)
  ν-synch' (`out ch z P) (`τ Q) | out x x₁ = refl
  ν-synch' (`out ch z P) (`τ Q) | out2 x x₁ = refl
  ν-synch' (`out ch z P) (`τ Q) | nope x = refl
  ν-synch' (`bout ch P) (`out ch' z' Q) with canNu? (bout ch)
  ν-synch' (`bout ch P) (`out ch' z' Q) | bout x = refl
  ν-synch' (`bout ch P) (`out ch' z' Q) | nope x = refl
  ν-synch' (`bout ch P) (`bout ch' Q) with canNu? (bout ch)
  ν-synch' (`bout ch P) (`bout ch' Q) | bout x = refl
  ν-synch' (`bout ch P) (`bout ch' Q) | nope x = refl
  ν-synch' (`bout ch P) (`inp ch' v' Q) with canNu? (bout ch)
  ν-synch' (`bout ch P) (`inp ch' v' Q) | bout x = refl
  ν-synch' (`bout ch P) (`inp ch' v' Q) | nope x = refl
  ν-synch' (`bout ch P) (`τ Q) with canNu? (bout ch)
  ν-synch' (`bout ch P) (`τ Q) | bout x = refl
  ν-synch' (`bout ch P) (`τ Q) | nope x = refl
  ν-synch' (`inp ch v P) x with canNu? (inp ch v)
  ν-synch' (`inp ch v P) (a , Q) | inp r r' = bind-ø (mapSProc _ _ ι (a , Q))
  ν-synch' (`inp ch v P) (a , Q) | nope x₁ = bind-ø (mapSProc _ _ ι (a , Q))
  ν-synch' (`binp ch P) x with canNu? (binp ch)
  ν-synch' (`binp ch P) x | binp x₁ = bind-ø (mapSProc _ _ ι x)
  ν-synch' (`binp ch P) x | nope x₁ = bind-ø (mapSProc _ _ ι x)
  ν-synch' (`τ P) aQ = bind-ø (mapSProc _ _ ι aQ)

  ν-synch'2 : ∀ {n} aP aQ →
    bind (mapSProc n _ ι aQ) (λ v → bind (synch' (next \ p q → parProc q p) (λ _ → νProc) v aP) stepν)
      ≡ bind (stepν aP) (λ z → synch' (next \ p q → parProc q p)  (λ _ → νProc) aQ z)
  ν-synch'2 (a , P) (τ , Q) = sym (bind-ø (stepν (a , P)))
  ν-synch'2 (a , P) (inp _ _ , Q) = sym (bind-ø (stepν (a , P)))
  ν-synch'2 (a , P) (binp _ , Q) = (cong₂ _∪_ refl (cong₂ bind (inps-ι _ Q) refl) ∙ idem _) ∙  sym (bind-ø (stepν (a , P)))
  ν-synch'2 (a , P) (`out ch z Q) with canNu? a
  ν-synch'2 (.(out _ _) , P) (`out ch z Q) | out r r' = refl
  ν-synch'2 (.(out _ _) , P) (`out ch z Q) | out2 r r' = refl
  ν-synch'2 (.(inp _ _) , P) (`out ch z Q) | inp {_} {_} {ch'} {z'} r r'
    with decName ch ch' | decName z z'
  ... | no ¬p | _ = cong₂ bind (no-synch'-out-inp _ _ _ _ \ p _ → ¬p (ι-inj _ _ (p ∙ r))) refl
  ... | yes p | no ¬r = cong₂ bind (no-synch'-out-inp _ _ _ _ \ _ r → ¬r (ι-inj _ _ (r ∙ r'))) refl
  ... | yes p | yes p' = cong₂ bind (synch'-out-inp _ _ _ _ (cong ι p ∙ sym r) (cong ι p' ∙ sym r')) refl ∙ cong′ η (cong′ `τ (later-ext \ α → ih α .ν∣∣X)) 
  ν-synch'2 (.(bout _) , P) (`out ch z Q) | bout r = refl
  ν-synch'2 (.(binp _) , P) (`out ch z Q) | binp {_} {ch'} r = refl
  ν-synch'2 (.τ , P) (`out ch z Q) | τ = refl
  ν-synch'2 (.(out _ _) , P) (`out ch z Q) | nope (out x) = refl
  ν-synch'2 (.(inp _ _) , P) (`out ch z Q) | nope (inp (_⊎_.inl r)) = cong₂ bind (no-synch'-out-inp _ _ _ _ \ p _ → fresh-ι (p ∙ r)) refl 
  ν-synch'2 (.(inp _ _) , P) (`out ch z Q) | nope (inp (_⊎_.inr r)) = cong₂ bind (no-synch'-out-inp _ _ _ _ (\ _ p → fresh-ι (p ∙ r))) refl
  ν-synch'2 (.(bout _) , P) (`out ch z Q) | nope (bout x) = refl
  ν-synch'2 (.(binp _) , P) (`out ch z Q) | nope (binp x) = refl
  ν-synch'2 (a , P) (`bout ch Q) with canNu? a
  ν-synch'2 (.(out _ _) , P) (`bout ch Q) | out x x₁ = refl
  ν-synch'2 (.(out _ _) , P) (`bout ch Q) | out2 x x₁ = refl
  ν-synch'2 (.(inp _ _) , P) (`bout ch Q) | inp x x₁ = refl
  ν-synch'2 (.(bout _) , P) (`bout ch Q) | bout x = refl
  ν-synch'2 (.(binp _) , P) (`bout ch Q) | binp {_} {ch'} r with decName ch ch'
  ... | yes eq = 
    cong₂ bind (synch'-bout-binp _ _ _ P (cong ι eq ∙ sym r)) refl
    ∙ cong′ η (cong′ `τ (later-ext \ α →
        ih α .swapνX
        ∙ cong νProc (cong νProc (par-map _ _ (_ , swap-inj) _ _
                            ∙ cong₂ parProc refl
                                         (mapmapProc _ _ _ (_ , swap-inj) (_ , lift-inj (_ , ι-inj)) _
                                          ∙ cong₂ (mapProc _ _) (funExt swap-lift-ι) refl))
                   ∙ ih α .ν∣∣X)))
  ... | no ¬eq = cong₂ bind (no-synch'-bout-binp _ _ _ P \ eq → ¬eq (ι-inj _ _ (eq ∙ r))) refl
  ν-synch'2 (.τ , P) (`bout ch Q) | τ = refl
  ν-synch'2 (.(out _ _) , P) (`bout ch Q) | nope (out x) = refl
  ν-synch'2 (.(inp _ _) , P) (`bout ch Q) | nope (inp x) = refl
  ν-synch'2 (.(bout _) , P) (`bout ch Q) | nope (bout x) = refl
  ν-synch'2 (.(binp _) , P) (`bout ch Q) | nope (binp r) =
    cong₂ bind (no-synch'-bout-binp _ _ _ _ λ p → fresh-ι (p ∙ r)) refl

  ν-synchF : ∀ {m} P Q
    → νProc (Fold (synchF (Unfold P) (Unfold (mapProc m _ ι Q)))) ≡
         Fold (synchF (Unfold (νProc P)) (Unfold Q))
  ν-synchF {n} P Q =
    cong′ (λ x → isPi-alg.νX (x _) (Fold (synchF (Unfold P) (Unfold (mapProc _ _ ι Q))))) (fix-eq ProcPi-algF)
    ∙ cong Fold
        (bind-bind (Unfold P) _ _
         ∙ cong (bind (Unfold P)) (funExt (λ aP' →
             bind-bind (mapProc' n (suc n) ι (Unfold Q)) _ _
             ∙ cong₂ bind (mapProc'-eq' _ _ _ (Unfold Q)) refl
             ∙ bind-bind (Unfold Q) _ _
             ∙ cong (bind (Unfold Q)) (funExt (λ aQ' →
                 bind-∪ _ _ (inps (next mapProc') ι aQ' (η (mapLabel ι (theLabel aQ') , (λ α → Fold (next mapProc' α (theM aQ') (labelN (theLabel aQ') (suc n))
                                  (labelRen (theLabel aQ') (suc n) ι) (Unfold (theX aQ' α)))))))
                 ∙ cong₂ _∪_
                     (ν-synch' aP' aQ')
                     (ν-synch'2 aP' aQ')
                 ∙ sym (bind-∪ _ _ (stepν aP'))))
             ∙ bind-comm _ (Unfold Q) (stepν aP')))
         ∙ sym (bind-bind (Unfold P) _ _))
    ∙ cong′ (λ x → Fold (synchF (Unfold (isPi-alg.νX (x _) P)) (Unfold Q))) (sym (fix-eq ProcPi-algF))

  ν-par : ∀ {m P Q} → νProc (parProc P (mapProc m _ ι Q)) ≡ parProc (νProc P) Q
  ν-par {n}{P}{Q} =
    cong′ νProc (cong′ (λ x → isPi-alg.parX (x _) P (mapProc n _ ι Q)) (fix-eq ProcPi-algF))
    ∙ cong′ (λ x → isPi-alg.νX (x _) (isPi-alg.parX (fix-eq ProcPi-algF i1 _) P (mapProc n _ ι Q))) (fix-eq ProcPi-algF)
    ∙ cong Fold
        (cong₂ _∪_ (cong₂ _∪_
                      (cong Unfold (cong′ (λ x → isPi-alg.νX (x _) (Fold (stepL (Unfold P) (mapProc n _ ι Q)))) (sym (fix-eq ProcPi-algF)) ∙ ν-stepL {P = P}))
                      (cong Unfold (cong′ (λ x → isPi-alg.νX (x _) (Fold (stepR P (Unfold (mapProc n _ ι Q))))) (sym (fix-eq ProcPi-algF)) ∙ ν-stepR)))
                   (cong Unfold (cong′ (λ x → isPi-alg.νX (x _) (Fold (synchF (Unfold P) (Unfold (mapProc _ _ ι Q))))) (sym (fix-eq ProcPi-algF)) ∙ ν-synchF P Q)))
    ∙ cong′ (λ x → isPi-alg.parX (x n) (νProc P) Q) (sym (fix-eq ProcPi-algF))

-- The equation stating that the order in which a process is
-- restricted twice does not matter (again with some extra lemmata).

  lift-swap-Inj : ∀ {n} → Inj (suc (suc (suc n))) (suc (suc (suc n)))
  lift-swap-Inj =
    (\ x → lift swap (swap x)) ,
    \ _ _ eq → swap-inj _ _ (lift-inj (_ , swap-inj) _ _ eq)


  postulate
    stepν-swap : ∀ {n} (aP : Step (\ n → ▹ Proc n) (suc (suc n)))
      → bind (stepν aP) stepν ≡ bind (stepν (mapSProc' _ _ swap aP)) stepν
--   stepν-swap (`out ch z P) with canNu? (out ch z)
--   stepν-swap aP@(`out ._ z P) | nope (out refl') with decName (fresh _) (swapS z)
--   ... | yes q = sym (cong stepνF r ∙ no-stepν (bout refl'))
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong₂ Label'.out (snoc-fresh _ _) (sym q)) refl) ∙ stepν-out-fresh
--   ... | no ¬q = sym (cong′ stepνF r ∙ no-stepν (out refl'))
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong₂ Label'.out (snoc-fresh _ _) (sym (ι-down \ eq → ¬q (sym eq)))) refl) ∙ stepν-out _ _ _
--   stepν-swap aP@(`out _ _ P) | out {_} {_} {ch} {z} refl' refl' with canNu? (out ch z)
--   stepν-swap aP@(`out _ _ P) | out {_} {_} {ch} {z} refl' refl' | out refl' refl' = refl ∙
--    sym (cong′ stepνF r ∙ stepν-out _ _ _ ∙ cong′ η (StepPath refl refl (later-ext (\ α → sym (ih α .swapνX)))))
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong₂ Label'.out (swapS-ιι _) (swapS-ιι _)) refl) ∙ stepν-out _ _ _
--   stepν-swap aP@(`out _ _ P) | out {_} {_} {ch} {z} refl' refl' | out2 refl' refl' = cong′ η (StepPath refl refl
--              (later-ext (\ α → cong νX (sym (mapmapProc' _ _ _ (_ , swapS-inj) (_ , swapS-inj) (P α) ∙ cong₂ (mapProc' _ _) (funExt swapswapS) refl ∙ mapProc'-id _ _)))))
--     ∙ sym (cong′ stepνF r ∙ stepν-bout)
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong₂ Label'.out (swapS-ιι _) (snoc-ι _ _ _ ∙ snoc-fresh _ _)) refl) ∙ stepν-out-fresh
--   stepν-swap aP@(`out _ _ P) | out {_} {_} {ch} {z} refl' refl' | nope (out refl') = sym (cong′ stepνF r)
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong Label'.out (snoc-ι _ _ _ ∙ snoc-fresh _ _) <* _) refl) ∙ no-stepν (out refl')
--   stepν-swap aP@(`out _ z P) | out2 {_} {_} {ch} refl' refl' with canNu? (bout ch)
--   stepν-swap aP@(`out _ z P) | out2 {_} {ch} refl' refl' | bout refl' = sym (cong′ stepνF r ∙ stepν-out-fresh)
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong₂ Label'.out (swapS-ιι _) (snoc-fresh _ _)) refl) ∙ stepν-out _ _ _
--   stepν-swap aP@(`out _ z P) | out2 {_} {ch} refl' refl' | nope (bout refl') = sym (cong′ stepνF r)
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong₂ Label'.out (snoc-ι _ _ _ ∙ snoc-fresh _ _) (snoc-fresh _ _ )) refl) ∙ no-stepν (out refl')
--   stepν-swap aP@(`bout ch0 P) with canNu? (bout ch0)
--   stepν-swap aP@(`bout ch0 P) | bout {_} {ch} refl' with canNu? (bout ch)
--   stepν-swap aP@(`bout ch0 P) | bout {_} {ch} refl' | bout {_} {ch'} refl' = sym (cong stepνF r ∙ stepν-bout ∙ cong′ η (StepPath refl refl (later-ext \ α →
--     cong νX (ν-map _ _ (_ , swapS-inj) _ ∙ cong νX (mapmapProc' _ _ _ (_ , liftS-inj (_ , swapS-inj)) (_ , swapS-inj) _
--                                                    ∙ mapmapProc' _ _ _ liftS-swapS-Inj (_ , liftS-inj (_ , swapS-inj)) _
--       ∙ cong₂ (mapProc' _ _) (funExt lift-vs-swap) refl ∙ sym (mapmapProc' _ _ _ (swapS , swapS-inj) liftS-swapS-Inj (P α)) ))
--       ∙ sym (ih α .swapνX) ∙ sym (cong νX (ν-map _ _ (_ , swapS-inj) _ ∙ cong νX (mapmapProc' _ _ _ (_ , liftS-inj (_ , swapS-inj)) (_ , swapS-inj) (P α)))))))
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong′ Label'.bout (swapS-ιι ch')) refl) ∙ stepν-bout
--   stepν-swap aP@(`bout ch0 P) | bout {_} {ch} refl' | nope (bout refl') = sym (cong stepνF r)
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong′ Label'.bout (snoc-ι _ _ _ ∙ snoc-fresh _ _)) refl) ∙ no-stepν (bout refl')
--   stepν-swap aP@(`bout ch0 P) | nope (bout refl') = sym (cong stepνF r ∙ no-stepν (bout refl'))
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong′ Label'.bout (snoc-fresh _ _)) refl) ∙ stepν-bout
--   stepν-swap aP@(`inp ch0 z0 P) with canNu? (inp ch0 z0)
--   ... | inp {_} {_} {ch} {z} refl' refl' with canNu? (inp ch z)
--   ... | nope (inp (_⊎_.inl refl')) = sym (cong stepνF r)
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong₂ Label'.inp (snoc-ι _ _ _ ∙ snoc-fresh _ _) (snoc-ι _ _ _)) refl) ∙ no-stepν (inp (_⊎_.inl refl'))
--   ... | nope (inp (_⊎_.inr refl')) = sym (cong stepνF r)
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong₂ Label'.inp (snoc-ι _ _ _) (snoc-ι _ _ _ ∙ snoc-fresh _ _)) refl) ∙ no-stepν (inp (_⊎_.inr refl'))
--   ... | inp refl' refl' = sym (cong stepνF r ∙ stepν-inp _ _ _ ∙ cong′ η (StepPath refl refl (later-ext \ α → sym (ih α .swapνX))))
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong₂ Label'.inp (swapS-ιι _) (swapS-ιι _)) refl) ∙ stepν-inp _ _ _
--   stepν-swap aP@(`inp ch0 z0 P) | nope (inp (_⊎_.inl refl')) with decName (fresh _) (swapS z0)
--   ... | yes q = sym (cong stepνF r)
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong₂ Label'.inp (snoc-fresh _ _) (sym q)) refl) ∙ no-stepν (inp (_⊎_.inr refl'))
--   ... | no ¬q = sym (cong stepνF r ∙ no-stepν (inp (_⊎_.inl refl')))
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong₂ Label'.inp (snoc-fresh _ _) (sym (ι-down (\ eq → ¬q (sym eq))))) refl) ∙ stepν-inp _ _ _
--   stepν-swap aP@(`inp ch0 z0 P) | nope (inp (_⊎_.inr refl')) with decName (fresh _) (swapS ch0)
--   ... | yes q = sym (cong stepνF r)
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong₂ Label'.inp (sym q) (snoc-fresh _ _)) refl) ∙ no-stepν (inp (_⊎_.inl refl'))
--   ... | no ¬q = sym (cong stepνF r ∙ no-stepν (inp (_⊎_.inr refl')))
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong₂ Label'.inp (sym (ι-down (\ eq → ¬q (sym eq)))) (snoc-fresh _ _)) refl) ∙ stepν-inp _ _ _
--   stepν-swap aP@(`binp ch0 P) with canNu? (binp ch0)
--   ... | binp {_} {ch} refl' with canNu? (binp ch)
--   ... | binp {_} {ch2} refl' = sym (cong′ stepνF r ∙ stepν-binp ∙ cong′ η (StepPath refl refl (later-ext \ α →
--     cong νX (ν-map _ _ (_ , swapS-inj) _ ∙ cong νX (mapmapProc' _ _ _ (_ ,  liftS-inj (_ , swapS-inj)) (_ , swapS-inj) _ ∙ mapmapProc' _ _ _ liftS-swapS-Inj (_ , liftS-inj (_ , swapS-inj)) _
--       ∙ cong₂ (mapProc' _ _) (funExt lift-vs-swap) refl ∙ sym (mapmapProc' _ _ _ (swapS , swapS-inj) liftS-swapS-Inj (P α)) ))
--       ∙ sym (ih α .swapνX) ∙ sym (cong νX (ν-map _ _ (_ , swapS-inj) _ ∙ cong νX (mapmapProc' _ _ _ (_ , liftS-inj (_ , swapS-inj)) (_ , swapS-inj) (P α))))
--     )))
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong Label'.binp (swapS-ιι ch2)) refl) ∙ stepν-binp
--   ... | nope (binp refl') = sym (cong′ stepνF r)
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong Label'.binp (snoc-ι _ _ _ ∙ snoc-fresh _ _)) refl) ∙ no-stepν (binp refl')
--   stepν-swap aP@(`binp ch0 P) | nope (binp refl') = sym (cong′ stepνF r ∙ no-stepν (binp refl'))
--     where
--      r : stepν (mapSProc' _ _ swapS aP) ≡ _
--      r = cong′ stepν (StepPath refl (cong Label'.binp (snoc-fresh _ _)) refl) ∙ stepν-binp
--   stepν-swap (`τ P) = cong′ η (cong′ `τ (later-ext \ α → ih α .swapνX))

--   stepν-swap : ∀ {n} (aP : Step (\ n → ▹ Proc n) (suc (suc n))) →
--       bind (stepν aP) stepν ≡ bind (stepν (mapSProc' _ _ swap aP)) stepν
--   stepν-swap (a , P) with canNu? a
--   ... | out {a = a} {a'} eq with canNu? (out (swap a'))
--   ... | out {a = b}{b'} eq2 with canNu? (out b) | canNu? (out a)
--   ... | out {a = a₁} eq' | out {a = a₂} eq'' =
--     cong η (StepPath (λ i → out (p i))
--                      (later-ext λ α → ih α .swapνX))
--     where        
--       p' : ι (ι a₂) ≡ ι (ι a₁)
--       p' =
--         sym (swap-ιι a₂)
--         ∙ (λ i → swap (ι (eq'' (~ i))))
--         ∙ (λ i → swap (eq (~ i)))
--         ∙ eq2
--         ∙ λ i → ι (eq' i)
        
--       p : a₂ ≡ a₁
--       p = ι-inj _ _ (ι-inj _ _ p')          
--   ... | out eq' | nope (out eq'') = ⊥-rec (fresh-ι p)
--     where
--       p : ι b ≡ fresh (suc _)
--       p =
--         sym eq2
--         ∙ (λ i → swap (eq i))
--         ∙ snoc-ι _ _ _
--         ∙ (λ i → snoc (λ x → ι (ι x)) (fresh (suc _)) (eq'' i))
--         ∙ snoc-fresh _ _
--   ... | nope (out eq') | out {a = a₂} eq'' = ⊥-rec (fresh-ι (ι-inj _ _ p))
--     where        
--       p : ι (ι a₂) ≡ ι (fresh _)
--       p = 
--         sym (swap-ιι a₂)
--         ∙ (λ i → swap (ι (eq'' (~ i))))
--         ∙ (λ i → swap (eq (~ i)))
--         ∙ eq2
--         ∙ λ i → ι (eq' i)
--   ... | nope (out _) | nope (out _) = refl
--   stepν-swap (._ , P) | out {a = a}{a'} eq | nope (out eq') with canNu? (out a)
--   ... | out eq'' = ⊥-rec (fresh-ι (sym p))
--     where
--       p : fresh (suc _) ≡ ι (ι _)
--       p =
--         sym eq'
--         ∙ (λ i → swap (eq i))
--         ∙ snoc-ι _ _ _
--         ∙ (λ i → snoc (λ x → ι (ι x)) (fresh (suc _)) (eq'' i))
--         ∙ snoc-ι _ _ _
--   ... | nope (out eq'') = refl
--   stepν-swap (._ , P) | inp {a = a}{a'} eq with canNu? (inp (swap a'))
--   ... | inp {a = b}{b'} eq2 with canNu? (inp b) | canNu? (inp a)
--   ... | inp eq' | inp eq'' = 
--     cong η (StepPath (λ i → inp (p i))
--                      (later-ext λ α → ih α .swapνX))
--     where        
--       p' : ι (ι _) ≡ ι (ι _)
--       p' =
--         sym (swap-ιι _)
--         ∙ (λ i → swap (ι (eq'' (~ i))))
--         ∙ (λ i → swap (eq (~ i)))
--         ∙ eq2
--         ∙ λ i → ι (eq' i)
        
--       p : _ ≡ _
--       p = ι-inj _ _ (ι-inj _ _ p')          
--   ... | inp eq' | nope (inp eq'') = ⊥-rec (fresh-ι p)
--     where
--       p : ι b ≡ fresh (suc _)
--       p =
--         sym eq2
--         ∙ (λ i → swap (eq i))
--         ∙ snoc-ι _ _ _
--         ∙ (λ i → snoc (λ x → ι (ι x)) (fresh (suc _)) (eq'' i))
--         ∙ snoc-fresh _ _
--   ... | nope (inp eq') | inp eq'' = ⊥-rec (fresh-ι (ι-inj _ _ p))
--     where        
--       p : ι (ι _) ≡ ι (fresh _)
--       p = 
--         sym (swap-ιι _)
--         ∙ (λ i → swap (ι (eq'' (~ i))))
--         ∙ (λ i → swap (eq (~ i)))
--         ∙ eq2
--         ∙ λ i → ι (eq' i)
--   ... | nope (inp eq') | nope (inp eq'') = refl
--   stepν-swap (._ , P) | inp {a = a}{a'} eq | nope (inp eq') with canNu? (inp a)
--   ... | inp eq'' = ⊥-rec (fresh-ι (sym p))
--     where
--       p : fresh (suc _) ≡ ι (ι _)
--       p =
--         sym eq'
--         ∙ (λ i → swap (eq i))
--         ∙ snoc-ι _ _ _
--         ∙ (λ i → snoc (λ x → ι (ι x)) (fresh (suc _)) (eq'' i))
--         ∙ snoc-ι _ _ _
--   ... | nope (inp eq'') = refl
--   stepν-swap (._ , P) | τ = cong η (StepPath refl (later-ext λ α → ih α .swapνX))
--   stepν-swap (._ , P) | nope (out {a'} eq) with canNu? (out (swap a'))
--   ... | nope (out eq') = refl
--   ... | out {a = a} eq' with canNu? (out a)
--   ... | nope (out eq'') = refl
--   ... | out eq'' = ⊥-rec (fresh-ι (ι-inj _ _ (sym p)))
--     where
--       p : ι (fresh _) ≡ ι (ι _)
--       p =
--         sym (snoc-fresh _ _)          
--         ∙ (λ i → swap (eq (~ i)))
--         ∙ eq'
--         ∙ λ i → ι (eq'' i)
--   stepν-swap (._ , P) | nope (inp {a'} eq) with canNu? (inp (swap a'))
--   ... | nope (inp eq') = refl
--   ... | inp {a = a} eq' with canNu? (inp a)
--   ... | nope (inp eq'') = refl
--   ... | inp eq'' = ⊥-rec (fresh-ι (ι-inj _ _ (sym p)))
--     where
--       p : ι (fresh _) ≡ ι (ι _)
--       p =
--         sym (snoc-fresh _ _)          
--         ∙ (λ i → swap (eq (~ i)))
--         ∙ eq'
--         ∙ λ i → ι (eq'' i)


  ν-swap : ∀ {n} {P : Proc (suc (suc n))} → νProc (νProc P) ≡ νProc (νProc (mapProc _ _ swap P))
  ν-swap {n} {P} =
    νProc (νProc P)
      ≡⟨ cong (λ x → isPi-alg.νX (x _) (isPi-alg.νX (x _) P)) (fix-eq ProcPi-algF) ⟩
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
      ≡⟨ cong (λ x → isPi-alg.νX (x _) (isPi-alg.νX (x _) (mapProc _ _ swap P))) (sym (fix-eq ProcPi-algF)) ⟩
    νProc (νProc (mapProc _ _ swap P))
      ∎


-- Matching when given the same name twice
  guard-refl : ∀ {m x P} → guardProc {m} x x P ≡ P
  guard-refl {m} {x} with decName x x
  guard-refl | yes p = refl
  guard-refl | no ¬p = ⊥-rec (¬p refl)

-- Putting everything together.
  ProcStructCongF : StructCong ProcPi-alg (mapProc _ _) _≡_
  ProcStructCongF = record
    { refl≈X = refl
    ; sym≈X = sym
    ; _∙≈X_ = _∙_
    ; cong·X = λ {_}{_}{_}{_}{a} → cong′ (actProc a)
    ; cong⊕X = λ eq1 eq2 → cong₂ sumProc eq1 eq2
    ; cong∣∣X = λ eq1 eq2 → cong₂ parProc eq1 eq2
    ; congνX = cong′ νProc
    ; congguardX = cong′ (guardProc _ _)
    ; cong!X = cong′ !Proc
    ; unit⊕X = unit-sum
    ; comm⊕X = comm-sum
    ; assoc⊕X = assoc-sum
    ; unit∣∣X = unit-par
    ; comm∣∣X = λ {_}{P} → comm-par {p = P}
    ; assoc∣∣X = λ {_}{P} → assoc-par {P = P} 
    ; replX = λ {_}{P} → repl-par {P = P}
    ; guardreflX = guard-refl
    ; ν∣∣X = ν-par
    ; swapνX = ν-swap
    ; νendX = ν-end
    }

ProcStructCong : StructCong ProcPi-alg (mapProc _ _) _≡_
ProcStructCong = fix ProcStructCongF


              

