{-# OPTIONS --cubical --guarded -WnoUnsupportedIndexedMatch #-}

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
open import pi-calculus.semantics.Dynamics ns

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
    congS (λ x → isPi-alg.parX (x n) P (isPi-alg.endX (x n))) (fix-eq ProcPi-algF)
    ∙ cong Fold (cong₂ _∪_ (unit _) (bind-ø (Unfold P))
                ∙ unit _
                ∙ congS (λ x → mapP∞ x (Unfold P))
                        (funExt (λ _ → StepPath refl refl
                                                (later-ext (λ α → cong₂ parProc refl (congS Fold (mapProc'-eq' _ _ _ _))
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
    congS (λ x → isPi-alg.parX (x n) P Q) (fix-eq ProcPi-algF)
    ∙ cong Fold (cong₂ _∪_ ((cong₂ _∪_
        (congS (λ f → mapP∞ f (Unfold P)) (funExt (λ x → StepPath refl refl (later-ext (λ α → ih α .comm∣∣X {_}{_}{mapProc _ _ (fst (labelInj (theLabel x))) Q})))))
        (congS (λ f → mapP∞ f (Unfold Q)) (funExt (λ x → StepPath refl refl (later-ext (λ α → ih α .comm∣∣X {_}{mapProc _ _ (fst (labelInj (theLabel x))) P})))))) ∙ comm _ _)
        (comm-synchF {_}{Unfold P}{Unfold Q}))
    ∙ congS (λ x → isPi-alg.parX (x n) Q P) (sym (fix-eq ProcPi-algF))

-- Associativity of parProc (which requires many lemmata)..
  step-LR : ∀ {n} P Q R →
    stepL {n} (stepR P Q) R ≡ stepR P (stepL Q R)
  step-LR P Q R =
    mapmapP∞ _ _ Q
    ∙ congS (λ f → mapP∞ f Q) (funExt (λ { (a , P') →
        StepPath refl refl (later-ext (λ α → ih α .assoc∣∣X {P = Fold (mapProc' _ _ _ _)}))}))
          ∙ sym (mapmapP∞ _ _ Q)

  step-RR : ∀ {n} P Q R →
    stepR {n} P (stepR Q R) ≡ stepR (parProc P Q) R
  step-RR P Q R =
    mapmapP∞ _ _ R
    ∙ sym (congS (λ f → mapP∞ f R) (funExt (λ { (a , R') →
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
      ∙ sym (ih α .ν∣∣X) ∙ congS νProc (ih α .assoc∣∣X {P = P' α}{Q' α}))))
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
            ∙ congS νProc (ih α .assoc∣∣X {P = Q α}{P α}))))
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
                    ∙ congS νProc (ih α .comm∣∣X {Q = Fold (mapProc' _ _ _ _)}
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
                    ∙ congS νProc (ih α .comm∣∣X {Q = Fold (mapProc' _ _ _ _)}
                            ∙ sym (ih α .assoc∣∣X {P = Fold (mapProc' _ _ _ _)})))))
  ... | nope = refl

  synch'-assoc : ∀ {n} (aP : Step (\ n → ▹ Proc n) n) Q aR →
    synch' (λ _ → parProc) (λ _ → νProc) (mapStep (λ m i P' α → parProc (P' α) (mapProc n m (i .fst) Q)) aP) aR
    ≡ synch' (λ _ → parProc) (λ _ → νProc) aP (mapStep (λ m i R' α → parProc (mapProc n m (i .fst) Q) (R' α)) aR)
  synch'-assoc (a , P) Q (b , R) with canSynchL? a b
  ... | local r r' = cong η (StepPath refl refl (later-ext (λ α → ih α .assoc∣∣X {P = P α})))
  ... | bound r = cong η (StepPath refl refl (later-ext (λ α → congS νProc (ih α .assoc∣∣X {P = P α}))))
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
            (congS (λ (f : ▹ (∀ n → Proc n → Proc n → Proc n)) → synch' (λ α {n} → f α n) (λ _ → νProc) aR' (mapStep (λ m i P' α → parProc (P' α) (mapProc _ m (i .fst) Q)) aP'))
              (later-ext (λ α → funExt (λ _ → funExt (λ p → (funExt (λ q → ih α .comm∣∣X {P = q}))))))
             ∙ congS (synch' (λ _ → parProc) (λ _ → νProc) aR') (StepPath refl refl (later-ext (λ α → ih α .comm∣∣X {P = theX aP' α})))
             ∙ sym (synch'-assoc aR' Q aP')
             ∙ congS {y = mapStep (λ m i R' α → parProc (mapProc _ m (i .fst) Q) (R' α)) aR'} (λ x → synch' (λ _ → parProc) (λ _ → νProc) x aP') (StepPath refl refl (later-ext (λ α → ih α .comm∣∣X {P = theX aR' α})))
             ∙ congS (λ (f : ▹ (∀ n → Proc n → Proc n → Proc n)) → synch' (λ α {n} → f α n) (λ _ → νProc) (mapStep (λ m i R' α → parProc (mapProc _ m (i .fst) Q) (R' α)) aR') aP')
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
  synchsynchF P Q R = congS (bind P) (funExt \ a' → bind-bind Q _ _ ∙ congS (bind Q) (funExt \ b' → bind-bind R _ _ ∙ congS (bind R)
    (funExt \ c' → synchsynch b' c' a') ∙ bind-ø R) ∙ bind-ø Q) ∙ bind-ø P

  step-LL : ∀ {n} P Q R →
    stepL {n} (stepL P Q) R ≡ stepL P (parProc Q R)
  step-LL {n} P Q R =
    mapmapP∞ _ _ P
    ∙ congS (λ f → mapP∞ f P) (funExt (λ { (a , P') →
        StepPath refl refl (later-ext (λ α →  ih α .assoc∣∣X {P = P' α} ∙ cong₂ parProc refl (sym (par-map _ _ (labelInj a) Q R))))}))

  assoc-synchF : ∀ {n} (P : F' n (\ _ → Proc)) Q R →
    synchF (synchF P Q) R ≡ synchF P (synchF Q R)
  assoc-synchF P Q R = comm-synchF {p = synchF P Q} {R} ∙ synchsynchF R P Q ∙ sym (synchsynchF P Q R)

  assoc-par : ∀ {n} {P Q R : Proc n} → parProc (parProc P Q) R ≡ parProc P (parProc Q R)
  assoc-par {n}{P}{Q}{R} =
   cong₂ parProc (congS (λ x → isPi-alg.parX (x n) P Q) (fix-eq ProcPi-algF)) refl
   ∙ congS (λ x → isPi-alg.parX (x n) (isPi-alg.parX (fix-eq ProcPi-algF i1 n) P Q) R) (fix-eq ProcPi-algF)
   ∙ cong Fold (sym (assoc _ _ _ ∙ assoc _ _ _ ∙ assoc _ _ _)
                ∙ cong₂ _∪_
                    (step-LL (Unfold P) Q R
                     ∙ congS (λ f → mapP∞ f (Unfold P)) (funExt (λ P' →
                         StepPath refl refl (later-ext (λ α → cong₂ parProc refl (congS (mapProc _ _ _) (congS (λ x → isPi-alg.parX (x n) Q R) (fix-eq ProcPi-algF))))))))
                    (cong₂ _∪_ (step-LR P (Unfold Q) R)
                      (comm _ _ ∙ sym (assoc _ _ _)
                       ∙ cong₂ _∪_
                           (sym (step-RR P Q (Unfold R)
                            ∙ congS (λ f → mapP∞ f (Unfold R)) (funExt (λ R' →
                             StepPath refl refl (later-ext (λ α → cong₂ parProc (congS (mapProc _ _ _) (congS (λ x → isPi-alg.parX (x n) P Q) (fix-eq ProcPi-algF))) refl))))))
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
   ∙ sym (congS (λ x → isPi-alg.parX (x n) P (isPi-alg.parX (fix-eq ProcPi-algF i1 n) Q R)) (fix-eq ProcPi-algF))
   ∙ sym (cong₂ parProc refl (congS (λ x → isPi-alg.parX (x n) Q R) (fix-eq ProcPi-algF)))

-- The equation characterizing replication as iterated parallel composition.

  synch-! : ∀ {n} (P : Proc n)
    → stepL (synchF (Unfold P) (Unfold P)) (!Proc P) ≡ synchF (Unfold P) (Unfold (!Proc P))
  synch-! P =
    sym (unit _)
    ∙ cong₂ _∪_ refl (sym (congS (λ P' → stepL P' (!Proc P)) (synchsynchF (Unfold P) (Unfold P) (Unfold P))))
    ∙ cong₂ _∪_ (synchF-L (Unfold P) (Unfold P) (!Proc P) ∙ bind-comm _ (Unfold P) (stepL (Unfold P) (!Proc P)))
                (synchF-L (Unfold P) (synchF (Unfold P) (Unfold P)) (!Proc P) ∙ bind-comm _ (Unfold P) (stepL (synchF (Unfold P) (Unfold P)) (!Proc P)))
    ∙ bind-comm _ (stepL (Unfold P) (!Proc P) ∪ stepL (synchF (Unfold P) (Unfold P)) (!Proc P)) (Unfold P)
    ∙ congS (synchF (Unfold P)) (cong Unfold (sym (!Proc-eq {_}{P})))

  stepR-! : ∀ {n} {P : Proc n} → stepR P (Unfold (!Proc P)) ≡ Unfold (!Proc P)
  stepR-! {_}{P} =
    cong₂ mapP∞ (funExt (λ aP' → StepPath refl refl (later-ext (λ α → ih α .comm∣∣X {P = Fold (mapProc' _ _ _ _)})))) (refl {x = Unfold (!Proc P)})
    ∙ cong₂ stepL (cong Unfold (!Proc-eq {_}{P})) refl
    ∙ cong₂ _∪_
        (step-LL (Unfold P) (!Proc P) P ∙ congS (stepL' (Unfold P)) (later-ext (λ α → ih α .comm∣∣X {P = !Proc P} ∙ sym (ih α .replX {P = P}))))
        (step-LL (synchF (Unfold P) (Unfold P)) (!Proc P) P ∙ congS (stepL' (synchF (Unfold P) (Unfold P))) (later-ext (λ α → ih α .comm∣∣X {P = !Proc P} ∙ sym (ih α .replX {P = P}))))
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
    ∙ congS (λ x → isPi-alg.parX (x _) P (isPi-alg.!X (fix-eq ProcPi-algF i0 _) P)) (sym (fix-eq ProcPi-algF))

-- Restriction of the nil process.
  ν-end : ∀ {n} → νProc endProc ≡ endProc {n}
  ν-end = refl

-- The equation relating restriction and parallel composition (plus
-- many required lemmata).
  ν-stepL' : ∀ {n} aP Q → stepν (mapStep (λ m i P' α → parProc (P' α) (mapProc _ _ (i .fst) (mapProc _ _ ι Q))) aP) ≡ stepL {n} (stepν aP) Q
  ν-stepL' (a , P) Q with canNu? a
  ν-stepL' (.(out _ _) , P) Q | out x x₁ = cong η (StepPath refl refl (later-ext (λ α →
      congS νProc (cong₂ parProc refl (mapProc-id _ _)) ∙ ih α .ν∣∣X ∙ cong₂ parProc refl (sym (mapProc-id _ _)))))

  ν-stepL' (.(out _ _) , P) Q | out2 x x₁ = cong η (StepPath refl refl (later-ext (λ α → cong₂ parProc refl (mapProc-id _ _))))
  ν-stepL' (.(inp _ _) , P) Q | inp x x₁ =
    cong η (StepPath refl refl (later-ext (λ α →
      congS νProc (cong₂ parProc refl (mapProc-id _ _)) ∙ ih α .ν∣∣X ∙ cong₂ parProc refl (sym (mapProc-id _ _)))))
  ν-stepL' (.(bout _) , P) Q | bout x =
    cong η (StepPath refl refl (later-ext (λ α →
      cong νProc (par-map _ _ (swap , swap-inj) _ _)
      ∙ cong νProc (cong₂ parProc refl
          (mapmapProc _ _ _ (_ , swap-inj) (_ , ι-inj) _
           ∙ mapmapProc _ _ _ (_ , \ x y p → ι-inj _ _ (swap-inj _ _ p)) (_ , ι-inj) _
           ∙ congS (λ x → mapProc _ _ x Q) (funExt swap-ιι)
           ∙ sym (mapmapProc _ _ _ (_ , ι-inj) (_ , ι-inj) _)))
      ∙ ih α .ν∣∣X)))
  ν-stepL' (.(binp _) , P) Q | binp x =
    cong η (StepPath refl refl (later-ext (λ α →
      cong νProc (par-map _ _ (swap , swap-inj) _ _)
      ∙ cong νProc (cong₂ parProc refl
          (mapmapProc _ _ _ (_ , swap-inj) (_ , ι-inj) _
           ∙ mapmapProc _ _ _ (_ , \ x y p → ι-inj _ _ (swap-inj _ _ p)) (_ , ι-inj) _
           ∙ congS (λ x → mapProc _ _ x Q) (funExt swap-ιι)
           ∙ sym (mapmapProc _ _ _ (_ , ι-inj) (_ , ι-inj) _)))
      ∙ ih α .ν∣∣X)))
  ν-stepL' (.τ , P) Q | τ = cong η (StepPath refl refl (later-ext (λ α →
    congS νProc (cong₂ parProc refl (mapProc-id _ _)) ∙ ih α .ν∣∣X ∙ cong₂ parProc refl (sym (mapProc-id _ _)))))
  ν-stepL' (a , P) Q | nope x = refl

  ν-stepL : ∀ {m P Q} →
    νProc (Fold (stepL (Unfold P) (mapProc m _ ι Q)))
    ≡ Fold (stepL (Unfold (νProc P)) Q)
  ν-stepL {n}{P}{Q} =
    congS (λ x → isPi-alg.νX (x _) (Fold (stepL (Unfold P) (mapProc n _ ι Q)))) (fix-eq ProcPi-algF)
    ∙ cong Fold
        (bind-map (Unfold P) _ _
         ∙ cong (bind (Unfold P)) (funExt (λ aP' → ν-stepL' aP' Q))
         ∙ sym (map-bind (Unfold P) _ _))
    ∙ congS (λ x → Fold (stepL (Unfold (isPi-alg.νX (x _) P)) Q)) (sym (fix-eq ProcPi-algF))

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
    cong η (StepPath refl (congS bout (down-ι p))
      (later-ext (λ α → congS νProc (par-map _ _ (_ , swap-inj) _ _
                                  ∙ cong₂ parProc (mapmapProc _ _ _ (_ , swap-inj) (_ , ι-inj) _ ∙ cong₂ (mapProc _ _) (funExt swap-ι-lift) refl)
                                               (mapmapProc _ _ _ (_ , swap-inj) (_ , lift-inj (_ , ι-inj)) _ ∙ cong₂ (mapProc _ _) (funExt swap-lift-ι) refl))
                         ∙ ih α .ν∣∣X
                         ∙ cong₂ parProc (sym (ν-map _ _ (_ , ι-inj) P)) refl)))
  ν-stepR' P (`inp ch v Q) with decName (ι ch) (fresh _) | decName (ι v) (fresh _)
  ν-stepR' P (`inp ch v Q) | yes p | _ = ⊥-rec (fresh-ι p)
  ν-stepR' P (`inp ch v Q) | no p | yes q = ⊥-rec (fresh-ι q)
  ν-stepR' P (`inp ch v Q) | no p | no q =
    cong η (StepPath refl (λ i → inp (down-ι p i) (down-ι q i)) (later-ext (λ α → ih α .ν∣∣X ∙ cong₂ parProc (congS νProc (mapProc-id _ _) ∙ sym (mapProc-id _ _)) refl)))
  ν-stepR' P (`binp ch Q) with decName (ι ch) (fresh _)
  ν-stepR' P (`binp ch Q) | yes p = ⊥-rec (fresh-ι p)
  ν-stepR' {n} P (`binp ch Q) | no p =
    cong₂ _∪_
      (cong η (StepPath refl (congS binp (down-ι p))
        (later-ext (λ α → congS νProc (par-map _ _ (_ , swap-inj) _ _
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
    cong η (congS `τ (later-ext (λ α → ih α .ν∣∣X ∙ cong₂ parProc (cong νProc (mapProc-id _ _) ∙ sym (mapProc-id _ _)) refl)))

  ν-stepR : ∀ {m P Q} → νProc (Fold (stepR P (Unfold (mapProc m _ ι Q)))) ≡ Fold (stepR (νProc P) (Unfold Q))
  ν-stepR {m} {P} {Q} =
    congS νProc (congS Fold (congS (stepR P) (mapProc'-eq' _ _ _ _)))
    ∙ congS (λ x → isPi-alg.νX (x _) (Fold (stepR P (mapProcF (next mapProc') m (suc m) ι (Unfold Q))))) (fix-eq ProcPi-algF)
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
    ∙ congS η (congS `τ (later-ext \ α → congS νProc (cong₂ parProc refl (cong₂ (mapProc _ _) (funExt snoc-ι-fresh) refl ∙ mapProc-id _ (Q _)))))
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
    = cong₂ _∪_ (congS η (congS `τ (later-ext \ α → (ih α .swapνX ∙ congS νProc (congS νProc (par-map _ _ (swap , swap-inj) (P α) _ ∙ cong₂ parProc refl
                       (mapmapProc _ _ _ (_ , swap-inj) (_ , lift-inj (_ , ι-inj)) (Q α)
                        ∙ λ i → mapProc _ _ (funExt swap-lift-ι i) (Q α))))) 
         ∙ congS νProc (ih α .ν∣∣X {P = Fold (mapProc' _ _ _ _)}))))
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
  ... | yes p | yes p' = cong₂ bind (synch'-out-inp _ _ _ _ (cong ι p ∙ sym r) (cong ι p' ∙ sym r')) refl ∙ congS η (congS `τ (later-ext \ α → ih α .ν∣∣X)) 
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
    ∙ congS η (congS `τ (later-ext \ α →
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
    congS (λ x → isPi-alg.νX (x _) (Fold (synchF (Unfold P) (Unfold (mapProc _ _ ι Q))))) (fix-eq ProcPi-algF)
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
    ∙ congS (λ x → Fold (synchF (Unfold (isPi-alg.νX (x _) P)) (Unfold Q))) (sym (fix-eq ProcPi-algF))

  ν-par : ∀ {m P Q} → νProc (parProc P (mapProc m _ ι Q)) ≡ parProc (νProc P) Q
  ν-par {n}{P}{Q} =
    congS νProc (congS (λ x → isPi-alg.parX (x _) P (mapProc n _ ι Q)) (fix-eq ProcPi-algF))
    ∙ congS (λ x → isPi-alg.νX (x _) (isPi-alg.parX (fix-eq ProcPi-algF i1 _) P (mapProc n _ ι Q))) (fix-eq ProcPi-algF)
    ∙ cong Fold
        (cong₂ _∪_ (cong₂ _∪_
                      (cong Unfold (congS (λ x → isPi-alg.νX (x _) (Fold (stepL (Unfold P) (mapProc n _ ι Q)))) (sym (fix-eq ProcPi-algF)) ∙ ν-stepL {P = P}))
                      (cong Unfold (congS (λ x → isPi-alg.νX (x _) (Fold (stepR P (Unfold (mapProc n _ ι Q))))) (sym (fix-eq ProcPi-algF)) ∙ ν-stepR)))
                   (cong Unfold (congS (λ x → isPi-alg.νX (x _) (Fold (synchF (Unfold P) (Unfold (mapProc _ _ ι Q))))) (sym (fix-eq ProcPi-algF)) ∙ ν-synchF P Q)))
    ∙ congS (λ x → isPi-alg.parX (x n) (νProc P) Q) (sym (fix-eq ProcPi-algF))

-- The equation stating that the order in which a process is
-- restricted twice does not matter (again with some extra lemmata).

  lift-swap-Inj : ∀ {n} → Inj (suc (suc (suc n))) (suc (suc (suc n)))
  lift-swap-Inj =
    (\ x → lift swap (swap x)) ,
    \ _ _ eq → swap-inj _ _ (lift-inj (_ , swap-inj) _ _ eq)


  stepν-swap : ∀ {n} (aP : Step (\ n → ▹ Proc n) (suc (suc n)))
    → bind (stepν aP) stepν ≡ bind (stepν (mapSProc' _ _ swap aP)) stepν
  stepν-swap (out ch z , P) with canNu? (out ch z)
  stepν-swap {n} aP@(`out ch z P) | nope (out r') with decName (fresh _) (swap z)
  ... | yes q =
    J (λ ch eq → ø ≡ bind (stepν (out (swap ch) (swap z) , (λ α → Fold (mapProc' _ _ swap (Unfold (P α)))))) stepν)
       (sym (cong stepνF r ∙ no-stepν (bout refl)))
       (sym r')
    where
      r : stepν (mapSProc' _ _ swap (`out (fresh _) z P)) ≡ _
      r = congS stepν (StepPath refl (cong₂ out (snoc-fresh _ _) (sym q)) refl) ∙ stepν-out-fresh
  ... | no ¬q =
    J (λ ch eq → ø ≡ bind (stepν (out (swap ch) (swap z) , (λ α → Fold (mapProc' _ _ swap (Unfold (P α)))))) stepν)
      (sym (congS stepνF r ∙ no-stepν (out refl)))
      (sym r')
    where
     r : stepν (mapSProc' _ _ swap (`out (fresh _) z P)) ≡ _
     r = congS stepν (StepPath refl ((λ i → out (snoc-fresh (snoc (λ x → ι (ι x)) (fresh (suc n))) (ι (fresh n)) i) (sym (ι-down \ eq → ¬q (sym eq)) i)))
       refl) ∙ stepν-out (fresh _) _ (λ α → Fold (mapProc' _ _ swap (Unfold (P α))))
  stepν-swap {n} (`out ch z P) | out {ch = ch'}{z'} p q with canNu? (out ch' z')
  ... | out {ch = ch₁}{z₁} r r' =
    sym (congS stepνF s ∙ stepν-out _ _ _ ∙ congS η (StepPath refl refl (later-ext (\ α → sym (ih α .swapνX)))))
    ∙ λ i → bind (stepν (out (swap (sym (p ∙ congS ι r) i)) (swap (sym (q ∙ congS ι r') i)) , λ α → Fold (mapProc' _ _ swap (Unfold (P α))))) stepν
    where
     s : stepν (mapSProc' _ _ swap (out _ _ , P)) ≡ _
     s = congS stepν (StepPath refl (λ i → out (swap-ιι ch₁ i) (swap-ιι z₁ i)) refl) ∙ stepν-out _ _ _
  ... | out2 {ch = ch₁} r r' =
   (congS η (StepPath refl refl
             (later-ext (\ α → cong νProc (sym (mapmapProc _ _ _ (_ , swap-inj) (_ , swap-inj) (P α) ∙ cong₂ (mapProc _ _) (funExt swapswap) refl ∙ mapProc-id _ _)))))
     ∙ sym (congS stepνF s ∙ stepν-bout))
     ∙ λ i → bind (stepν (out (swap (sym (p ∙ congS ι r) i)) (swap (sym (q ∙ congS ι r') i)) , λ α → Fold (mapProc' _ _ swap (Unfold (P α))))) stepν
    where
      s : stepν (mapSProc' _ _ swap (out _ _ , P)) ≡ _
      s = congS stepν (StepPath refl (congS (out (swap (ι (ι ch₁)))) (snoc-ι _ _ _ ∙ snoc-fresh _ _) ∙ λ i → out (swap-ιι ch₁ i) (fresh (suc n))) refl) ∙ stepν-out-fresh
  ... | nope (out r) =
    sym (congS stepνF s)
    ∙ λ i → bind (stepν (out (swap (sym (p ∙ congS ι r) i)) (swap (q (~ i))) , λ α → Fold (mapProc' _ _ swap (Unfold (P α))))) stepν
    where
      s : stepν (mapSProc' _ _ swap (out _ _ , P)) ≡ _
      s = congS stepν (StepPath refl (congS (λ a → out a (swap (ι z'))) (snoc-ι _ _ _ ∙ snoc-fresh _ _)) refl) ∙ no-stepν (out refl)
  stepν-swap (`out ch z P) | out2 {ch = ch'} p q with canNu? (bout ch')
  ... | bout {ch = ch₁} r =
    sym (congS stepνF s ∙ stepν-out-fresh)
    ∙ λ i → bind (stepν (out (swap (sym (p ∙ congS ι r) i)) (swap (q (~ i))) , λ α → Fold (mapProc' _ _ swap (Unfold (P α))))) stepν    
    where
      s : stepν (mapSProc' _ _ swap (out _ _ , P)) ≡ _
      s = congS stepν (StepPath refl (congS (out (swap (ι (ι ch₁)))) (snoc-fresh _ _) ∙ congS (λ a → out a (ι (fresh _))) (swap-ιι ch₁)) refl) ∙ stepν-out _ _ _
  ... | nope (bout r) = 
    sym (congS stepνF s)
    ∙ λ i → bind (stepν (out (swap (sym (p ∙ congS ι r) i)) (swap (q (~ i))) , λ α → Fold (mapProc' _ _ swap (Unfold (P α))))) stepν    
    where
      s : stepν (mapSProc' _ _ swap (out _ _ , P)) ≡ _
      s = congS stepν (StepPath refl (congS (out (swap (ι (fresh _)))) (snoc-fresh _ _) ∙ congS (λ a → out a (ι (fresh _))) (snoc-ι _ _ _ ∙ snoc-fresh _ _)) refl) ∙ no-stepν (out refl)  
  stepν-swap (bout ch0 , P) with canNu? (bout ch0)
  stepν-swap (`bout ch0 P) | bout {ch = ch} p with canNu? (bout ch)
  ... | bout {ch = ch'} q =
    sym (cong stepνF r ∙ stepν-bout ∙ congS η (StepPath refl refl (later-ext \ α →
    cong νProc (ν-map _ _ (_ , swap-inj) _ ∙ congS νProc (mapmapProc _ _ _ (_ , lift-inj (_ , swap-inj)) (_ , swap-inj) _
                                                   ∙ mapmapProc _ _ _ lift-swap-Inj (_ , lift-inj (_ , swap-inj)) _
      ∙ cong₂ (mapProc _ _) (funExt lift-vs-swap) refl ∙ sym (mapmapProc _ _ _ (swap , swap-inj) lift-swap-Inj (P α)) ))
      ∙ sym (ih α .swapνX) ∙ sym (cong νProc (ν-map _ _ (_ , swap-inj) _ ∙ cong νProc (mapmapProc _ _ _ (_ , lift-inj (_ , swap-inj)) (_ , swap-inj) (P α)))))))
    ∙ λ i → bind (stepν (bout (swap (sym (p ∙ congS ι q) i)) , λ α → Fold (mapProc' _ _ (lift swap) (Unfold (P α))))) stepν    
    where
      r : stepν (mapSProc' _ _ swap (bout _ , P)) ≡ _
      r = congS stepν (StepPath refl (congS bout (swap-ιι ch')) refl) ∙ stepν-bout
  ... | nope (bout q) =
    sym (cong stepνF r)
    ∙ λ i → bind (stepν (bout (swap (sym (p ∙ congS ι q) i)) , λ α → Fold (mapProc' _ _ (lift swap) (Unfold (P α))))) stepν    
    where
      r : stepν (mapSProc' _ _ swap (bout _ , P)) ≡ _
      r = congS stepν (StepPath refl (congS bout (snoc-ι _ _ _ ∙ snoc-fresh _ _)) refl) ∙ no-stepν (bout refl)  
  stepν-swap (`bout ch0 P) | nope (bout p) =
    sym (cong stepνF r ∙ no-stepν (bout refl))
    ∙ λ i → bind (stepν (bout (swap (p (~ i))) , λ α → Fold (mapProc' _ _ (lift swap) (Unfold (P α))))) stepν    
    where
     r : stepν (mapSProc' _ _ swap (bout _ , P)) ≡ _
     r = congS stepν (StepPath refl (congS bout (snoc-fresh _ _)) refl) ∙ stepν-bout
  stepν-swap (inp ch0 z0 , P) with canNu? (inp ch0 z0)
  ... | inp {ch = ch} {z} p q with canNu? (inp ch z)
  ... | nope (inp (_⊎_.inl s)) =
    sym (cong stepνF r)
    ∙ λ i → bind (stepν (inp (swap (sym (p ∙ congS ι s) i)) (swap (q (~ i))) , λ α → Fold (mapProc' _ _ swap (Unfold (P α))))) stepν    
    where
      r : stepν (mapSProc' _ _ swap (inp _ _ , P)) ≡ _
      r = congS stepν (StepPath refl (congS (inp (swap (ι (fresh _)))) (snoc-ι _ _ _) ∙ congS (λ a → inp a (snoc (λ x → ι (ι x)) (fresh _) z)) (snoc-ι _ _ _ ∙ snoc-fresh _ _)) refl) ∙ no-stepν (inp (_⊎_.inl refl))
  ... | nope (inp (_⊎_.inr s)) =
    sym (cong stepνF r)
    ∙ λ i → bind (stepν (inp (swap (p (~ i))) (swap (sym (q ∙ cong ι s) i)) , λ α → Fold (mapProc' _ _ swap (Unfold (P α))))) stepν    
    where
      r : stepν (mapSProc' _ _ swap (inp _ _ , P)) ≡ _
      r = congS stepν (StepPath refl (congS (inp (swap (ι ch))) (snoc-ι _ _ _ ∙ snoc-fresh _ _) ∙ congS (λ a → inp a _) (snoc-ι _ _ _)) refl) ∙ no-stepν (inp (_⊎_.inr refl))
  ... | inp {ch = ch₁}{z₁}s s' =
    sym (cong stepνF r ∙ stepν-inp _ _ _ ∙ congS η (StepPath refl refl (later-ext \ α → sym (ih α .swapνX))))
    ∙ λ i → bind (stepν (inp (swap (sym (p ∙ cong ι s) i)) (swap (sym (q ∙ cong ι s') i)) , λ α → Fold (mapProc' _ _ swap (Unfold (P α))))) stepν    
    where
      r : stepν (mapSProc' _ _ swap (inp _ _ , P)) ≡ _
      r = congS stepν (StepPath refl (λ i → inp (swap-ιι ch₁ i) (swap-ιι z₁ i)) refl) ∙ stepν-inp _ _ _
  stepν-swap (inp ch0 z0 , P) | nope (inp (_⊎_.inl p)) with decName (fresh _) (swap z0)
  ... | yes q =
    sym (cong stepνF r)
    ∙ λ i → bind (stepν (inp (swap (sym p i)) (swap z0) , λ α → Fold (mapProc' _ _ swap (Unfold (P α))))) stepν    
    where
      r : stepν (mapSProc' _ _ swap (inp _ _ , P)) ≡ _
      r = congS stepν (StepPath refl (congS (inp (swap (fresh _))) (sym q) ∙ congS (λ a → inp a (fresh _)) (snoc-fresh _ _)) refl) ∙ no-stepν (inp (_⊎_.inr refl))
  ... | no ¬q =
    J (λ ch eq → ø ≡ bind (stepν (inp (swap ch) (swap z0) , (λ α → Fold (mapProc' _ _ swap (Unfold (P α)))))) stepν)
      (sym (congS stepνF r ∙ no-stepν (inp (_⊎_.inl refl))))
      (sym p)
    where
     r : stepν (mapSProc' _ _ swap (`inp (fresh _) z0 P)) ≡ _
     r = congS stepν (StepPath refl ((λ i → inp (snoc-fresh (snoc (λ x → ι (ι x)) (fresh (suc _))) (ι (fresh _)) i) (sym (ι-down \ eq → ¬q (sym eq)) i)))
       refl) ∙ stepν-inp (fresh _) _ (λ α → Fold (mapProc' _ _ swap (Unfold (P α))))
  stepν-swap (inp ch0 z0 , P) | nope (inp (_⊎_.inr p)) with decName (fresh _) (swap ch0)
  ... | yes q =
    sym (cong stepνF r)
    ∙ λ i → bind (stepν (inp (swap ch0) (swap (sym p i)) , λ α → Fold (mapProc' _ _ swap (Unfold (P α))))) stepν        
    where
      r : stepν (mapSProc' _ _ swap (inp _ _ , P)) ≡ _
      r = congS stepν (StepPath refl (congS (inp (swap ch0)) (snoc-fresh _ _) ∙ congS (λ a → inp a _) (sym q)) refl) ∙ no-stepν (inp (_⊎_.inl refl))
  ... | no ¬q = 
    J (λ z0 eq → ø ≡ bind (stepν (inp (swap ch0) (swap z0) , (λ α → Fold (mapProc' _ _ swap (Unfold (P α)))))) stepν)
      (sym (congS stepνF r ∙ no-stepν (inp (_⊎_.inr refl))))
      (sym p)
    where
     r : stepν (mapSProc' _ _ swap (`inp ch0 (fresh _) P)) ≡ _
     r = congS stepν (StepPath refl ((λ i → inp (sym (ι-down \ eq → ¬q (sym eq)) i) (snoc-fresh (snoc (λ x → ι (ι x)) (fresh (suc _))) (ι (fresh _)) i)))
       refl) ∙ stepν-inp _ (fresh _) (λ α → Fold (mapProc' _ _ swap (Unfold (P α))))
  stepν-swap (binp ch0 , P) with canNu? (binp ch0)
  ... | binp {ch = ch} p with canNu? (binp ch)
  ... | binp {_} {ch2} q =
    sym (congS stepνF r ∙ stepν-binp ∙ congS η (StepPath refl refl (later-ext \ α →
      cong νProc (ν-map _ _ (_ , swap-inj) _ ∙ cong νProc (mapmapProc _ _ _ (_ ,  lift-inj (_ , swap-inj)) (_ , swap-inj) _ ∙ mapmapProc _ _ _ lift-swap-Inj (_ , lift-inj (_ , swap-inj)) _
       ∙ cong₂ (mapProc _ _) (funExt lift-vs-swap) refl ∙ sym (mapmapProc _ _ _ (swap , swap-inj) lift-swap-Inj (P α)) ))
       ∙ sym (ih α .swapνX) ∙ sym (cong νProc (ν-map _ _ (_ , swap-inj) _ ∙ cong νProc (mapmapProc _ _ _ (_ , lift-inj (_ , swap-inj)) (_ , swap-inj) (P α))))
    )))
    ∙ λ i → bind (stepν (binp (swap (sym (p ∙ congS ι q) i)) , λ α → Fold (mapProc' _ _ (lift swap) (Unfold (P α))))) stepν    
    where
      r : stepν (mapSProc' _ _ swap (binp _ , P)) ≡ _
      r = congS stepν (StepPath refl (congS binp (swap-ιι ch2)) refl) ∙ stepν-binp
  ... | nope (binp q) =
    sym (congS stepνF r)
    ∙ λ i → bind (stepν (binp (swap (sym (p ∙ congS ι q) i)) , λ α → Fold (mapProc' _ _ (lift swap) (Unfold (P α))))) stepν    
    where
      r : stepν (mapSProc' _ _ swap (binp _ , P)) ≡ _
      r = congS stepν (StepPath refl (congS binp (snoc-ι _ _ _ ∙ snoc-fresh _ _)) refl) ∙ no-stepν (binp refl)
  stepν-swap (binp ch0 , P) | nope (binp p) =
    sym (congS stepνF r ∙ no-stepν (binp refl))
    ∙ λ i → bind (stepν (binp (swap (sym p i)) , λ α → Fold (mapProc' _ _ (lift swap) (Unfold (P α))))) stepν        
    where
      r : stepν (mapSProc' _ _ swap (binp _ , P)) ≡ _
      r = congS stepν (StepPath refl (congS binp (snoc-fresh _ _)) refl) ∙ stepν-binp
  stepν-swap (τ , P) = congS η (congS `τ (later-ext \ α → ih α .swapνX))
  
  ν-swap : ∀ {n} {P : Proc (suc (suc n))} → νProc (νProc P) ≡ νProc (νProc (mapProc _ _ swap P))
  ν-swap {n} {P} =
    νProc (νProc P)
      ≡⟨ cong (λ x → isPi-alg.νX (x _) (isPi-alg.νX (x _) P)) (fix-eq ProcPi-algF) ⟩
    Fold (bind (bind (Unfold P) stepν) stepν)
      ≡⟨ cong Fold (bind-bind (Unfold P) stepν stepν) ⟩
    Fold (bind (Unfold P) (λ x → bind (stepν x) stepν))
      ≡⟨ cong Fold (congS (bind (Unfold P)) (funExt stepν-swap)) ⟩
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
    ; cong·X = λ {_}{_}{_}{_}{a} → congS (actProc a)
    ; cong⊕X = λ eq1 eq2 → cong₂ sumProc eq1 eq2
    ; cong∣∣X = λ eq1 eq2 → cong₂ parProc eq1 eq2
    ; congνX = congS νProc
    ; congguardX = congS (guardProc _ _)
    ; cong!X = congS !Proc
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


              

