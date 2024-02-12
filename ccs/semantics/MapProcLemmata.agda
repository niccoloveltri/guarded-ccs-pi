{-# OPTIONS --cubical --guarded -WnoUnsupportedIndexedMatch #-}
open import Cubical.Data.Sum hiding (inl; inr)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (lift)
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.Relation.Nullary
open import CountablePowerSet
open import LaterPrims hiding (_∙_)
open import AbsNames

module ccs.semantics.MapProcLemmata (ns : Names) where

open Names ns
open OpNames ns
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
import ccs.Syntax 
open import ccs.Syntax ns
open import ccs.Algebra ns
open import ccs.semantics.Algebra ns
open StepLemmata Proc (\ α n → ProcCCS-alg n) (mapProc _ _)
open Synch' 

-- This file contains lemmata about mapProc. We mainly show that
-- these action on renamings appropriately commute with the
-- CCS-operations in Proc (called endProc, actProc, sumProc, parProc,
-- νProc and !Proc). This is used to show that evaluation in Proc
-- respects actions on injective renamings.

-- mapProc and endProc.
end-map : ∀ {n m} (f : Name n → Name m) →
    mapProc n m f endProc ≡ endProc
end-map {n}{m} f =
  cong Fold (mapProc'-eq' _ _ _ _
            ∙ congS (mapProcF (next mapProc') _ _ f) (congS Unfold (cong (λ alg → isCCS-alg.endX (alg n)) (fix-eq ProcCCS-algF)))
            ∙ sym (cong Unfold (cong (λ alg → isCCS-alg.endX (alg m)) (fix-eq ProcCCS-algF))))

-- mapProc and actProc.
act-map : ∀ {n m} (f : Name n → Name m) a P →
  mapProc _ _ f (actProc a P) ≡ actProc (mapAct f a) (mapProc _ _ f P)
act-map {n}{m} f a P = 
  cong Fold (mapProc'-eq' _ _ _ _
            ∙ congS (mapProcF (next mapProc') _ _ f) (congS Unfold (cong (λ alg → isCCS-alg.actX (alg n) a P) (fix-eq ProcCCS-algF)))
            ∙ sym (congS Unfold (cong (λ alg → isCCS-alg.actX (alg m) (mapAct f a) (mapProc _ _ f P)) (fix-eq ProcCCS-algF))))

-- mapProc and sumProc.
sum-map : ∀ {n m} (f : Name n → Name m) P Q →
  mapProc n m f (sumProc P Q) ≡ sumProc (mapProc n m f P) (mapProc n m f Q)
sum-map {n}{m} f P Q =
  cong Fold (mapProc'-eq' _ _ _ _
            ∙ congS (mapProcF (next mapProc') _ _ f) (congS Unfold (cong (λ alg → isCCS-alg.sumX (alg n) P Q) (fix-eq ProcCCS-algF)))
            ∙ cong₂ _∪_ (sym (mapProc'-eq' _ _ _ _)) (sym (mapProc'-eq' _ _ _ _))
            ∙ sym (congS Unfold (cong (λ alg → isCCS-alg.sumX (alg _) (mapProc _ _ f P) (mapProc _ _ f Q)) (fix-eq ProcCCS-algF))))

-- mapProc and νProc (which requires some extra lemmata).
no-stepν-inp : ∀ {n} P → stepν (`inp (fresh n) P) ≡ ø
no-stepν-inp {n} P with canNu? (inp (fresh n))
no-stepν-inp P | inp x = ⊥-rec (fresh-ι (sym x))
no-stepν-inp P | nope x = refl

stepν-inp : ∀ {n} a P → stepν {n} (`inp (ι a) P) ≡ η (`inp a λ α → νProc (P α) )
stepν-inp a P with canNu? (inp (ι a))
stepν-inp a P | inp x = congS η (StepPath (congS inp (sym (ι-inj _ _ x))) refl)
stepν-inp a P | nope (inp x) = ⊥-rec (fresh-ι x)

stepν-out : ∀ {n} a P → stepν {n} (`out (ι a) P) ≡ η (`out a λ α → νProc (P α) )
stepν-out a P with canNu? (out (ι a))
stepν-out a P | out x = congS η (StepPath (congS out (sym (ι-inj _ _ x))) refl)
stepν-out a P | nope (out x) = ⊥-rec (fresh-ι x)

no-stepν : ∀ {n} {aP : Step (\ n → ▹ Proc n) (suc n)} → CannotNu (theLabel aP) → stepν aP ≡ ø
no-stepν {n} {a , P} cn with canNu? a
... | nope _ = refl
no-stepν {n} {.(out _) , P} (out r) | out x = ⊥-rec (fresh-ι (sym x ∙ r))
no-stepν {n} {.(inp _) , P} (inp r) | inp x = ⊥-rec (fresh-ι (sym x ∙ r))
no-stepν {n} {.τ , P} () | τ

ν-mapF : ∀ n m (f : Name n → Name m) p
        (ih : ▹ (∀ n m f p → mapProc n m f (νProc p) ≡ νProc (mapProc _ _ (lift f) p)))
        → mapProc'-eq i1 _ _ f (stepν p) ≡ stepνF (mapProc'-eq i1 _ _ (lift f) (η p))
ν-mapF n m f (`out a P) ih with canNu? (out a) | canNu? (out (lift f a))
ν-mapF n m f (`out a P) ih | out r | out x with decName a (fresh n)
... | yes p = ⊥-rec (fresh-ι (sym x))
ν-mapF n m f (out a , P) ih | out {a = a₁} r | out x | no ¬p = 
  cong η (StepPath (congS out (ι-inj _ _ (cong ι (cong f lem) ∙ x))) (later-ext (λ α → ih α _ _ f (P α))))
    where
      lem : a₁ ≡ down a ¬p
      lem = J (λ y eq → (q : ¬ y ≡ fresh n) → a₁ ≡ down y q)
              (λ q → sym (down-ι q))
              (sym r) ¬p
ν-mapF n m f (`out a P) ih | out r | nope (out x) with decName a (fresh n)
... | yes p = ⊥-rec (fresh-ι (sym r ∙ p))
... | no ¬p = ⊥-rec (fresh-ι x)
ν-mapF n m f (`out a P) ih | nope (out r) | out x with decName a (fresh n)
... | yes p = ⊥-rec (fresh-ι (sym x))
... | no ¬p = ⊥-rec (¬p r)
ν-mapF n m f (`out a P) ih | nope (out refl') | nope (out x) = refl
ν-mapF n m f (`inp a P) ih with canNu? (inp a) | canNu? (inp (lift f a))
ν-mapF n m f (`inp a P) ih | inp {a = a₁} r | inp x with decName a (fresh n)
... | yes p = ⊥-rec (fresh-ι (sym x))
... | no ¬p =
  cong η (StepPath (congS inp (ι-inj _ _ (cong ι (cong f lem) ∙ x))) (later-ext (λ α → ih α _ _ f (P α))))
    where
      lem : a₁ ≡ down a ¬p
      lem = J (λ y eq → (q : ¬ y ≡ fresh n) → a₁ ≡ down y q)
              (λ q → sym (down-ι q))
              (sym r) ¬p
ν-mapF n m f (`inp a P) ih | inp r | nope (inp x) with decName a (fresh n)
... | yes p = ⊥-rec (fresh-ι (sym r ∙ p))
... | no ¬p = ⊥-rec (fresh-ι x)
ν-mapF n m f (`inp a P) ih | nope (inp r) | inp x with decName a (fresh n)
... | yes p = ⊥-rec (fresh-ι (sym x))
... | no ¬p = ⊥-rec (¬p r)
ν-mapF n m f (`inp a P) ih | nope (inp r) | nope (inp x) = refl
ν-mapF n m f (`τ P) ih = cong η (StepPath refl (later-ext (λ α → ih α _ _ f (P α))))

ν-map : ∀ n m (f : Name n → Name m) p
  → mapProc _ _ f (νProc p) ≡ νProc (mapProc _ _ (lift f) p)
ν-map = fix (\ ih n m f p → cong Fold (mapProc'-eq' _ _ f (Unfold (νProc p))) ∙ congS (\ p → Fold (mapProcF (next mapProc') _ _ f (Unfold p)))
      (cong (λ alg → isCCS-alg.νX (alg n) p) (fix-eq ProcCCS-algF))
      ∙ cong Fold
             (map-bind (Unfold p) _ _
              ∙ congS (bind (Unfold p)) (funExt \ v → ν-mapF n m f v ih)
              ∙ sym (bind-map (Unfold p) _ _))
      ∙ sym \ i → isCCS-alg.νX (fix-eq ProcCCS-algF i _) (Fold (mapProc'-eq' _ _ (lift f) (Unfold p) i)))


-- mapProc and parProc (which requires some extra lemmata).
synch'-out-inp : ∀ {n} {a a' : Name n} (f : ▹ ( ∀ {n} → Proc n → Proc n → Proc n)) P Q
                 → a ≡ a' → synch' f (`out a P) (`inp a' Q) ≡ η (`τ \ α → f α (P α) (Q α))
synch'-out-inp {n} {a} {a'} f P Q eq with decName a a'
... | no ¬p  = ⊥-rec (¬p eq)
... | yes _ = refl

no-synch'-out-inp : ∀ {n} {a a' : Name n} (f : ▹ (∀ {n} → Proc n → Proc n → Proc n)) P Q
                 → (a ≡ a' → ⊥) → synch' f (`out a P) (`inp a' Q) ≡ ø
no-synch'-out-inp {n} {a} {a'} f P Q ¬pr with decName a a'
... | no _ = refl
... | yes p = ⊥-rec (¬pr p)

stepL-map : (ih : ▹
      ((n₁ m₁ : ℕ) (f₁ : Inj n₁ m₁) (p₁ q₁ : Proc n₁) →
       mapProc n₁ m₁ (fst f₁) (parProc p₁ q₁) ≡
       parProc (mapProc n₁ m₁ (fst f₁) p₁) (mapProc n₁ m₁ (fst f₁) q₁)))
  → ∀ n m (f : Inj n m) p q
  → mapProc' n m (fst f) (stepL (Unfold p) q)
    ≡ stepL (Unfold (mapProc _ _ (fst f) p)) (mapProc _ _ (fst f) q)
stepL-map ih n m f p q =
  mapProc'-eq' _ _ _ (stepL (Unfold p) q) 
  ∙ mapmapP∞ _ _ (Unfold p)
  ∙ congS (λ x → mapP∞ x (Unfold p)) (funExt (λ x →
            StepPath refl (later-ext (λ α → ih α _ _ f _ _))))
  ∙ sym (mapmapP∞ _ _ (Unfold p))
  ∙ cong₂ stepL (sym (mapProc'-eq' _ _ _ (Unfold p))) refl

stepR-map : (ih : ▹
      ((n₁ m₁ : ℕ) (f₁ : Inj n₁ m₁) (p₁ q₁ : Proc n₁) →
       mapProc n₁ m₁ (fst f₁) (parProc p₁ q₁) ≡
       parProc (mapProc n₁ m₁ (fst f₁) p₁) (mapProc n₁ m₁ (fst f₁) q₁)))
  → ∀ n m (f : Inj n m) p q
  → mapProc' n m (fst f) (stepR p (Unfold q))
    ≡ stepR (mapProc _ _ (fst f) p) (Unfold (mapProc _ _ (fst f) q))
stepR-map ih n m f p q =
  mapProc'-eq' _ _ _ (stepR p (Unfold q)) 
  ∙ mapmapP∞ _ _ (Unfold q)
  ∙ congS (λ x → mapP∞ x (Unfold q)) (funExt (λ x →
            StepPath refl (later-ext (λ α → ih α _ _ f _ _))))
  ∙ sym (mapmapP∞ _ _ (Unfold q))
  ∙ cong₂ stepR refl (sym (mapProc'-eq' _ _ _ (Unfold q)))

synch'-map : ∀ n m (f : Inj n m) v v' (parX : ∀ {n} → Proc n → Proc n → Proc n)
        (ih : ▹ (∀ n m (f : Inj n m) p q → mapProc n m (fst f) (parX p q) ≡ parX (mapProc _ _ (fst f) p) (mapProc _ _ (fst f) q))) →
       mapProc'-eq i1 n m (fst f) (synch' (λ _ → parX) v v')
       ≡ synchF' (λ _ → parX) (mapProc'-eq i1 n m (fst f) (η v)) (mapProc'-eq i1 n m (fst f) (η v'))
synch'-map n m f (`out x P) (`out y Q)  parX ih = refl
synch'-map n m f (`out x P) (`inp y Q)  parX ih with decName x y 
synch'-map n m f (`out x P) (`inp y Q)  parX ih | yes eq  =
  sym (synch'-out-inp _ _ _ (cong (fst f) eq) 
  ∙ congS η (congS `τ (later-ext \ α → sym (ih α _ _ f _ _))))
synch'-map n m f (`out x P) (`inp y Q)  parX ih | no ¬eq =
  sym (no-synch'-out-inp _ _ _ \ x → ¬eq (f .snd _ _ x)) 
synch'-map n m f (`out x P) (`τ Q)  parX ih = refl
synch'-map n m f (`inp x P) (`out y Q)  parX ih = refl
synch'-map n m f (`inp x P) (`inp y Q)  parX ih = refl
synch'-map n m f (`inp x P) (`τ Q)  parX ih = refl
synch'-map n m f (`τ P) (`out y Q)  parX ih = refl
synch'-map n m f (`τ P) (`inp y Q)  parX ih = refl
synch'-map n m f (`τ P) (`τ Q)  parX ih = refl

synchF-eq : ∀ {n} (p q : F' n (\ _ → Proc))
  → synchF p q ≡ synchF' (λ _ → parProc) p q ∪ synchF' (next (λ x y → parProc y x)) q p
synchF-eq p q = congS (bind p) (funExt (λ _ → bind-∪ _ _ q)) ∙ bind-∪ _ _ p ∙ cong₂ _∪_ refl (bind-comm _ p q)

synch-map :
   (ih : ▹ (∀ n m (f : Inj n m) p q → mapProc n m (fst f) (parProc p q) ≡ parProc (mapProc _ _ (fst f) p) (mapProc _ _ (fst f) q))) →
   ∀ n m (f : Inj n m) v v'
    → mapProc'-eq' n m (fst f) (synch v v') i1 ≡ synchF (mapProc'-eq' n m (fst f) (η v) i1) (mapProc'-eq' n m (fst f) (η v') i1)
synch-map ih n m f v v' =
  cong₂ _∪_ (synch'-map n m f v v' parProc ih) (synch'-map n m f v' v (\ p' q' → parProc q' p') \ α n m f p' q' → ih α n m f q' p')
  ∙ sym (synchF-eq (mapProc'-eq' n m (fst f) (η v) i1) (mapProc'-eq' n m (fst f) (η v') i1))

synchF-map :
     (ih : ▹ (∀ n m (f : Inj n m) p q → mapProc n m (fst f) (parProc p q) ≡ parProc (mapProc _ _ (fst f) p) (mapProc _ _ (fst f) q))) →
     ∀ n m (f : Inj n m) v v'
    → mapProc' _ _ (fst f) (synchF v v') ≡ synchF (mapProc' _ _ (fst f) v) (mapProc' n m (fst f) v')
synchF-map ih n m f v v' =
  mapProc'-eq' _ _ _ _
  ∙ map-bind  v _ _
  ∙ congS (bind v) (funExt λ aP →
      map-bind  v' _ _
      ∙ congS (bind v') (funExt λ aQ →
          synch-map ih n m f aP aQ)
      ∙ sym (bind-map v' _ _))
  ∙ sym (bind-map v _ _)
  ∙ sym (cong₂ synchF (mapProc'-eq' _ _ _ _) (mapProc'-eq' _ _ _ _))

par-map : ∀ n m (f : Inj n m) P Q →
  mapProc n m (fst f) (parProc P Q) ≡ parProc (mapProc _ _ (fst f) P) (mapProc _ _ (fst f) Q)
par-map = fix \ ih n m f P Q →
  cong Fold (mapProc'-eq' _ _ _ _
            ∙ congS (mapProcF (next mapProc') _ _ (fst f)) (congS Unfold (cong (λ alg → isCCS-alg.parX (alg n) P Q) (fix-eq ProcCCS-algF)))
            ∙ cong₂ _∪_ (cong₂ _∪_
                (sym (mapProc'-eq' _ _ _ _) ∙ stepL-map ih _ _ f P Q) 
                (sym (mapProc'-eq' _ _ _ _) ∙ stepR-map ih _ _ f P Q))
                (sym (mapProc'-eq' _ _ _ _) ∙ synchF-map ih _ _ f (Unfold P) (Unfold Q))
            ∙ sym (congS Unfold (cong (λ alg → isCCS-alg.parX (alg _) (mapProc _ _ (fst f) P) (mapProc _ _ (fst f) Q)) (fix-eq ProcCCS-algF))))

-- mapProc and !Proc.
rep-map : ∀ {n m} (f : Inj n m) (P : Proc n) →
  mapProc n m (fst f) (!Proc P) ≡ !Proc (mapProc _ _ (fst f) P) 
rep-map = fix λ ih f P →
  congS (mapProc _ _ (fst f)) (!Proc-eq {P = P})
  ∙ cong Fold
      (∪-map (fst f) _ _
      ∙ cong₂ _∪_ (stepL-map (next par-map) _ _ f P (!Proc P)
                  ∙ congS (stepL' (Unfold (mapProc _ _ (fst f) P))) (later-ext (λ α → ih α f P)))
                  (stepL-map (next par-map) _ _ f (Fold (synchF (Unfold P) (Unfold P))) (!Proc P)
                  ∙ cong₂ stepL' (synchF-map (next par-map) _ _ f (Unfold P) (Unfold P)) (later-ext (λ α → ih α f P))))
  ∙ sym (!Proc-eq {P = mapProc _ _ (fst f) P})

-- The main result of this file: evaluation into Proc respects actions
-- on injective renamings.
mapProc-evalX : ∀ {n m} (f : Inj m n) (p : CCS m) →
    evalX ProcCCS-alg (mapCCS (fst f) p)
    ≡ mapProc m n (fst f) (evalX ProcCCS-alg p)
mapProc-evalX f end = sym (end-map (fst f))
mapProc-evalX f (a · p) =
  cong₂ actProc refl (mapProc-evalX f p)
  ∙ sym (act-map (fst f) _ _)
mapProc-evalX f (p ⊕ q) =
  cong₂ sumProc (mapProc-evalX f p) (mapProc-evalX f q)
  ∙ sym (sum-map (fst f) _ _)
mapProc-evalX f (p ∣∣ q) =
  cong₂ parProc (mapProc-evalX f p) (mapProc-evalX f q)
  ∙ sym (par-map _ _ f _ _)
mapProc-evalX f (ν p) =
  congS νProc (mapProc-evalX (lift (fst f) , lift-inj f) p)
  ∙ sym (ν-map _ _ (fst f) _)
mapProc-evalX f (! p) =
  congS !Proc (mapProc-evalX f p)
  ∙ sym (rep-map f _)
