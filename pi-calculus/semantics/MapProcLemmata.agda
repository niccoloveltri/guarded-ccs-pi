{-# OPTIONS --cubical --guarded -WnoUnsupportedIndexedMatch #-}
open import Cubical.Data.Sum hiding (inl; inr) renaming (rec to rec⊎)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (lift)
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.Relation.Nullary
open import CountablePowerSet
open import LaterPrims hiding (_∙_)
open import AbsNames

module pi-calculus.semantics.MapProcLemmata (ns : Names) where

open Names ns
open OpNames ns
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
import pi-calculus.Syntax 
open import pi-calculus.Syntax ns
open import pi-calculus.Algebra ns
open import pi-calculus.semantics.Algebra ns
open StepLemmata Proc (\ α n → ProcPi-alg n) (mapProc _ _)
open Synch' 

-- This file contains lemmata about mapProc. We mainly show that these
-- action on renamings appropriately commute with the Pi-operations in
-- Proc (called endProc, actProc, sumProc, parProc, νProc, !Proc and
-- guardProc). This is used to show that evaluation in Proc respects
-- actions on renamings.

-- mapProc and endProc.

end-map : ∀ {n m} (f : Name n → Name m) →
      mapProc n m f endProc ≡ endProc
end-map {n}{m} f =
  cong Fold (mapProc'-eq' _ _ _ _
            ∙ congS (mapProcF (next mapProc') _ _ f) (congS Unfold (cong (λ alg → isPi-alg.endX (alg n)) (fix-eq ProcPi-algF)))
              ∙ sym (cong Unfold (cong (λ alg → isPi-alg.endX (alg m)) (fix-eq ProcPi-algF))))

-- mapProc and sumProc.
sum-map : ∀ {n m} (f : Name n → Name m) P Q →
  mapProc n m f (sumProc P Q) ≡ sumProc (mapProc n m f P) (mapProc n m f Q)
sum-map {n}{m} f P Q =
  cong Fold (mapProc'-eq' _ _ _ _
            ∙ congS (mapProcF (next mapProc') _ _ f) (congS Unfold (cong (λ alg → isPi-alg.sumX (alg n) P Q) (fix-eq ProcPi-algF)))
            ∙ cong₂ _∪_ (sym (mapProc'-eq' _ _ _ _)) (sym (mapProc'-eq' _ _ _ _))
            ∙ sym (congS Unfold (cong (λ alg → isPi-alg.sumX (alg m) (mapProc _ _ f P) (mapProc _ _ f Q)) (fix-eq ProcPi-algF))))

-- mapProc and guardProc.

guard-map' : ∀ {n m} (f : Inj n m) (x y : Name n) (P : Proc n) →
  mapProcF (λ _ → mapProc') n m (fst f) (stepguard x y (Unfold P)) ≡
  stepguard (fst f x) (fst f y) (mapProcF (λ _ → mapProc') n m (fst f) (Unfold P))
guard-map' f x y P with decName x y | decName (fst f x) (fst f y)
guard-map' f x y P | yes p | yes p₁ = refl
guard-map' f x y P | yes p | no ¬p = ⊥-rec (¬p (cong (fst f) p))
guard-map' f x y P | no ¬p | yes p = ⊥-rec (¬p (snd f _ _ p))
guard-map' f x y P | no ¬p | no ¬p₁ = refl

guard-map : ∀ {n m} (f : Inj n m) x y P →
  mapProc n m (fst f) (guardProc x y P) ≡ guardProc (fst f x) (fst f y) (mapProc n m (fst f) P)
guard-map {n}{m} f x y P =
  cong Fold (mapProc'-eq' _ _ _ _
            ∙ congS (mapProcF (next mapProc') _ _ (fst f)) (congS Unfold (cong (λ alg → isPi-alg.guardX (alg n) x y P) (fix-eq ProcPi-algF)))
            ∙ guard-map' f x y P
            ∙ congS (stepguard _ _) (sym (mapProc'-eq' _ _ _ _))
            ∙ sym (congS Unfold (cong (λ alg → isPi-alg.guardX (alg m) (fst f x) (fst f y) (mapProc _ _ (fst f) P)) (fix-eq ProcPi-algF))))

-- mapProc and νProc (which requires some extra lemmata).
no-stepν-inp : ∀ {n} v P → stepν (`inp (fresh n) v P) ≡ ø
no-stepν-inp {n} v P with canNu? (inp (fresh n) v)
no-stepν-inp v P | inp x _ = ⊥-rec (fresh-ι (sym x))
no-stepν-inp v P | nope x = refl

stepν-inp : ∀ {n} ch v P → stepν {n} (`inp (ι ch) (ι v) P) ≡ η (`inp ch v λ α → νProc (P α) )
stepν-inp ch v P with canNu? (inp (ι ch) (ι v))
stepν-inp ch v P | inp {ch = ch'}{v'} x x₁ =
  congS η (StepPath refl (sym λ i → inp (ι-inj ch ch' x i) (ι-inj v v' x₁ i)) refl)
stepν-inp ch v P | nope (inp (_⊎_.inl x)) = ⊥-rec (fresh-ι (x))
stepν-inp ch v P | nope (inp (_⊎_.inr x)) = ⊥-rec (fresh-ι (x))

stepν-out : ∀ {n} ch v P → stepν {n} (`out (ι ch) (ι v) P) ≡ η (`out ch v λ α → νProc (P α) )
stepν-out ch v P with canNu? (out (ι ch) (ι v))
stepν-out ch v P | out2 x x₁ = ⊥-rec (fresh-ι (x₁))
stepν-out ch v P | out {ch = ch'}{v'} x x₁ =
  congS η (StepPath refl (sym (λ i → out (ι-inj _ ch' x i) (ι-inj _ v' x₁ i))) refl)
stepν-out ch v P | nope (out x) = ⊥-rec (fresh-ι (x))

stepν-bout : ∀ {n} {P : ▹ Proc _} {ch : Name n}
  → stepν (`bout (ι ch) P) ≡ η (`bout ch (λ α → νProc (mapProc _ _ swap (P α))))
stepν-bout {n} {P} {ch} with canNu? (bout (ι ch))
... | nope (bout eq) = ⊥-rec (fresh-ι (eq))
... | bout eq = cong η (StepPath refl (λ i → bout (ι-inj _ _ eq (~ i))) refl)

stepν-binp : ∀ {n} {P : ▹ Proc _} {ch : Name n}
  → stepν (`binp (ι ch) P) ≡ η (`binp ch (λ α → νProc (mapProc _ _ swap (P α))))
stepν-binp {n} {P} {ch} with canNu? (binp (ι ch))
... | nope (binp eq) = ⊥-rec (fresh-ι (eq))
... | binp eq = cong η (StepPath refl (λ i → binp (ι-inj _ _ eq (~ i))) refl)

no-stepν : ∀ {n} {aP : Step (\ n → ▹ Proc n) (suc n)} → CannotNu (theLabel aP) → stepν aP ≡ ø
no-stepν {n} {a , P} cn with canNu? a
... | nope _ = refl
no-stepν {n} {.(out _ _) , P} (out r) | out x₁ x₂ = ⊥-rec (fresh-ι (sym x₁ ∙ r))
no-stepν {n} {.(out _ _) , P} (out r) | out2 x₁ x₂ = ⊥-rec (fresh-ι (sym x₁ ∙ r))
no-stepν {n} {.(inp _ _) , P} (inp (_⊎_.inl x)) | inp r r' = ⊥-rec (fresh-ι (sym r ∙ x))
no-stepν {n} {.(inp _ _) , P} (inp (_⊎_.inr x)) | inp r r' = ⊥-rec (fresh-ι (sym r' ∙ x))
no-stepν {n} {.(bout _) , P} (bout r) | bout x₁ = ⊥-rec (fresh-ι (sym x₁ ∙ r)) 
no-stepν {n} {.(binp _) , P} (binp r) | binp x₁ = ⊥-rec (fresh-ι (sym x₁ ∙ r))
no-stepν {n} {.τ , P} () | τ

abstract
  no-stepνF-inps' : ∀ {n m} (f : Name n → Name m) P
    → stepνF (inps' (\ _ → mapProc') (lift f) (fresh n) P) ≡ ø
  no-stepνF-inps' f P =
    congS stepνF (inps'-eq (\ _ → mapProc') _ _ _)
    ∙ bind-bind (neg (image (lift f)) (image-fn _)) _ _
    ∙ cong (bind (neg (image (lift f)) (image-fn _)))
        (funExt λ v → congS stepν (StepPath refl (congS (λ x → inp x v) (lift-fresh f)) refl) ∙ no-stepν-inp v _)
    ∙ bind-ø (neg (image (lift f)) (image-fn _))

  stepνF-inps' : ∀ {n m} ch (f : Inj n m) P →
    (ih : ▹ (∀ n m (f : Inj n m) p
      → mapProc _ _ (fst f) (νProc p) ≡ νProc (mapProc _ _ (lift (fst f)) p))) →
    stepνF (inps' (\ _ → mapProc') (lift (fst f)) (ι ch) P) ≡
      inps' (λ _ → mapProc') (fst f) ch (λ α → νProc (mapProc _ _ swap (P α)))
  stepνF-inps' ch f P ih =
    congS stepνF (inps'-eq (\ _ → mapProc') _ _ _)
    ∙ bind-bind (neg (image (lift (fst f))) (image-fn _)) _ _
    ∙ cong₂ bind (neg-image-lift (fst f)) refl
    ∙ bind-map (neg (image (fst f)) (image-fn _)) _ _
    ∙ cong-bind (neg (image (fst f)) (image-fn _)) (λ z m →
        congS stepν (StepPath refl (congS (λ x → inp x (ι z)) (lift-ι (fst f) ch)) refl)
        ∙ stepν-inp (fst f ch) z _
        ∙ cong η (congS (`inp (fst f ch) z) (later-ext (λ α → cong νProc (congS (λ y → mapProc _ _ y (P α)) (funExt (snoc-lift-ι (fst f) z))
                                                                         ∙ sym (mapmapProc _ _ _ (_ , lift-inj (_ , snoc-inj f z m)) (_ , swap-inj) _))
                                                                ∙ sym (ih α _ _ (_ , snoc-inj f z m) (mapProc _ _ swap (P α)))))))
    ∙ sym (inps'-eq (\ _ → mapProc') _ _ _)

ν-mapF : ∀ n m (f : Inj n m) p
        (ih : ▹ (∀ n m (f : Inj n m) p →
          mapProc _ _ (fst f) (νProc p) ≡ νProc (mapProc _ _ (lift (fst f)) p)))
        → mapProc'-eq i1 _ _ (fst f) (stepν p) ≡ stepνF (mapProc'-eq i1 _ _ (lift (fst f)) (η p))
ν-mapF n m f (`out ch z P) ih with canNu? (out ch z) | canNu? (out (lift (fst f) ch) (lift (fst f) z))
... | out {ch = ch'}{z'} r r' | out p p' with decName ch (fresh _) | decName z (fresh _)
... | yes q | q' = ⊥-rec (fresh-ι (sym p))
... | no q | yes q' = ⊥-rec (fresh-ι (sym p'))
... | no q | no q' =
  cong η (StepPath refl
                   (λ i → out (ι-inj _ _ ((λ i → ι (fst f (lem (~ i)))) ∙ p) i)
                               (ι-inj _ _ ((λ i → ι (fst f (lem' (~ i)))) ∙ p') i))
                   (later-ext (\ α → ih α _ _ f (P α))))
  where
    lem : down _ q ≡ ch'
    lem = J (λ x eq → (q : ¬ x ≡ fresh n) → down x q ≡ ch')
             down-ι
            (sym r)
            q
    lem' : down _ q' ≡ z'
    lem' = J (λ x eq → (q : ¬ x ≡ fresh n) → down x q ≡ z')
             down-ι
            (sym r')
            q'
ν-mapF n m f (`out ch z P) ih | out r r' | out2 p p' with decName ch (fresh _) | decName z (fresh _)
... | yes q | q' = ⊥-rec (fresh-ι (sym p))
... | no q | yes q' = ⊥-rec (fresh-ι (sym r' ∙ q'))
... | no q | no q' = ⊥-rec (fresh-ι p')
ν-mapF n m f (`out ch z P) ih | out r r' | nope (out p) with decName ch (fresh _)
... | yes q = ⊥-rec (fresh-ι (sym r ∙ q))
... | no q = ⊥-rec (fresh-ι p)
ν-mapF n m f (`out ch z P) ih | out2 r r' | out p p' with decName ch (fresh _) | decName z (fresh _)
... | yes q | q' = ⊥-rec (fresh-ι (sym p))
... | no q | yes q' = ⊥-rec (fresh-ι (sym p'))
... | no q | no q' = ⊥-rec (q' r')
ν-mapF n m f (`out ch z P) ih | out2 {ch = ch'} r r' | out2 p p' with decName ch (fresh _) | decName z (fresh _)
... | yes q | q' = ⊥-rec (fresh-ι (sym p))
... | no q | yes q' =
  cong η (StepPath refl
                   (congS bout (ι-inj _ _ (cong ι (cong (fst f) (sym lem)) ∙ p)))
                   (later-ext (λ _ → refl)))
  where                   
    lem : down _ q ≡ ch'
    lem = J (λ x eq → (q : ¬ x ≡ fresh n) → down x q ≡ ch')
             down-ι
            (sym r)
            q      
... | no q | no q' = ⊥-rec (q' r')
ν-mapF n m f (`out ch z P) ih | out2 r r' | nope (out p) with decName ch (fresh _)
... | yes q = ⊥-rec (fresh-ι (sym r ∙ q))
... | no q = ⊥-rec (fresh-ι p)
ν-mapF n m f (`out ch z P) ih | nope (out r) | out p p' with decName ch (fresh _) | decName z (fresh _)
... | yes q | q' = ⊥-rec (fresh-ι (sym p))
... | no q | yes q' = ⊥-rec (fresh-ι (sym p'))
... | no q | no q' = ⊥-rec (q r)
ν-mapF n m f (`out ch z P) ih | nope (out r) | out2 p p' with decName ch (fresh _)
... | yes q = ⊥-rec (fresh-ι (sym p))
... | no q = ⊥-rec (q r)
ν-mapF n m f (`out ch z P) ih | nope (out r) | nope (out p) = refl
ν-mapF n m f (`bout ch P) ih with canNu? (bout ch) | canNu? (bout (lift (fst f) ch))
ν-mapF n m f (`bout ch P) ih | bout {ch = ch'} r | bout p with decName ch (fresh _)
... | yes q = ⊥-rec (fresh-ι (sym p))
... | no q =
  cong η (StepPath refl
                   (congS bout (ι-inj _ _ (cong ι (cong (fst f) (sym lem)) ∙ p)))
    (later-ext (λ α → ih α _ _ (lift (fst f) , lift-inj f) (mapProc (suc (suc n)) (suc (suc n)) swap (P α))
                      ∙ congS νProc (mapmapProc _ _ _ (_ , lift-inj (_ , lift-inj f)) (_ , swap-inj) (P α)
                                  ∙ congS (λ g → mapProc _ _ g (P α)) (funExt (swap-lift (fst f)))
                                  ∙ sym (mapmapProc _ _ _ (_ , swap-inj) (_ , lift-inj (_ , lift-inj f)) (P α))))))
  where                   
    lem : down _ q ≡ ch'
    lem = J (λ x eq → (q : ¬ x ≡ fresh n) → down x q ≡ ch')
             down-ι
            (sym r)
            q                         
ν-mapF n m f (`bout ch P) ih | bout r | nope (bout p) with decName ch (fresh _)
... | yes q = ⊥-rec (fresh-ι (sym r ∙ q))
... | no q = ⊥-rec (fresh-ι p)
ν-mapF n m f (`bout ch P) ih | nope (bout r) | bout p with decName ch (fresh _)
... | yes q = ⊥-rec (fresh-ι (sym p))
... | no q = ⊥-rec (q r)
ν-mapF n m f (`bout ch P) ih | nope (bout r) | nope (bout p) = refl
ν-mapF n m f (`inp ch z P) ih with canNu? (inp ch z) | canNu? (inp (lift (fst f) ch) (lift (fst f) z))
... | inp {ch = ch'}{z'} r r' | inp p p' with decName ch (fresh _) | decName z (fresh _)
... | yes q | q' = ⊥-rec (fresh-ι (sym p))
... | no q | yes q' = ⊥-rec (fresh-ι (sym p'))
... | no q | no q' =
  cong η (StepPath refl
                   (λ i → inp (ι-inj _ _ ((λ i → ι (fst f (lem (~ i)))) ∙ p) i)
                               (ι-inj _ _ ((λ i → ι (fst f (lem' (~ i)))) ∙ p') i))
                   (later-ext (\ α → ih α _ _ f (P α))))
  where
    lem : down _ q ≡ ch'
    lem = J (λ x eq → (q : ¬ x ≡ fresh n) → down x q ≡ ch')
             down-ι
            (sym r)
            q
    lem' : down _ q' ≡ z'
    lem' = J (λ x eq → (q : ¬ x ≡ fresh n) → down x q ≡ z')
             down-ι
            (sym r')
            q'
ν-mapF n m f (`inp ch z P) ih | inp r r' | nope (inp p) with decName ch (fresh _) | decName z (fresh _)
... | yes q | q' = ⊥-rec (fresh-ι (sym r ∙ q))
... | no q | yes q' = ⊥-rec (fresh-ι (sym r' ∙ q'))
... | no q | no q' = ⊥-rec (rec⊎ fresh-ι fresh-ι p)
ν-mapF n m f (`inp ch z P) ih | nope (inp r) | inp p p' with decName ch (fresh _) | decName z (fresh _)
... | yes q | q' = ⊥-rec (fresh-ι (sym p))
... | no q | yes q' = ⊥-rec (fresh-ι (sym p'))
... | no q | no q' = ⊥-rec (rec⊎ q q' r)
ν-mapF n m f (`inp ch z P) ih | nope (inp r) | nope (inp p) = refl
ν-mapF n m f (`binp ch P) ih with canNu? (binp ch) | canNu? (binp (lift (fst f) ch))
ν-mapF n m f (`binp ch P) ih | binp {ch = ch'} r | binp p with decName ch (fresh _)
... | yes q = ⊥-rec (fresh-ι (sym p))
... | no q =
  cong₂ _∪_ (cong η (StepPath refl
                              (congS binp (ι-inj _ _ (cong ι (cong (fst f) (sym lem)) ∙ p)))
              (later-ext (λ α →  ih α _ _ (lift (fst f) , lift-inj f) (mapProc (suc (suc n)) (suc (suc n)) swap (P α))
                                 ∙ congS νProc (mapmapProc _ _ _ (_ , lift-inj (_ , lift-inj f)) (_ , swap-inj) (P α)
                                            ∙ congS (λ g → mapProc _ _ g (P α)) (funExt (swap-lift (fst f)))
                                            ∙ sym (mapmapProc _ _ _ (_ , swap-inj) (_ , lift-inj (_ , lift-inj f)) (P α)))))))
            (sym ((λ i → stepνF (inps' (λ _ → mapProc') (lift (fst f)) (r i) P)) ∙ stepνF-inps' _ f P ih))
  where                   
    lem : down _ q ≡ ch'
    lem = J (λ x eq → (q : ¬ x ≡ fresh n) → down x q ≡ ch')
             down-ι
            (sym r)
            q                         
ν-mapF n m f (`binp ch P) ih | binp r | nope (binp p) with decName ch (fresh _)
... | yes q = ⊥-rec (fresh-ι (sym r ∙ q))
... | no q = ⊥-rec (fresh-ι p)
ν-mapF n m f (`binp ch P) ih | nope (binp r) | binp p with decName ch (fresh _)
... | yes q = ⊥-rec (fresh-ι (sym p))
... | no q = ⊥-rec (q r)
ν-mapF n m f (`binp ch P) ih | nope (binp r) | nope (binp p) with decName ch (fresh _) 
... | yes q =
  sym (comm _ _ ∙  unit _ ∙ (λ i → bind (inps' (λ _ → mapProc') (lift (fst f)) (r i) P) stepν) ∙ no-stepνF-inps' (fst f) P)
... | no q = ⊥-rec (fresh-ι p)
ν-mapF n m f (`τ P) ih = cong η (StepPath refl refl (later-ext (λ α → ih α _ _ f (P α))))

ν-map : ∀ n m (f : Inj n m) p
  → mapProc _ _ (fst f) (νProc p) ≡ νProc (mapProc _ _ (lift (fst f)) p)
ν-map = fix (\ ih n m f p → cong Fold (mapProc'-eq' _ _ (fst f) (Unfold (νProc p))) ∙ congS (\ p → Fold (mapProcF (next mapProc') _ _ (fst f) (Unfold p)))
      (cong (λ alg₁ → isPi-alg.νX (alg₁ n) p) (fix-eq ProcPi-algF)) ∙ cong Fold (bind-bind (Unfold p) _ _ )
      ∙ cong Fold (cong₂ bind (\ _ → Unfold p) (funExt \ v → ν-mapF n m f v ih))
      ∙ sym (cong Fold (bind-bind (Unfold p) _ _))
      ∙ sym \ i → isPi-alg.νX (fix-eq ProcPi-algF i _) (Fold (mapProc'-eq' _ _ (lift (fst f)) (Unfold p) i)))

-- mapProc and parProc (which requires some extra lemmata).
synch'-out-inp : ∀ {n} {ch ch' : Name n}
  → (f : ▹ (∀ {n} → Proc n → Proc n → Proc n)) 
  → (g : ▹ (∀ {n} → Proc (suc n) → Proc n))
  → ∀ {z z'} P Q → ch ≡ ch' → z ≡ z'
  → synch' f g (`out ch z P) (`inp ch' z' Q) ≡ η (`τ \ α → f α (P α) (Q α))
synch'-out-inp {n} {ch} {ch'} f g {z} {z'} P Q eqch eqz with decName ch ch' | decName z z'
... | no ¬p | _ = ⊥-rec (¬p eqch)
... | yes _ | no ¬r = ⊥-rec (¬r eqz)
... | yes _ | yes _ = refl

no-synch'-out-inp : ∀ {n} {ch ch' : Name n}
  → (f : ▹ (∀ {n} → Proc n → Proc n → Proc n))
  → (g : ▹ (∀ {n} → Proc (suc n) → Proc n))
  → ∀ {z z'} P Q → (ch ≡ ch' → z ≡ z' → ⊥)
  → synch' f g (`out ch z P) (`inp ch' z' Q) ≡ ø
no-synch'-out-inp {n} {ch} {ch'} f g {z} {z'} P Q ¬pr with decName ch ch' | decName z z'
... | no _ | _ = refl
... | yes _ | no _ = refl
... | yes p | yes r = ⊥-rec (¬pr p r)

synch'-bout-binp : ∀ {n} {ch ch' : Name n}
  → (f : ▹ (∀ {n} → Proc n → Proc n → Proc n))
  → (g : ▹ (∀ {n} → Proc (suc n) → Proc n))
  → ∀ P Q → ch ≡ ch'
  → synch' f g (`bout ch P) (`binp ch' Q) ≡ η (`τ \ α → g α (f α (P α) (Q α)))
synch'-bout-binp {n} {ch} {ch'} f g P Q eqch with decName ch ch'
... | no ¬eq = ⊥-rec (¬eq eqch)
... | yes _ = refl

no-synch'-bout-binp : ∀ {n} {ch ch' : Name n}
  → (f : ▹ (∀ {n} → Proc n → Proc n → Proc n))
  → (g : ▹ (∀ {n} → Proc (suc n) → Proc n))
  → ∀ P Q → (ch ≡ ch' → ⊥) → synch' f g (`bout ch P) (`binp ch' Q) ≡ ø
no-synch'-bout-binp {n} {ch} {ch'} f g P Q ¬eqch with decName ch ch'
... | yes eqch = ⊥-rec (¬eqch eqch)
... | no ¬eq = refl

stepL-map : (ih : ▹
      ((n₁ m₁ : ℕ) (f₁ : Inj n₁ m₁) (p₁ q₁ : Proc n₁) →
       mapProc n₁ m₁ (fst f₁) (parProc p₁ q₁) ≡
       parProc (mapProc n₁ m₁ (fst f₁) p₁) (mapProc n₁ m₁ (fst f₁) q₁)))
      → ∀ n m (f : Inj n m) p q → mapProc' n m (fst f) (stepL (Unfold p) q) ≡ stepL (Unfold (mapProc _ _ (fst f) p)) (mapProc _ _ (fst f) q)
stepL-map ih n m f p q = mapProc'-eq' _ _ _ (stepL (Unfold p) q) ∙ (bind-map (Unfold p) _ _
                       ∙ congS (bind (Unfold p))
                          (funExt \ v → inps-eq (fst f) (mapStep (λ m₁ i x α → parProc (x α) (mapProc n m₁ (fst i) q)) v) _
                          ∙ cong₂ _∪_ (cong η (StepPath refl refl (later-ext \ α → ih α _ _ (labelRen (theLabel v) m (fst f) , labelRen-inj _ _ f) _ _ ∙
                                                                  cong₂ parProc refl (mapmapProc _ _ _ (_ , labelRen-inj (theLabel v) m f) (labelInj (theLabel v)) q
                                                                 ∙ cong₂ (mapProc _ _) (funExt \ x → labelRenInj (fst f) (theLabel v)) refl
                                                                 ∙ sym (mapmapProc _ _ _ (labelInj (mapLabel (fst f) (theLabel v))) f q)))))
                                       (inps-lemma v)
                          ∙ cong (mapP∞ _) (sym (inps-eq (fst f) v _)))
                       ∙ sym (map-bind (Unfold p) _ _)) ∙ cong₂ stepL (sym (mapProc'-eq' _ _ _ (Unfold p))) refl
  where
    inps-lemma : ∀ v → inps'2 (fst f) (mapStep (λ m₁ i x α → parProc (x α) (mapProc n m₁ (fst i) q)) v) ≡
                 mapP∞ (mapStep (λ m₁ i x α → parProc (x α) (mapProc m m₁ (fst i) (Fold (mapProc' n m (fst f) (Unfold q)))))) (inps'2 (fst f) v)
    inps-lemma (b , Q') with binp? b
    inps-lemma (.(binp _) , Q') | binp {ch} = inps'-eq (\ _ → mapProc') (fst f) _ _
                                         ∙  cong-bind (neg (image (fst f)) (image-fn _)) (\ v mv →
                                             congS η ( congS (`inp (fst f ch) v) (later-ext \ α →  ih α _ _ (snoc (fst f) v , snoc-inj f v mv) _ _ ∙ cong₂ parProc refl
                                                 (mapmapProc _ _ _ (_ , snoc-inj f v mv) (_ , ι-inj) q ∙ cong₂ (mapProc _ _) (funExt \ v → snoc-ι _ _ v) refl ∙
                                                   sym (mapmapProc _ _ _ (_ , \ _ _ p → p) f q))  ) )  )
                                         ∙ sym (map-bind (neg (image (fst f)) (image-fn _)) _ _)
                                         ∙ cong₂ mapP∞ refl (sym (inps'-eq (\ _ → mapProc') (fst f) _ _))
    inps-lemma (b , Q') | nope = refl

stepR-map : (ih : ▹
      ((n₁ m₁ : ℕ) (f₁ : Inj n₁ m₁) (p₁ q₁ : Proc n₁) →
       mapProc n₁ m₁ (fst f₁) (parProc p₁ q₁) ≡
       parProc (mapProc n₁ m₁ (fst f₁) p₁) (mapProc n₁ m₁ (fst f₁) q₁)))
      → ∀ n m (f : Inj n m) p q → mapProc' n m (fst f) (stepR p (Unfold q)) ≡ stepR (mapProc _ _ (fst f) p) (Unfold (mapProc _ _ (fst f) q))
stepR-map ih n m f p q = mapProc'-eq' _ _ _ (stepR p (Unfold q)) ∙ (bind-map (Unfold q) _ _
                       ∙ congS (bind (Unfold q))
                          ( (funExt \ v → inps-eq (fst f) (mapStep (λ m₁ i x α → parProc (mapProc n m₁ (fst i) p) (x α)) v) _
                          ∙ cong₂ _∪_ (cong η (StepPath refl refl (later-ext \ α → ih α _ _ (labelRen (theLabel v) m (fst f) , labelRen-inj _ _ f) _ _ ∙
                                                                  cong₂ parProc (mapmapProc _ _ _ (_ , labelRen-inj _ _ f) (labelInj (theLabel v)) p
                                                                 ∙ cong₂ (mapProc _ _) (funExt \ x → labelRenInj (fst f) (theLabel v)) refl
                                                                 ∙ sym (mapmapProc _ _ _ (labelInj (mapLabel (fst f) (theLabel v))) f p)) refl)))
                                       ( (inps-lemma v) )
                          ∙ cong (mapP∞ _) (sym (inps-eq (fst f) v _))) )
                       ∙ sym (map-bind (Unfold q) _ _)) ∙ cong₂ stepR refl (sym (mapProc'-eq' _ _ _ (Unfold q)))
  where
    inps-lemma : ∀ v → inps'2 (fst f) (mapStep (λ m₁ i x α → parProc (mapProc n m₁ (fst i) p) (x α)) v) ≡
                 mapP∞ (mapStep (λ m₁ i x α → parProc (mapProc m m₁ (fst i) (Fold (mapProc' n m (fst f) (Unfold p)))) (x α))) (inps'2 (fst f) v)
    inps-lemma (b , Q') with binp? b
    inps-lemma (.(binp _) , Q') | binp {ch} =  inps'-eq (\ _ → mapProc') (fst f) _ _
                                         ∙  cong-bind (neg (image (fst f)) (image-fn _)) (\ v mv →
                                             congS η ( congS (`inp (fst f ch) v) (later-ext \ α →  ih α _ _ (snoc (fst f) v , snoc-inj f v mv) _ _
                                              ∙ cong₂ parProc
                                                 (mapmapProc _ _ _ (_ , snoc-inj f v mv) (_ , ι-inj) p
                                                   ∙ cong₂ (mapProc _ _) (funExt \ v → snoc-ι _ _ v) refl ∙ sym (mapmapProc _ _ _ (_ , \ _ _ p → p) f p)) refl  ) )  )
                                         ∙ sym (map-bind (neg (image (fst f)) (image-fn _)) _ _)
                                         ∙ cong₂ mapP∞ refl (sym (inps'-eq (\ _ → mapProc') (fst f) _ _))
    inps-lemma (b , Q') | nope = refl

synch'-map :
       ∀ n m (f : Inj n m) v v'
        (parX : ∀ {n} → Proc n → Proc n → Proc n) --(νX : ∀ {n} → Proc (suc n) → Proc n)
        (ih : ▹ (∀ n m (f : Inj n m) p q → mapProc n m (fst f) (parX p q) ≡ parX (mapProc _ _ (fst f) p) (mapProc _ _ (fst f) q))) →
       mapProc'-eq i1 n m (fst f) (synch' (λ _ → parX) (λ _ → νProc) v v') ≡ synchF' (λ _ → parX) (λ _ → νProc) (mapProc'-eq i1 n m (fst f) (η v)) (mapProc'-eq i1 n m (fst f) (η v'))
synch'-map n m f (`out x x₁ P) (`out x₂ x₃ Q) parX ih = refl
synch'-map n m f (`out x x₁ P) (`bout x₂ Q) parX ih = refl
synch'-map n m f (`out ch z P) (`inp ch' z' Q) parX ih with decName ch ch' | decName z z'
synch'-map n m f (`out ch z P) (`inp ch' z' Q) parX ih | yes p | yes p₁ = sym (synch'-out-inp _ _ _ _ (cong (fst f) p) (cong (fst f) p₁)
  ∙ congS η (congS `τ (later-ext \ α → sym (ih α _ _ f _ _))))
synch'-map n m f (`out ch z P) (`inp ch' z' Q) parX ih | yes p | no ¬p = sym (no-synch'-out-inp _ _ _ _ \ _ ze → ¬p (f .snd _ _ ze))
synch'-map n m f (`out ch z P) (`inp ch' z' Q) parX ih | no ¬p | q
  = sym (no-synch'-out-inp _ _ _ _ (\ che ze → ¬p (f .snd _ _ che)))
synch'-map n m f (`out x x₁ P) (`binp x₂ Q) parX ih = sym (idem _) ∙ cong₂ _∪_ refl (sym (cong₂ bind (inps'-eq _ _ _ Q) refl
          ∙ bind-bind (neg (image (fst f)) (image-fn _)) _ _
          ∙ cong-bind (neg (image (fst f)) (image-fn _)) (\ a am → no-synch'-out-inp _ _ _ _ (\ _ ze → neg-image-out a (fst f) am (sym ze)))
          ∙ bind-ø (neg (image (fst f)) (image-fn _))))
synch'-map n m f (`out x x₁ P) (`τ Q) parX ih = refl
synch'-map n m f (`bout x P) (`out x₁ x₂ Q) parX ih = refl
synch'-map n m f (`bout x P) (`bout x₁ Q) parX ih = refl
synch'-map n m f (`bout x P) (`inp x₁ x₂ Q) parX ih = refl
synch'-map n m f (`bout ch P) (`binp ch' Q) parX ih with decName ch ch'
synch'-map n m f (`bout ch P) (`binp ch' Q) parX ih | yes p = 
  (congS η (congS `τ (later-ext \ α → ν-map _ _ f _ ∙ cong νProc (ih α _ _ (_ , lift-inj f) _ _)))
  ∙ sym (unit _)) ∙ cong₂ _∪_ (sym (synch'-bout-binp _ _ _ _ (cong (fst f) p))) ((sym (cong₂ bind (inps'-eq _ _ _ Q) refl
          ∙ bind-bind (neg (image (fst f)) (image-fn _)) _ _
          ∙ bind-ø (neg (image (fst f)) (image-fn _)))))
synch'-map n m f (`bout ch P) (`binp ch' Q) parX ih | no ¬p = sym (idem _) ∙ cong₂ _∪_ (sym (no-synch'-bout-binp _ _ _ _ \ p → ¬p (f .snd _ _ p)))
  ((sym (cong₂ bind (inps'-eq _ _ _ Q) refl
          ∙ bind-bind (neg (image (fst f)) (image-fn _)) _ _
          ∙ bind-ø (neg (image (fst f)) (image-fn _)))))
synch'-map n m f (`bout x P) (`τ Q) parX  ih = refl
synch'-map n m f (`inp x x₁ P) (`out x₂ x₃ Q) parX ih = refl
synch'-map n m f (`inp x x₁ P) (`bout x₂ Q) parX ih = refl
synch'-map n m f (`inp x x₁ P) (`inp x₂ x₃ Q) parX ih = refl
synch'-map n m f (`inp x x₁ P) (`binp x₂ Q) parX ih = sym (idem _)
          ∙ cong₂ _∪_ refl (sym (cong₂ bind (inps'-eq _ _ _ Q) refl
          ∙ bind-bind (neg (image (fst f)) (image-fn _)) _ _
          ∙ bind-ø (neg (image (fst f)) (image-fn _))))
synch'-map n m f (`inp x x₁ P) (`τ Q) parX  ih = refl
synch'-map n m f (`binp x P) (`out x₁ x₂ Q) parX ih = sym (idem _)
  ∙ cong₂ _∪_ refl (sym (cong₂ bind (inps'-eq _ _ _ P) refl
  ∙ bind-bind (neg (image (fst f)) (image-fn _)) _ _
  ∙ bind-ø (neg (image (fst f)) (image-fn _))))
synch'-map n m f (`binp x P) (`bout x₁ Q) parX ih = sym (idem _)
  ∙ cong₂ _∪_ refl (sym (cong₂ bind (inps'-eq _ _ _ P) refl
  ∙ bind-bind (neg (image (fst f)) (image-fn _)) _ _
  ∙ bind-ø (neg (image (fst f)) (image-fn _))))
synch'-map n m f (`binp x P) (`inp x₁ x₂ Q) parX ih = sym (idem _)
  ∙ cong₂ _∪_ refl (sym (cong₂ bind (inps'-eq _ _ _ P) refl
  ∙ bind-bind (neg (image (fst f)) (image-fn _)) _ _
  ∙ bind-ø (neg (image (fst f)) (image-fn _))))
synch'-map n m f (`binp x P) (`binp x₁ Q) parX ih = sym (cong₂ _∪_ (idem _) refl ∙ idem _) ∙ cong₂ _∪_ (cong₂ _∪_ refl ((sym (cong₂ bind (inps'-eq _ _ _ Q) refl
          ∙ bind-bind (neg (image (fst f)) (image-fn _)) _ _
          ∙ bind-ø (neg (image (fst f)) (image-fn _)))))) (sym (cong₂ bind (inps'-eq _ _ _ P) refl ∙ bind-bind (neg (image (fst f)) (image-fn _)) _ _
                                              ∙ congS (bind (neg (image (fst f)) (image-fn _))) (funExt \ z →  cong₂ _∪_ refl (cong₂ bind (inps'-eq _ _ _ Q) refl
          ∙ bind-bind (neg (image (fst f)) (image-fn _)) _ _
          ∙ bind-ø (neg (image (fst f)) (image-fn _))) ∙ idem _) ∙ bind-ø (neg (image (fst f)) (image-fn _))))
synch'-map n m f (`binp x P) (`τ Q) parX ih = sym (idem _)
  ∙ cong₂ _∪_ refl (sym (cong₂ bind (inps'-eq _ _ _ P) refl
  ∙ bind-bind (neg (image (fst f)) (image-fn _)) _ _
  ∙ bind-ø (neg (image (fst f)) (image-fn _))))
synch'-map n m f (`τ P) (`out _ _ _) parX ih = refl
synch'-map n m f (`τ P) (`bout x Q) parX ih = refl
synch'-map n m f (`τ P) (`inp x x₁ Q) parX ih = refl
synch'-map n m f (`τ P) (`binp x Q) parX ih =
          sym (idem _)
          ∙ cong₂ _∪_ refl (sym (cong₂ bind (inps'-eq _ _ _ Q) refl
          ∙ bind-bind (neg (image (fst f)) (image-fn _)) _ _
          ∙ bind-ø (neg (image (fst f)) (image-fn _))))
synch'-map n m f (`τ P) (`τ Q) parX  ih = refl

synchF-eq : ∀ {n} (p q : F' n (\ _ → Proc))
  → synchF p q ≡ synchF' (λ _ → parProc) (λ _ → νProc) p q ∪ synchF' (next (λ x y → parProc y x)) (λ _ → νProc) q p
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
    ∙ bind-bind v _ _
    ∙ congS (bind v) (funExt (λ x →
        bind-bind v' _ _
        ∙ congS (bind v') (funExt (λ y → synch-map ih n m f x y))
        ∙ bind-comm _ v' (inps (next mapProc') (fst f) x  _)
        ∙ congS (bind (inps (next mapProc') (fst f) x  _)) (funExt (λ y → sym (bind-bind v' _ _)))))
    ∙ sym (bind-bind v _ _)
    ∙ sym (cong₂ synchF (mapProc'-eq' _ _ _ _) (mapProc'-eq' _ _ _ _))

par-map : ∀ n m (f : Inj n m) P Q →
  mapProc n m (fst f) (parProc P Q) ≡ parProc (mapProc _ _ (fst f) P) (mapProc _ _ (fst f) Q)
par-map = fix \ ih n m f P Q →
  cong Fold (mapProc'-eq' _ _ _ _
            ∙ congS (mapProcF (next mapProc') _ _ (fst f)) (congS Unfold (cong (λ alg → isPi-alg.parX (alg n) P Q) (fix-eq ProcPi-algF)))
            ∙ cong₂ _∪_ (cong₂ _∪_
                (sym (mapProc'-eq' _ _ _ _) ∙ stepL-map ih _ _ f P Q) 
                (sym (mapProc'-eq' _ _ _ _) ∙ stepR-map ih _ _ f P Q))
                (sym (mapProc'-eq' _ _ _ _) ∙ synchF-map ih _ _ f (Unfold P) (Unfold Q))
            ∙ sym (congS Unfold (cong (λ alg → isPi-alg.parX (alg _) (mapProc _ _ (fst f) P) (mapProc _ _ (fst f) Q)) (fix-eq ProcPi-algF))))

-- mapProc and !Proc.

stepL-map' : ∀ {n m} (f : Inj n m) p q
  → mapProc' n m (fst f) (stepL (Unfold p) q)
     ≡ stepL (Unfold (mapProc _ _ (fst f) p)) (mapProc _ _ (fst f) q)
stepL-map' = stepL-map (next par-map) _ _

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

-- mapProc and actProc.
-- act-map : ∀ {n m} (f : Name n → Name m) a P →
--   mapProc _ _ f (actProc a P) ≡ actProc (mapAct f a) (mapProc _ _ f P)
-- act-map {n}{m} f a P = 
--   cong Fold (mapProc'-eq' _ _ _ _
--             ∙ congS (mapProcF (next mapProc') _ _ f) (congS Unfold (cong (λ alg → isCCS-alg.actX (alg n) a P) (fix-eq ProcCCS-algF)))
--             ∙ sym (congS Unfold (cong (λ alg → isCCS-alg.actX (alg m) (mapAct f a) (mapProc _ _ f P)) (fix-eq ProcCCS-algF))))

-- -- The main result of this file: evaluation into Proc respects actions
-- -- on injective renamings.
-- mapProc-evalX : ∀ {n m} (f : Inj m n) (p : CCS m) →
--     evalX ProcCCS-alg (mapCCS (fst f) p)
--     ≡ mapProc m n (fst f) (evalX ProcCCS-alg p)
-- mapProc-evalX f end = sym (end-map (fst f))
-- mapProc-evalX f (a · p) =
--   cong₂ actProc refl (mapProc-evalX f p)
--   ∙ sym (act-map (fst f) _ _)
-- mapProc-evalX f (p ⊕ q) =
--   cong₂ sumProc (mapProc-evalX f p) (mapProc-evalX f q)
--   ∙ sym (sum-map (fst f) _ _)
-- mapProc-evalX f (p ∣∣ q) =
--   cong₂ parProc (mapProc-evalX f p) (mapProc-evalX f q)
--   ∙ sym (par-map _ _ f _ _)
-- mapProc-evalX f (ν p) =
--   congS νProc (mapProc-evalX (lift (fst f) , lift-inj f) p)
--   ∙ sym (ν-map _ _ (fst f) _)
-- mapProc-evalX f (! p) =
--   congS !Proc (mapProc-evalX f p)
--   ∙ sym (rep-map f _)

-- mapProc-evalX : ∀ {n m} (f : Name m → Name n) (p : Pi m) →
--     evalX ProcPi-alg (mapPi f p)
--     ≡ mapProc m n f (evalX ProcPi-alg p)
-- mapProc-evalX f end = sym (end-map (f))
-- mapProc-evalX f (out ch v · p) = {!!}
-- mapProc-evalX f (inp ch · p) = {!!}
-- mapProc-evalX f (τ · p) = {!!}
-- mapProc-evalX f (p ⊕ q) =
--   cong₂ sumProc (mapProc-evalX f p) (mapProc-evalX f q)
--   ∙ sym (sum-map (f) _ _)
-- mapProc-evalX f (p ∣∣ q) =
--   cong₂ parProc (mapProc-evalX f p) (mapProc-evalX f q)
--   ∙ sym (par-map _ _ {!!} _ _)
-- mapProc-evalX f (ν p) =
--   congS νProc (mapProc-evalX (lift f) p)
--   ∙ sym (ν-map _ _ {!!} _)
-- mapProc-evalX f (! p) =
--   congS !Proc (mapProc-evalX f p)
--   ∙ sym (rep-map {!!} _)
