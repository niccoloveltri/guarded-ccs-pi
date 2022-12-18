{-# OPTIONS --cubical --guarded #-}

open import Cubical.Data.Sum hiding (inl; inr) 
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (lift)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary
open import CountablePowerSet
open import Basic
open import AbsNames
open import LaterPrims hiding (_∙_)

module pi-calculus.semantics.Dynamics (ns : Names) where

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

-- Here we show that the relation (λ P a P' → (a , next P') ← P) models
-- the early operational semantics of π-calculus.

-- An equivalent characterization of the type ⟨ (a , Q) ∈ synch' P1 P2
-- ⟩, when synch' is defined for a generic Pi-algebra X (as in the
-- module StepLemmata in pi-calculus.semantics.Algebra): this can only
-- happen if (a ≡ τ), (P1 ≡ out ch a' , P1'), (P2 ≡ inp ch a' , P2')
-- and (Q α = parX α (P1' α) (P2' α)) or when (a ≡ τ), (P1 ≡ bout ch ,
-- P1'), (P2 ≡ binp ch , P2') and (Q α = νX α (parX α (P1' α) (P2'
-- α))) (so when P1 and P2 can communicate)

module StepLemmata2
  (X : ℕ → Type)
  (X-alg : ▹ (∀ n → isPi-alg X n))
  (mapX : ∀ {n m} → (Name m → Name n) → X m → X n)
  where

  open StepLemmata X X-alg mapX

  module _ (parX : ▹ (∀ {n} → X n → X n → X n)) (νX : ▹ (∀ {n} → X (suc n) → X n)) where
    open Synch' parX νX

    synch'-in-f : ∀ {n} {m1 m2} {a1 : Label n m1}{a2 : Label n m2} {P1 : ▹ (X m1)} {P2} {aQ} →
      ∥ (Σ (▹ X (suc n)) \ P1' → Σ (▹ X (suc n)) \ P2' → Σ (Name n) \ ch → ((_,_ {X = \ n → ▹ X n} a1 P1) ≡ `bout ch P1') ×
                  ((_,_ {X = \ n → ▹ X n} a2 P2) ≡ (binp ch , P2')) ×
                    ((aQ) ≡ (`τ (\ α → νX α (parX α (P1' α) ((P2' α))) )))) ∥₁
      → ⟨ aQ ∈ synch' (a1 , P1) (a2 , P2) ⟩
    synch'-in-f {n}{m1}{m2}{a1}{a2}{P1}{P2}{aQ} = PT.rec (snd (aQ ∈ synch' (a1 , P1) (a2 , P2)))
      λ { (P1' , P2' , ch , eq1 , eq2 , eqn) →
         J (λ aP1' _ → ⟨ aQ ∈ synch' aP1' (a2 , P2) ⟩)
           (J (λ aP2' _ → ⟨ aQ ∈ synch' (`bout ch P1') aP2' ⟩)
             (subst (λ x → ⟨ x ∈ synch' (`bout ch P1') (`binp ch P2') ⟩) (sym eqn) lem)
             (sym eq2))
           (sym eq1) }
      where
        lem : ∀{P1' P2' ch} → ⟨ `τ (λ α → νX α (parX α (P1' α) (P2' α))) ∈ synch' (`bout ch P1') (`binp ch P2') ⟩
        lem {ch = ch}  with decName ch ch
        ... | yes _ = ∣ refl ∣₁
        ... | no r = r refl

    synch'-in-s : ∀ {n} {m1 m2} {a1 : Label n m1}{a2 : Label n m2} {P1 P2} {aQ} →
      ∥ (Σ (▹ X n) \ P1' → Σ (▹ X n) \ P2' → Σ (Name n) \ ch → Σ _ \ z → ((a1 , P1) ≡ `out ch z P1') ×
                 ((_,_ {X = \ n → ▹ X n} a2 P2) ≡ (inp ch z , P2')) ×
                   ((aQ) ≡ (`τ (\ α → parX α (P1' α) ((P2' α)) )))) ∥₁
      → ⟨ aQ ∈ synch' (a1 , P1) (a2 , P2) ⟩
    synch'-in-s {n}{m1}{m2}{a1}{a2}{P1}{P2}{aQ} = PT.rec (snd (aQ ∈ synch' (a1 , P1) (a2 , P2)))
      λ { (P1' , P2' , ch , z , eq1 , eq2 , eqn) →
        J (λ aP1' _ → ⟨ aQ ∈ synch' aP1' (a2 , P2) ⟩)
          (J (λ aP2' _ → ⟨ aQ ∈ synch' (`out ch z P1') aP2' ⟩)
            (subst (λ x → ⟨ x ∈ synch' (`out ch z P1') (`inp ch z P2') ⟩) (sym eqn) lem)
            (sym eq2))
          (sym eq1) }
      where
        lem : ∀{P1' P2' ch z} → ⟨ `τ (λ α → parX α (P1' α) (P2' α)) ∈ synch' (`out ch z P1') (`inp ch z P2') ⟩
        lem {ch = ch} with decName ch ch
        lem {z = z} | yes _ with decName z z
        lem         | yes _ | yes _ = ∣ refl ∣₁
        lem         | yes _ | no r = r refl
        lem         | no r  = r refl

    data synch'∈ {n} (P1 P2 aQ : Step (\ n → ▹ X n) n) : Set where
        synch'-s : ∀ (P1' P2' : ▹ X n) {ch z}
          → P1 ≡ `out ch z P1' → P2 ≡ `inp ch z P2'
          → aQ ≡ `τ (λ α → parX α (P1' α) (P2' α))
          → synch'∈ P1 P2 aQ
        synch'-f : ∀ (P1' P2' : ▹ X (suc n)) {ch}
          → P1 ≡ `bout ch P1' → P2 ≡ `binp ch P2'
          → aQ ≡ `τ (λ α → νX α (parX α (P1' α) (P2' α)))
          → synch'∈ P1 P2 aQ

    abstract
      synch'-in' : ∀ {n} {P1 P2 aQ : Step (\ n → ▹ X n) n}
        → synch'∈ P1 P2 aQ → ⟨ aQ ∈ synch' P1 P2 ⟩
      synch'-in' {P1 = P1}{P2} (synch'-s P1' P2' {ch} {z} p q r) =
        subst (λ x → ⟨ x ∈ synch' P1 P2 ⟩) (sym r) (subst2 (λ x y → ⟨ _ ∈ synch' x y ⟩) (sym p) (sym q) lem)
        where
          lem : ⟨ (τ , (λ α → parX α (P1' α) (P2' α))) ∈ synch' (out ch z , P1') (inp ch z , P2') ⟩
          lem with decName ch ch | decName z z
          lem | no ¬p | _ = ¬p refl
          lem | yes _ | yes _ = ∣ refl ∣₁
          lem | yes _ | no ¬q = ¬q refl
      synch'-in' {P1 = P1}{P2} (synch'-f P1' P2' {ch} p q r) = 
        subst (λ x → ⟨ x ∈ synch' P1 P2 ⟩) (sym r) (subst2 (λ x y → ⟨ _ ∈ synch' x y ⟩) (sym p) (sym q) lem)
        where
          lem : ⟨ (τ , (λ α → νX α (parX α (P1' α) (P2' α)))) ∈ synch' (bout ch , P1') (binp ch , P2') ⟩
          lem with decName ch ch 
          lem | no ¬p = ¬p refl
          lem | yes _ = ∣ refl ∣₁

      synch'-out' : ∀ {n} {P1 P2 aQ : Step (\ n → ▹ X n) n}
        → ⟨ aQ ∈ synch' P1 P2 ⟩ → ∥ synch'∈ P1 P2 aQ ∥₁
      synch'-out' {P1 = a , P1} {b , P2} m with canSynchL? a b
      synch'-out' {P1 = _ , P1} m | local r r' =
        PT.map (synch'-s _ _ (λ i → out (r i) (r' i) , P1) refl) m
      synch'-out' {P1 = _ , P1} m | bound r =
        PT.map (synch'-f _ _ (λ i → bout (r i) , P1) refl) m

  data synchF∈  {n} (P Q : F' n (λ _ → X)) aR : Set where
    con : ∀ {P'} {Q'} → ⟨ P' ∈ P ⟩ → ⟨ Q' ∈ Q ⟩ → ⟨ aR ∈ synch P' Q' ⟩ → synchF∈ P Q aR

  abstract
    synchF-out' : ∀ {n} P Q {aR} → ⟨ aR ∈ synchF {n} P Q ⟩ → ∥ synchF∈ P Q aR ∥₁
    synchF-out' P Q {aR} m =
      PT.rec squash₁
             (λ { (P' , P'∈ , aR∈) →
               PT.rec squash₁
                      (λ { (Q' , Q'∈ , aR∈) →  ∣ con P'∈ Q'∈ aR∈ ∣₁})
                      (bind-out (synch P') _ Q aR∈) })
             (bind-out (\ P' → bind Q (synch P')) _ P m)

    synchF-in' : ∀ {n} P Q {aR} → synchF∈ P Q aR → ⟨ aR ∈ synchF {n} P Q ⟩
    synchF-in' P Q (con {P'} P'∈ Q'∈ aR∈) =
      bind-in (λ P' → bind Q (synch P')) _ P (_ , P'∈ , bind-in (synch P') _ Q (_ , Q'∈ , aR∈))

    synch-out : ∀ {n} P Q {aR} → ⟨ aR ∈ synchF {n} P Q ⟩ → ∥ Σ _ (\ P' → Σ _ \ Q' → ⟨ P' ∈ P ⟩ × ⟨ Q' ∈ Q ⟩ × ⟨ aR ∈ synch P' Q' ⟩) ∥₁
    synch-out P Q {aR} m =
      PT.rec squash₁
             (λ { (P' , P'∈ , aR∈ ) →
               PT.rec squash₁
                      (λ { (Q' , Q'∈ , aR∈) → ∣ _ , _ , P'∈ , Q'∈ , aR∈ ∣₁ })
                      (bind-out (synch P') _ Q aR∈) })
             (bind-out (\ P' → bind Q (synch P')) _ P m) 

    synch-in : ∀ {n} P Q {aR} → (Σ _ (\ P' → Σ _ \ Q' → ⟨ P' ∈ P ⟩ × ⟨ Q' ∈ Q ⟩ × ⟨ aR ∈ synch P' Q' ⟩)) → ⟨ aR ∈ synchF {n} P Q ⟩
    synch-in P Q (P' , Q' ,  P'∈ , Q'∈ , aR∈) =
      bind-in (λ P' → bind Q (synch P')) _ P (_ , P'∈ , bind-in (synch P') _ Q (_ , Q'∈ , aR∈))

-- Another characterization of the type ⟨ (a , Q) ∈ synch' P1 P2 ⟩,
-- but now for the case where synch' is defined directly for Pi, not
-- a generic algebra X (as in the module StepLemmataPi in
-- pi-calculus.semantics.Algebra)
module StepLemmata2Pi where

  open StepLemmataPi

  module _ (parX : ∀ {n} → Pi n → Pi n → Pi n) (νX : ∀ {n} → Pi (suc n) → Pi n) where
    open Synch' parX νX

    synch'-in-s : ∀ {n} {m1 m2} {a1 : Label n m1}{a2 : Label n m2} {P1 P2} {aQ} →
      ∥ (Σ (Pi n) \ P1' → Σ (Pi n) \ P2' → Σ (Name n) \ ch → Σ _ \ z → ((a1 , P1) ≡ `out ch z P1') ×
                 ((_,_ {X = \ n → Pi n} a2 P2) ≡ (inp ch z , P2')) ×
                   (aQ ≡ (`τ (parX P1' P2')))) ∥₁
      → ⟨ aQ ∈ synch' (a1 , P1) (a2 , P2) ⟩
    synch'-in-s {n}{m1}{m2}{a1}{a2}{P1}{P2}{aQ} = PT.rec (snd (aQ ∈ synch' (a1 , P1) (a2 , P2)))
      λ { (P1' , P2' , ch , z , eq1 , eq2 , eqn) →
        J (λ aP1' _ → ⟨ aQ ∈ synch' aP1' (a2 , P2) ⟩)
          (J (λ aP2' _ → ⟨ aQ ∈ synch' (`out ch z P1') aP2' ⟩)
            (subst (λ x → ⟨ x ∈ synch' (`out ch z P1') (`inp ch z P2') ⟩) (sym eqn) lem)
            (sym eq2))
          (sym eq1) }
      where
        lem : ∀{P1' P2' ch z} → ⟨ `τ (parX P1' P2') ∈ synch' (`out ch z P1') (`inp ch z P2') ⟩
        lem {ch = ch} with decName ch ch
        lem {z = z} | yes _ with decName z z
        lem         | yes _ | yes _ = ∣ refl ∣₁
        lem         | yes _ | no r = r refl
        lem         | no r  = r refl
        
    synch'-in-f : ∀ {n} {m1 m2} {a1 : Label n m1}{a2 : Label n m2} {P1 : Pi m1} {P2} {aQ} →
      ∥ (Σ (Pi (suc n)) \ P1' → Σ (Pi (suc n)) \ P2' → Σ (Name n) \ ch → ((_,_ {X = \ n → Pi n} a1 P1) ≡ `bout ch P1') ×
                  ((_,_ {X = \ n → Pi n} a2 P2) ≡ (binp ch , P2')) ×
                    ((aQ) ≡ (`τ (νX (parX P1' P2') )))) ∥₁
      → ⟨ aQ ∈ synch' (a1 , P1) (a2 , P2) ⟩
    synch'-in-f {n}{m1}{m2}{a1}{a2}{P1}{P2}{aQ} = PT.rec (snd (aQ ∈ synch' (a1 , P1) (a2 , P2)))
      λ { (P1' , P2' , ch , eq1 , eq2 , eqn) →
         J (λ aP1' _ → ⟨ aQ ∈ synch' aP1' (a2 , P2) ⟩)
           (J (λ aP2' _ → ⟨ aQ ∈ synch' (`bout ch P1') aP2' ⟩)
             (subst (λ x → ⟨ x ∈ synch' (`bout ch P1') (`binp ch P2') ⟩) (sym eqn) lem)
             (sym eq2))
           (sym eq1) }
      where
        lem : ∀{P1' P2' ch} → ⟨ `τ (νX (parX P1' P2')) ∈ synch' (`bout ch P1') (`binp ch P2') ⟩
        lem {ch = ch}  with decName ch ch
        ... | yes _ = ∣ refl ∣₁
        ... | no r = r refl

    data synch'∈ {n} (P1 P2 aQ : Step Pi n) : Set where
        synch'-s : ∀ (P1' P2' : Pi n) {ch z}
          → P1 ≡ `out ch z P1' → P2 ≡ `inp ch z P2'
          → aQ ≡ `τ (parX P1' P2')
          → synch'∈ P1 P2 aQ
        synch'-f : ∀ (P1' P2' : Pi (suc n)) {ch}
          → P1 ≡ `bout ch P1' → P2 ≡ `binp ch P2'
          → aQ ≡ `τ (νX (parX P1' P2'))
          → synch'∈ P1 P2 aQ

    abstract
      synch'-out' : ∀ {n} {P1 P2 aQ : Step Pi n}
        → ⟨ aQ ∈ synch' P1 P2 ⟩ → ∥ synch'∈ P1 P2 aQ ∥₁
      synch'-out' {P1 = a , P1} {b , P2} m with canSynchL? a b
      synch'-out' {P1 = _ , P1} m | local r r' =
        PT.map (synch'-s _ _ (λ i → out (r i) (r' i) , P1) refl) m
      synch'-out' {P1 = _ , P1} m | bound r =
        PT.map (synch'-f _ _ (λ i → bout (r i) , P1) refl) m

  data synchF∈  {n} (P Q : F n Pi) aR : Set where
    con : ∀ {P'} {Q'} → ⟨ P' ∈ P ⟩ → ⟨ Q' ∈ Q ⟩ → ⟨ aR ∈ synch P' Q' ⟩ → synchF∈ P Q aR

  abstract
    synchF-out' : ∀ {n} P Q {aR} → ⟨ aR ∈ synchF {n} P Q ⟩ → ∥ synchF∈ P Q aR ∥₁
    synchF-out' P Q {aR} m =
      PT.rec squash₁
             (λ { (P' , P'∈ , aR∈) →
               PT.rec squash₁
                      (λ { (Q' , Q'∈ , aR∈) →  ∣ con P'∈ Q'∈ aR∈ ∣₁})
                      (bind-out (synch P') _ Q aR∈) })
             (bind-out (\ P' → bind Q (synch P')) _ P m)


open StepLemmata Proc (\ α n → ProcPi-alg n) (mapProc _ _)
open StepLemmata2 Proc (\ α n → ProcPi-alg n) (mapProc _ _)

-- An equivalent characterization of (a , R) ← parProc P Q, i.e. the
-- transitions out of a parallel composition in Proc.
data par∈ {n} (P Q : Proc n) (aR : Step (\ n → ▹ Proc n) n) : Set where
  parL : ∀ P' (let a = theLabel aR) → (a , P') ← P → (theX aR ≡ \ α → parProc (P' α) (mapProc _ _ (labelInj a .fst) Q)) → par∈ P Q aR
  parR : ∀ Q' (let a = theLabel aR) → (a , Q') ← Q → (theX aR ≡ \ α → parProc (mapProc _ _ (labelInj a .fst) P) (Q' α)) → par∈ P Q aR
  parS : ∀ P' Q' → P' ← P → Q' ← Q →  ⟨ aR ∈ synch P' Q' ⟩ → par∈ P Q aR

par-out : ∀ {n} {P Q : Proc n} {R} → R ← (parProc P Q) → ∥ par∈ P Q R ∥₁
par-out {n}{P}{Q}{R'@(a , R)} m = ∪-out {P = L1}{R1} (subst (_←_ (a , R)) (cong (λ alg₁ → isPi-alg.parX (alg₁ n) P Q) (fix-eq ProcPi-algF)) m) >>PT 
  λ { (_⊎_.inl x) → ∪-out {P = L2}{R2} x >>PT
    λ { (_⊎_.inl mL) → PT.map
      (λ { ((a' , P') , mP' , eq) → J (λ aR _ → par∈ P Q aR) (parL P' mP' refl) (sym eq) })
      (mapP∞-out _ (a , R) (Unfold P) mL)
      ; (_⊎_.inr mR) →  PT.map
      (λ { ((a' , Q') , mQ' , eq) → J (λ aR _ → par∈ P Q aR) (parR Q' mQ' refl) (sym eq) })
      (mapP∞-out _ (a , R) (Unfold Q) mR) }
    ; (_⊎_.inr mS) → PT.map
      (λ { (con m1 m2 m) → parS _ _ m1 m2 m })
      (synchF-out' (Unfold P) (Unfold Q) mS) }
  where
    L2 = stepL (Unfold P) Q
    R2 = stepR P (Unfold Q)
    L1 = L2 ∪ R2
    R1 = bind (Unfold P) (λ sp → bind (Unfold Q) (λ sq → synch sp sq))

par-in : ∀ {n} {P Q : Proc n} {R} → par∈ P Q R → R ← (parProc P Q)
par-in {n}{P}{Q}{a , R} (parL P' mP' r) =
  J (λ x eq → (a , x) ← parProc P Q)
    (subst (_←_ (a , (λ α → parProc (P' α) _)))
           (sym (cong (λ alg → isPi-alg.parX (alg n) P Q) (fix-eq ProcPi-algF)))
           (∪-in-L {P = stepL (Unfold P) Q ∪ stepR P (Unfold Q)}
                   {bind (Unfold P) (λ sp → bind (Unfold Q) (λ sq → synch sp sq))}
                   (∪-in-L {P = stepL (Unfold P) Q}
                           {stepR P (Unfold Q)}
                           (mapP∞-in _ (a , P') (Unfold P) mP'))))
    (sym r)
par-in {n}{P}{Q}{a , R} (parR Q' mQ' r) = 
  J (λ x eq → (a , x) ← parProc P Q)
    (subst (_←_ (a , (λ α → parProc _ (Q' α))))
           (sym (cong (λ alg → isPi-alg.parX (alg n) P Q) (fix-eq ProcPi-algF)))
           (∪-in-L {P = stepL (Unfold P) Q ∪ stepR P (Unfold Q)}
                   {bind (Unfold P) (λ sp → bind (Unfold Q) (λ sq → synch sp sq))}
                   (∪-in-R {P = stepL (Unfold P) Q}
                           {stepR P (Unfold Q)}
                           (mapP∞-in _ (a , Q') (Unfold Q) mQ'))))
    (sym r)
par-in {n}{P}{Q}{a , R} (parS P' Q' mP' mQ' mS) = 
  subst (_←_ (a , R))
        (sym (cong (λ alg → isPi-alg.parX (alg n) P Q) (fix-eq ProcPi-algF)))
        (∪-in-R {P = stepL (Unfold P) Q ∪ stepR P (Unfold Q)}
                {bind (Unfold P) (λ sp → bind (Unfold Q) (λ sq → synch sp sq))}
                (synchF-in' (Unfold P) (Unfold Q) (con mP' mQ' mS)))

-- An equivalent characterization of (a , Q) ← νProc P, i.e. the
-- transitions out of restriction in Proc.
data isLabelι {m} : ∀ {n} → (a : Label (suc m) (suc n)) (b : Label m n) → Set where
  inp : ∀ ch z → isLabelι (inp (ι ch) (ι z)) (inp ch z)
  out : ∀ ch z → isLabelι (out (ι ch) (ι z)) (out ch z)
  bout : ∀ ch → isLabelι (bout (ι ch)) (bout ch)
  binp : ∀ ch → isLabelι (binp (ι ch)) (binp ch)
  τ : isLabelι τ τ


swapProc : ∀ {m n} → (a : Label (suc m) (suc n)) → Proc (suc n) → Proc (suc n)
swapProc (bout x) P = mapProc _ _ swap P
swapProc (binp x) P = mapProc _ _ swap P
swapProc (out x x₁) P = P
swapProc (inp x x₁) P = P
swapProc τ P = P

data ν∈ {m}(P : Proc (suc m)) (aR : Step (\ n → ▹ Proc n) m) : Set where
  pr : ∀{n} (a' : Label _ (suc n)) (R' : _) (prf : Σ (Label _ _) \ a → isLabelι a' a)
    → (a' , R') ← P → m ≡ n → aR ≡ (prf .fst , \ α → νProc (R' α))
    → ν∈ P aR
  pr2 : ∀ {n} (a' : Label _ (suc n)) (R' : _) (prf : Σ (Label _ _) \ a → isLabelι a' a)
    → (a' , R') ← P → suc m ≡ n → aR ≡ (prf .fst , \ α → νProc (swapProc a' (R' α)))
    → ν∈ P aR
  bound : ∀ {ch : Name m} R'
    → (out (ι ch) (fresh _) , R') ← P → aR ≡ `bout ch R'
    → ν∈ P aR

stepν-out-fresh : ∀ {m}{ch : Name m}{R : ▹ Proc (suc m)}
  → stepν (`out (ι ch) (fresh m) R) ≡ η (`bout ch R)
stepν-out-fresh {m} {ch} {R} with decName (ι ch) (fresh _) | decName (fresh m) (fresh m)
... | yes p | _ = ⊥-rec (fresh-ι p)
... | no _  | no ¬r = ⊥-rec (¬r refl)
... | no ¬p | yes r = cong η (StepPath refl (cong′ bout (down-ι ¬p)) refl)

ν-in-pr : ∀{m n}{a' : Label _ (suc n)}
    (prf : Σ (Label m _) (isLabelι a'))
    (R' : (x : Tick) → Proc (suc n)) →
    (eq : m ≡ n) → 
    ⟨ (prf .fst , (λ α → νProc (R' α))) ∈ stepν (a' , R') ⟩
ν-in-pr (._ , inp ch a) R' eq with decName (ι ch) (fresh _) | decName (ι a) (fresh _)
... | yes p | _ = ⊥-rec (fresh-ι p)
... | no ¬p | yes q = ⊥-rec (fresh-ι q)
... | no ¬p | no ¬q = ∣ StepPath refl (λ i → inp (sym (down-ι ¬p) i) (sym (down-ι ¬q) i)) refl ∣₁  
ν-in-pr (._ , out ch a) R' eq with decName (ι ch) (fresh _) | decName (ι a) (fresh _)
... | yes p | _ = ⊥-rec (fresh-ι p)
... | no ¬p | yes q = ⊥-rec (fresh-ι q)
... | no ¬p | no ¬q = ∣ StepPath refl (λ i → out (sym (down-ι ¬p) i) (sym (down-ι ¬q) i)) refl ∣₁ 
ν-in-pr (._ , binp ch) R' eq = ⊥-rec (¬≡suc _ eq)
ν-in-pr (._ , bout ch) R' eq = ⊥-rec (¬≡suc _ eq)
ν-in-pr (._ , τ) R' eq = ∣ refl ∣₁

ν-in-pr2 : ∀ {m} {n} {a' : Label (suc m) (suc n)}
   (R' : (x : Tick) → Proc (suc n))
   (prf : Σ (Label m _) (isLabelι a')) (eq : suc m ≡ n) →
   ⟨ (prf .fst , (λ α → isPi-alg.νX (fix ProcPi-algF n) (swapProc a' (R' α)))) ∈ stepν (a' , R') ⟩
ν-in-pr2 R' (_ , bout ch) eq with decName (ι ch) (fresh _)
... | yes p = ⊥-rec (fresh-ι p)
... | no ¬p = ∣ StepPath refl (λ i → bout (sym (down-ι ¬p) i)) refl ∣₁
ν-in-pr2 R' (_ , binp ch) eq with decName (ι ch) (fresh _)
... | yes p = ⊥-rec (fresh-ι p)
... | no ¬p = ∣ StepPath refl (λ i → binp (sym (down-ι ¬p) i)) refl ∣₁
ν-in-pr2 R' (_ , inp ch z) eq = ⊥-rec (¬≡suc _ (sym eq))
ν-in-pr2 R' (_ , out ch z) eq = ⊥-rec (¬≡suc _ (sym eq))
ν-in-pr2 R' (_ , τ) eq = ⊥-rec (¬≡suc _ (sym eq))

ν-in : ∀ {m} (P : Proc (suc m)) aR  → ν∈ P aR → aR ← νProc P
ν-in P aR (pr a' R' prf x q p) =
  J (λ x eq → x ← νProc P)
    (subst ((prf .fst , (λ α → νProc (R' α))) ←_)
           (sym (λ i → isPi-alg.νX (fix-eq ProcPi-algF i _) P))
           (bind-in stepν (prf .fst , (λ α → νProc (R' α))) (Unfold P) (_ , x , ν-in-pr prf R' q)))
    (sym p)
ν-in P aR (pr2 a' R' prf x q p) =
  J (λ x eq → x ← νProc P)
    (subst ((prf .fst , (λ α → νProc (swapProc a' (R' α)))) ←_)
           (sym (λ i → isPi-alg.νX (fix-eq ProcPi-algF i _) P))
           (bind-in _ _ (Unfold P) (_ , (x , ν-in-pr2 R' prf q))))
    (sym p)
ν-in P aR (bound R' x p) =
    J (λ x eq → x ← νProc P)
      (subst ((bout _ , R') ←_)
             (sym (λ i → isPi-alg.νX (fix-eq ProcPi-algF i _) P))
             (bind-in _ _ (Unfold P)
                      (_ , (x , subst (λ s → ⟨ `bout _ R' ∈ s ⟩) (sym stepν-out-fresh) ∣ refl ∣₁))))
      (sym p)



-- Using these equivalent characterizations of reductions from parProc
-- and νProc, the relation (λ P a P' → (a , next P') ← P) is easily
-- shown to model all the rules of the CCS-operational semantics.
outProc : {n : ℕ} {P : Proc n} (ch v : Name n) →
  `out ch v (next P) ← actProc (out ch v) P
outProc ch v = ∣ refl ∣₁

binpProc : {n : ℕ} {P : Proc (suc n)} (ch : Name n) →
  `binp ch (next P) ← actProc (inp ch) P
binpProc ch = ∣ _⊎_.inr (0 , ∣ refl ∣₁) ∣₁

τProc : {n : ℕ} {P : Proc n} → `τ (next P) ← actProc τ P
τProc = ∣ refl ∣₁

inpProc : {n : ℕ} {P : Proc (suc n)} (ch v : Name n) →
  `inp ch v (next (mapProc _ _ (for-fresh v) P)) ← actProc (inp ch) P
inpProc {n}{P} ch v =
  subst (λ x →
          `inp ch v (next (mapProc _ _ (for-fresh v) P))
           ←
           Fold (bind x (\ v → η ((`inp ch v \ α →  mapProc _ _ (for-fresh v) P)))
                ∪ (η (`binp ch \ α → P))))
        (sym (enum-eq (η v)))
        ∣ _⊎_.inl ∣ _⊎_.inl ∣ refl ∣₁ ∣₁ ∣₁ 

sumtrProc : {n m : ℕ} {P Q : Proc n} {P' : Proc m} {a : Label n m} →
  (a , next P') ← P →
  (a , next P') ← sumProc P Q
sumtrProc {P = P}{Q} mP' = ∪-in-L {P = Unfold P} {Unfold Q} mP'

partrProc : {n m : ℕ} {P Q : Proc n} {P' : Proc m} {a : Label n m} →
  (a , next P') ← P →
  (a , next (parProc P' (mapProc n m (labelInj a .fst) Q))) ← parProc P Q
partrProc {P = P} {Q} mP' = par-in {P = P}{Q} (parL _ mP' refl)

comProc : {n : ℕ} {P Q P' Q' : Proc n} {ch a : Name n} →
  (out ch a ,  next P') ← P → (inp ch a , next Q') ← Q →
  (τ , next (parProc P' Q')) ← parProc P Q
comProc {P = P}{Q}{P'}{Q'}{ch}{a} mP' mQ' =
  par-in {P = P} {Q}
    (parS _ _ mP' mQ'
      (∪-in-L {P = Synch'.synch' parX' νX' (out ch a , next P') (inp ch a , next Q')}
              {ø}
              (synch'-in-s _ _ ∣ _ , _ , _ , _ , refl , refl , refl ∣₁)))

closeProc : {n : ℕ} {P Q : Proc n} {P' Q' : Proc (suc n)} {ch : Name n} →
  `bout ch (next P') ← P → `binp ch (next Q') ← Q →
  `τ (next (νProc (parProc P' Q'))) ← parProc P Q
closeProc {P = P}{Q}{P'}{Q'}{ch} mP' mQ' =
  par-in {P = P}{Q}
    (parS _ _ mP' mQ'
      (∪-in-L {P = Synch'.synch' parX' νX' (bout ch , next P') (binp ch , next Q')}
              {ø}
              (synch'-in-f _ _ ∣ _ , _ , _ , refl , refl , refl ∣₁)))

resProc : {n m : ℕ} {P : Proc (suc n)} {P' : Proc (suc m)} {a : Label n m} →
    (mapLabelι a , next P') ← P →
    (a , next (νProc (swap?X ProcPi-alg (mapProc _ _) a P'))) ← νProc P
resProc {P = P}{a = out ch a} mP' = ν-in P _ (pr _ _ (_ , out ch a) mP' refl refl)
resProc {P = P}{a = bout ch} mP' = ν-in P _ (pr2 _ _ (_ , bout ch) mP' refl refl)
resProc {P = P}{a = inp ch a} mP' = ν-in P _ (pr _ _ (_ , inp ch a) mP' refl refl)
resProc {P = P}{a = binp ch} mP' = ν-in P _ (pr2 _ _ (_ , binp ch) mP' refl refl)
resProc {P = P}{a = τ} mP' = ν-in P _ (pr _ _ (_ , τ) mP' refl refl)

opnProc : {n : ℕ} {P P' : Proc (suc n)} {ch : Name n} →
    `out (ι ch) (fresh n) (next P') ← P →
    `bout ch (next P') ← νProc P
opnProc {P = P}  mP' = ν-in P _ (bound _ mP' refl) 

ProcDynamics : Dynamics ProcPi-alg (mapProc _ _) _≡_ (λ P a P' → (a , next P') ← P)
ProcDynamics = record
               { outX = outProc
               ; inpX = inpProc
               ; binpX = binpProc
               ; τX = τProc
               ; sumtrX = λ {n}{m}{P}{Q} → sumtrProc {n}{m}{P}{Q}
               ; partrX = λ {n}{P}{Q} → partrProc {n}{P}{Q}
               ; comX = λ {n}{P}{Q} → comProc {n}{P}{Q}
               ; resX = λ {n}{m}{P} → resProc {n}{m}{P}
               ; opnX = λ {n}{P} → opnProc {n}{P}
               ; closeX = λ {n}{P} → closeProc {n}{P}
               ; convX = λ tr eq eq' →
                       transport (cong₂ (\ P P' → (_ , next P') ← P) eq eq') tr
               }

-- open import pi-calculus.semantics.StructuralCongruence ns
-- 
-- ProcPi-premodel : isPi-premodel Proc
-- ProcPi-premodel = record
--   { algX = ProcPi-alg
--   ; mapX = mapProc _ _
--   ; EqX = _≡_
--   ; congX = ProcStructCong 
--   ; TransX = λ P a P' → (a , next P') ← P
--   ; dynX = ProcDynamics
--   ; mapX-id = mapProc-id _
--   ; mapX-∘ = λ {_}{_}{_}{f}{g} P → {!!}
--   }


-- -- Check?
-- 
-- module Check where
-- 
--   P : Pi 2
--   P = inp (fresh 1) · end
-- 
--   f : Name 2 -> Name 2
--   f _ = fresh 1
-- 
--   check' : mapProc' _ _ f (Unfold (evalX ProcPi-alg P)) ⊂ Unfold (evalX ProcPi-alg (mapPi f P)) → ⊥
--   check' p =
--     PT.rec isProp⊥
--            (λ { (_⊎_.inl m) → PT.rec isProp⊥
--                                       (λ { (v , v∈ , eq') → PT.rec isProp⊥
--                                                                     (λ eq → {!eq'!})
--                                                                     eq' })
--                                       (bind-out _ x enum m)
--               ; (_⊎_.inr m) → {!!} })
--            (p x x∈)
--     where
--       x : Step (λ m → (x₁ : Tick) → Proc m) 2
--       theM x = _
--       theLabel x = inp (fresh 1) (ι (fresh 0))
--       theX x _ = Fold ø
-- 
--       x∈ : ⟨ x ∈ mapProc' _ _ f (Unfold (evalX ProcPi-alg P)) ⟩
--       x∈ = subst (λ s → ⟨ x ∈ s ⟩)
--                  (sym (mapProc'-eq' _ _ f (Unfold (evalX ProcPi-alg P))))
--                  ∣ _⊎_.inr (0 , ∣ _⊎_.inr (0 , 
--                      subst (λ s → ⟨ x ∈ s ⟩)
--                            (sym (inps'-eq (next mapProc') f (fresh 1) (λ _ → Fold ø)))
--                            (bind-in _ x (neg (image f) (image-fn f))
--                              (ι (fresh 0) , neg-in _ _ _ (λ q → PT.rec isProp⊥ (λ { (v , v∈ , eq) → fresh-ι eq }) (mapP∞-out f (ι (fresh 0)) enum q)) ,
--                                ∣ (λ i → (inp (fresh 1) (ι (fresh 0)) , (λ α → Fold (mapProc'-eq' 3 2 (snoc (λ _ → fresh 1) (ι (fresh 0))) ø (~ i))))) ∣₁)))
--                          ∣₁) ∣₁
-- 
--       x∈' : ⟨ x ∈ Unfold (evalX ProcPi-alg (mapPi f P)) ⟩
--       x∈' = ∣ _⊎_.inl (bind-in _ x enum (ι (fresh 0) , {!!} , ∣ {!!} ∣₁)) ∣₁
-- 
--   check? : evalX ProcPi-alg (mapPi f P) ≡ mapProc _ _ f (evalX ProcPi-alg P)
--   check? = {!!}
