{-# OPTIONS --cubical --guarded #-}

open import Cubical.Data.Sum hiding (inl; inr) 
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (lift)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary
open import CountablePowerSet
open import Basic
open import AbsNames
open import LaterPrims hiding (_∙_)

module ccs.semantics.Dynamics (ns : Names) where

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

-- Here we show that the relation (λ P a P' → (a , next P') ← P) models
-- the operational semantics of CCS.

-- An equivalent characterization of the type ⟨ (a , Q) ∈ synch' P1 P2 ⟩,
-- when synch' is defined for a generic CCS-algebra X (as in the
-- module StepLemmata in ccs.semantics.Algebra): this can only happen
-- if (a ≡ τ), (P1 ≡ out a' , P1'), (P2 ≡ inp a' , P2') and (Q α =
-- parX α (P1' α) (P2' α)) (so when P1 and P2 can communicate)
module StepLemmata2
  (X : ℕ → Type)
  (X-alg : ▹ (∀ n → isCCS-alg X n))
  (mapX : ∀ {n m} → (Name m → Name n) → X m → X n)
  where

  open StepLemmata X X-alg mapX

  module _ (parX : ▹ (∀ {n} → X n → X n → X n)) where
    open Synch' parX

    synch'-in-s : ∀ {n} {a1 : Act n}{a2 : Act n} {P1 P2 : ▹ X n} {aQ} →
      ∥ (Σ (▹ X n) \ P1' → Σ (▹ X n) \ P2' → Σ (Name n) \ a' → ((a1 , P1) ≡ (out a' , P1')) ×
                   ((_,_ {X = \ n → ▹ X n} a2 P2) ≡ (inp a' , P2')) ×
                     ((aQ) ≡ (τ , (\ α → parX α (P1' α) ((P2' α)) )))) ∥₁ → ⟨ (aQ) ∈ synch' (a1 , P1) (a2 , P2) ⟩
    synch'-in-s {n}{a1}{a2}{P1}{P2}{aQ} = PT.rec (snd (aQ ∈ synch' (a1 , P1) (a2 , P2)))
      λ { (P1' , P2' , a' , eq1 , eq2 , eqn) →
        J (λ aP1' _ → ⟨ aQ ∈ synch' aP1' (a2 , P2) ⟩)
          (J (λ aP2' _ → ⟨ aQ ∈ synch' (out a' , P1') aP2' ⟩)
             (subst (λ x → ⟨ x ∈ synch' (out a' , P1') (inp a' , P2') ⟩) (sym eqn) lem)
             (sym eq2))
          (sym eq1) }
      where
        lem : ∀{P1' P2' a} → ⟨ (τ  , (λ α → parX α (P1' α) (P2' α))) ∈ synch' (out a , P1') (inp a , P2') ⟩
        lem {a = a} with decName a a
        ... | yes _ = ∣ refl ∣₁
        ... | no r = r refl

    data synch'∈ {n} (P1 P2 aQ : Step (\ n → ▹ X n) n) : Set where
      synch'-s : ∀ (P1' P2' : ▹ X n) {a}
        → P1 ≡ `out a P1' → P2 ≡ `inp a P2'
        → aQ ≡ `τ (\ α → parX α (P1' α) (P2' α))
        → synch'∈ P1 P2 aQ

    abstract
      synch'-in' : ∀ {n} {P1 P2 aQ : Step (\ n → ▹ X n) n} → synch'∈ P1 P2 aQ → ⟨ aQ ∈ synch' P1 P2 ⟩
      synch'-in' {P1 = P1}{P2} (synch'-s P1' P2' {a} p q r) =
        subst (λ x → ⟨ x ∈ synch' P1 P2 ⟩) (sym r) (subst2 (λ x y → ⟨ _ ∈ synch' x y ⟩) (sym p) (sym q) lem)
        where
          lem : ⟨ (τ , (λ α → parX α (P1' α) (P2' α))) ∈ synch' (out a , P1') (inp a , P2') ⟩
          lem with decName a a
          lem | yes _ = ∣ refl ∣₁
          lem | no ¬p = ¬p refl

      synch'-out' : ∀ {n} {P1 P2 aQ : Step (\ n → ▹ X n) n} → ⟨ aQ ∈ synch' P1 P2 ⟩ → ∥ synch'∈ P1 P2 aQ ∥₁
      synch'-out' {P1 = a , P1} {b , P2} m with canSynchL? a b
      synch'-out' m | local r = PT.map (λ eq → synch'-s _ _ refl (cong (λ z → inp z , _) (sym r)) eq) m

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
-- but now for the case where synch' is defined directly for CCS, not
-- a generic algebra X (as in the module StepLemmataCCS in
-- ccs.semantics.Algebra)
module StepLemmata2CCS where

  open StepLemmataCCS

  module _ (parX : ∀ {n} → (CCS n → CCS n → CCS n)) where
    open Synch' parX public

    synch'-in-s : ∀ {n} {a1 : Act n}{a2 : Act n} {P1 P2 : CCS n} {aQ} →
        ∥ (Σ (CCS n) \ P1' → Σ (CCS n) \ P2' → Σ (Name n) \ a' → ((a1 , P1) ≡ `out a' P1') ×
                     ((_,_ {X = CCS} a2 P2) ≡ `inp a' P2') ×
                       (aQ ≡ (`τ (parX P1' P2')))) ∥₁ → ⟨ aQ ∈ synch' (a1 , P1) (a2 , P2) ⟩
    synch'-in-s {n}{a1}{a2}{P1}{P2}{aQ} = PT.rec (snd (aQ ∈ synch' (a1 , P1) (a2 , P2)))
        λ { (P1' , P2' , a' , eq1 , eq2 , eqn) →
          J (λ aP1' _ → ⟨ aQ ∈ synch' aP1' (a2 , P2) ⟩)
            (J (λ aP2' _ → ⟨ aQ ∈ synch' (out a' , P1') aP2' ⟩)
               (subst (λ x → ⟨ x ∈ synch' (out a' , P1') (inp a' , P2') ⟩) (sym eqn) lem)
               (sym eq2))
            (sym eq1) }
        where
          lem : ∀{P1' P2' a} → ⟨ `τ  (parX P1' P2') ∈ synch' (`out a P1') (`inp a P2') ⟩
          lem {a = a} with decName a a
          ... | yes _ = ∣ refl ∣₁
          ... | no r = r refl

    data synch'∈ {n} (P1 P2 aQ : Step CCS n) : Set where
      synch'-s : ∀ (P1' P2' : CCS n) {a}
        → P1 ≡ `out a P1' → P2 ≡ `inp a P2' → aQ ≡ (`τ (parX P1' P2'))
        → synch'∈ P1 P2 aQ

    abstract
      synch'-out' : ∀ {n} {P1 P2 aQ : Step CCS n} → ⟨ aQ ∈ synch' P1 P2 ⟩ → ∥ synch'∈ P1 P2 aQ ∥₁
      synch'-out' {P1 = a , P1} {b , P2} m with canSynchL? a b
      synch'-out' {P2 = _ , P2} m | local r = PT.map (λ eq → synch'-s _ _ refl (λ i → inp (r (~ i)) , P2) eq) m

  data synchF∈  {n} (P Q : F n CCS) aR : Set where
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

open StepLemmata Proc (\ α n → ProcCCS-alg n) (mapProc _ _)
open StepLemmata2 Proc (\ α n → ProcCCS-alg n) (mapProc _ _)

-- An equivalent characterization of (a , R) ← parProc P Q, i.e. the
-- transitions out of a parallel composition in Proc.
data par∈ {n} (P Q : Proc n) (aR : Step (\ n → ▹ Proc n) n) : Set where
  parL : ∀ P' (let a = theLabel aR) → (a , P') ← P → (theX aR ≡ \ α → parProc (P' α) Q) → par∈ P Q aR
  parR : ∀ Q' (let a = theLabel aR) → (a , Q') ← Q → (theX aR ≡ \ α → parProc P (Q' α)) → par∈ P Q aR
  parS : ∀ P' Q' → P' ← P → Q' ← Q →  ⟨ aR ∈ synch P' Q' ⟩ → par∈ P Q aR

par-out : ∀ {n} {P Q : Proc n} {R} → R ← (parProc P Q) → ∥ par∈ P Q R ∥₁
par-out {n}{P}{Q}{R'@(a , R)} m = ∪-out {P = L1}{R1} (subst (_←_ (a , R)) (cong (λ alg₁ → isCCS-alg.parX (alg₁ n) P Q) (fix-eq ProcCCS-algF)) m) >>PT 
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
    (subst (_←_ (a , (λ α → parProc (P' α) Q)))
           (sym (cong (λ alg → isCCS-alg.parX (alg n) P Q) (fix-eq ProcCCS-algF)))
           (∪-in-L {P = stepL (Unfold P) Q ∪ stepR P (Unfold Q)}
                   {bind (Unfold P) (λ sp → bind (Unfold Q) (λ sq → synch sp sq))}
                   (∪-in-L {P = stepL (Unfold P) Q}
                           {stepR P (Unfold Q)}
                           (mapP∞-in _ (a , P') (Unfold P) mP'))))
    (sym r)
par-in {n}{P}{Q}{a , R} (parR Q' mQ' r) = 
  J (λ x eq → (a , x) ← parProc P Q)
    (subst (_←_ (a , (λ α → parProc P (Q' α))))
           (sym (cong (λ alg → isCCS-alg.parX (alg n) P Q) (fix-eq ProcCCS-algF)))
           (∪-in-L {P = stepL (Unfold P) Q ∪ stepR P (Unfold Q)}
                   {bind (Unfold P) (λ sp → bind (Unfold Q) (λ sq → synch sp sq))}
                   (∪-in-R {P = stepL (Unfold P) Q}
                           {stepR P (Unfold Q)}
                           (mapP∞-in _ (a , Q') (Unfold Q) mQ'))))
    (sym r)
par-in {n}{P}{Q}{a , R} (parS P' Q' mP' mQ' mS) = 
  subst (_←_ (a , R))
        (sym (cong (λ alg → isCCS-alg.parX (alg n) P Q) (fix-eq ProcCCS-algF)))
        (∪-in-R {P = stepL (Unfold P) Q ∪ stepR P (Unfold Q)}
                {bind (Unfold P) (λ sp → bind (Unfold Q) (λ sq → synch sp sq))}
                (synchF-in' (Unfold P) (Unfold Q) (con mP' mQ' mS)))

-- An equivalent characterization of (a , Q) ← νProc P, i.e. the
-- transitions out of restriction in Proc.
data isActι {n} : (a : Act (suc n)) (b : Act n) → Set where
 inp : ∀ a → isActι (inp (ι a)) (inp a)
 out : ∀ a → isActι (out (ι a)) (out a)
 τ : isActι τ τ

data ν∈ {m}(P : Proc (suc m)) (aR : Step (\ n → ▹ Proc n) m) : Set where
  pr : ∀ (a' : Act (suc m)) (R' : _) (prf : Σ (Act _) \ a → isActι a' a) → (a' , R') ← P → aR ≡ (prf .fst , \ α → νProc (R' α)) → ν∈ P aR

ν-in : ∀ {m} (P : Proc (suc m)) aR  → ν∈ P aR → aR ← νProc P
ν-in P aR (pr a' R' prf x p) =
  J (λ x eq → x ← νProc P)
    (subst ((prf .fst , (λ α → νProc (R' α))) ←_)
           (sym (λ i → isCCS-alg.νX (fix-eq ProcCCS-algF i _) P))
           (bind-in stepν (prf .fst , (λ α → νProc (R' α))) (Unfold P) (_ , x , aux prf R')))
    (sym p)
  where
   aux : ∀ {n} {a' : Act (suc n)}
       (prf : Σ (Act n) (isActι a'))
       (R' : (x : Tick) → Proc (suc n)) →
       ⟨ (prf .fst , (λ α → νProc (R' α))) ∈ stepν (a' , R') ⟩
   aux (.(inp a) , inp a) R' with decName (ι a) (fresh _)
   ... | yes p = ⊥-rec (fresh-ι p)
   ... | no ¬p = ∣ StepPath (cong {B = λ _ → Act _} inp (sym (down-ι ¬p))) refl ∣₁
   aux (.(out a) , out a) R' with decName (ι a) (fresh _)
   ... | yes p = ⊥-rec (fresh-ι p)
   ... | no ¬p = ∣ StepPath (cong {B = λ _ → Act _} out (sym (down-ι ¬p))) refl ∣₁
   aux (.τ , τ) R' = ∣ refl ∣₁

-- Using these equivalent characterizations of reductions from parProc
-- and νProc, the relation (λ P a P' → (a , next P') ← P) is easily
-- shown to model all the rules of the CCS-operational semantics.
acttrProc : {n : ℕ} {P : Proc n} (a : Act n) →
     (a , next P) ← actProc a P
acttrProc a = ∣ refl ∣₁

sumtrProc : {n : ℕ} {P Q : Proc n} {P' : Proc n} {a : Act n} →
  (a , next P') ← P →
  (a , next P') ← sumProc P Q
sumtrProc {P = P}{Q} mP' = ∪-in-L {P = Unfold P} {Unfold Q} mP'

partrProc : {n : ℕ} {P Q : Proc n} {P' : Proc n} {a : Act n} →
  (a , next P') ← P →
  (a , next (parProc P' Q)) ← parProc P Q
partrProc {P = P} {Q} mP' = par-in {P = P}{Q} (parL _ mP' refl)

next-parProc : ▹ ({n : ℕ} → Proc n → Proc n → Proc n)
next-parProc α = parProc

comProc : {n : ℕ} {P Q P' Q' : Proc n} {a : Name n} →
  (out a ,  next P') ← P → (inp a , next Q') ← Q →
  (τ , next (parProc P' Q')) ← parProc P Q
comProc {P = P}{Q}{P'}{Q'}{a} mP' mQ' =
  par-in {P = P} {Q}
    (parS _ _ mP' mQ'
      (∪-in-L {P = Synch'.synch' parX' (out a , next P') (inp a , next Q')}
              {ø}
              (synch'-in-s next-parProc ∣ _ , _ , _ , refl , refl , refl ∣₁)))

resProc : {n : ℕ} {P P' : Proc (suc n)} {a : Act n} →
    (mapAct ι a , next P') ← P →
    (a , next (νProc P')) ← νProc P
resProc {P = P}{a = out a} mP' = ν-in P _ (pr _ _ (_ , out _) mP' refl)
resProc {P = P}{a = inp a} mP' = ν-in P _ (pr _ _ (_ , inp _) mP' refl)
resProc {P = P}{a = τ} mP' = ν-in P _ (pr _ _ (_ , τ) mP' refl)

ProcDynamics : Dynamics ProcCCS-alg _≡_ (λ P a P' → (a , next P') ← P)
ProcDynamics = record
               { actX = acttrProc
               ; sumtrX = λ {n}{P}{Q} → sumtrProc {n}{P}{Q}
               ; partrX = λ {n}{P}{Q} → partrProc {n}{P}{Q}
               ; comX = λ {n}{P}{Q} → comProc {n}{P}{Q}
               ; resX = λ {n}{P} → resProc {n}{P}
               ; convX = λ tr eq eq' →
                       transport (cong₂ (\ P P' → (_ , next P') ← P) eq eq') tr
               }



