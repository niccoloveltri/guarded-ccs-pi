{-# OPTIONS --cubical --guarded #-}

open import Cubical.Data.Sum as Sum hiding (inl; inr) 
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (act)
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.Relation.Nullary
open import LaterPrims hiding (_∙_)
open import CountablePowerSet
open import Basic
open import AbsNames

module ccs.semantics.Algebra (ns : Names) where

open Names ns
open OpNames ns
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
open import ccs.Syntax ns
open import ccs.Algebra ns

-- The type of steps, which are pairs of an action and an element of X
-- n (think of X as a CCS-algebra or the type of semantic processes)
record Step (X : ℕ → Set) (n : ℕ) : Set where
  constructor _,_
  field
    theLabel : Act n
    theX    : X n

open Step public

StepPath : ∀ {X : ℕ → Set} {n} {x y : Step X n}
  → theLabel x ≡ theLabel y
  → theX x ≡ theX y
  → x ≡ y
StepPath a xy = \ i → a i , xy i

pattern `τ p = τ , p
pattern `out a p = out a , p
pattern `inp a p = inp a , p

-- The functor F, describing one step of the transition relation, so
-- that a coalgebra c : ∀{n} → X n → F n X takes processes to the
-- collection of reachable processes (in the next time step).
F' : ∀ n (X : ▹ (ℕ → Set)) → Set
F' n X = P∞ (Step (\ m → ▸ \ α → X α m) n)

-- Variant of F without later modality.
F : ℕ → (ℕ → Set) → Set
F n X = P∞ (Step X n)

-- The denotational domain of processes. Notice that this is an
-- 'inductive' record, but the presence of the later modality in the
-- definition of F makes it a guarded recursive type. Proc could be
-- equivalently defined using the primitive fix operator.
record Proc (n : ℕ) : Set where
  inductive
  constructor Fold
  field
    Unfold : F' n (\ _ → Proc)

open Proc public

isSetProc : ∀ n → isSet (Proc n)
isSetProc n = isOfHLevelRetract 2 Proc.Unfold Fold (\ _ → refl) trunc

-- Estensional equality in Proc.
_←_ : ∀ {n} aQ → (P : Proc n) → Set
aQ ← (Fold P) = ⟨ aQ ∈ P ⟩

abstract
  Proc-ext : ∀ {n} {P : Proc n} {Q} → (∀ x → x ← P → x ← Q) → (∀ x → x ← Q → x ← P) → P ≡ Q
  Proc-ext p q = cong Fold (P∞-ext (p , q))

-- F' (when applied to type family (λ _ → Proc)) acts on renamings.
-- The action is defined via the fixpoint operator.
mapProcF : ▹ (∀ n m → (f : Name n → Name m) → F' n (λ _ → Proc) → F' m (λ _ → Proc))
  → ∀ n m → (f : Name n → Name m) → F' n (λ _ → Proc) → F' m (λ _ → Proc)
mapProcF h n m f p =
  mapP∞ (λ aq → mapAct f (theLabel aq) , λ α → Fold (h α n m f (Unfold (theX aq α))) ) p

abstract
  mapProc' : ∀ n m → (f : Name n → Name m) → F' n (λ _ → Proc) → F' m (λ _ → Proc)
  mapProc' = fix mapProcF

  mapProc'-eq : mapProc' ≡ mapProcF (next mapProc')
  mapProc'-eq = fix-eq mapProcF

-- Proc acts on (injective) renamings, functorially.
mapProc : ∀ n m → (f : Name n → Name m) → Proc n → Proc m
mapProc n m f p .Unfold = mapProc' n m f (Unfold p)

mapProc'-eq' : ∀ n m f p → mapProc' n m f p ≡ mapProcF (next mapProc') n m f p
mapProc'-eq' n m f p i = mapProc'-eq i n m f p

mapProc-id : ∀ m Q → mapProc m m (\ x → x) Q ≡ Q
mapProc-id = fix \ ih m Q → cong Fold (
  mapProc'-eq' _ _ _ _
  ∙ cong′ (λ x → mapP∞ x (Unfold Q)) (funExt (λ { aQ' →
      StepPath (mapAct-id _) (later-ext (λ α → ih α _ (theX aQ' α))) }))
  ∙ mapidP∞ (Unfold Q))

mapmapProc : ∀ l m n (f : Name _ → Name _) (g : Name _ → Name _) p →
  mapProc n m f (mapProc l n g p) ≡ mapProc _ m (\ x → f (g x)) p
mapmapProc = fix \ where
  ih l m n f g p →
    cong (mapProc _ _ _) (cong Fold (mapProc'-eq' _ _ _ _))
    ∙ cong Fold
      (mapProc'-eq' _ _ _ _
       ∙ mapmapP∞ _ _ (Unfold p)
       ∙ cong′ (λ x → mapP∞ x (Unfold p)) (funExt (λ { aQ' →
           StepPath (mapmapAct _) (later-ext (λ α → ih α _ _ _ _ _ (theX aQ' α)))})))
    ∙ sym (cong Fold (mapProc'-eq' _ _ _ _))

∪-map : ∀ {n m} (f : Name n → Name m) P Q
  → mapProc' n m f (P ∪ Q) ≡ mapProc' n m f P ∪ mapProc' n m f Q
∪-map f P Q =
  mapProc'-eq' _ _ _ _
  ∙ cong₂ _∪_ (sym (mapProc'-eq' _ _ _ _)) (sym (mapProc'-eq' _ _ _ _))

mapProc-Inj : ∀ n m → (f : Inj n m) → Proc n → Proc m
mapProc-Inj n m (f , _) = mapProc n m f

-- Step also has its own action on renamings.
mapSProc : ∀ n m (f : Name n → Name m) → Step (\ n → ▹ Proc n) n → F' m (λ _ → Proc)
mapSProc n m f aq = mapProcF (next mapProc') _ _ f (η aq)

mapSProc' : ∀ n m (f : Name n → Name m) → Step (\ n → ▹ Proc n) n → Step (\ n → ▹ Proc n) m
mapSProc' n m f (a , Q) = mapAct f a , λ α → Fold (mapProc' _ _ f (Unfold (Q α)))

mapProc-swap : ∀ {m} (P : Proc (suc (suc m)))
  → mapProc _ _ swap P ≡ Fold (mapP∞ (mapSProc' _ _ swap) (Unfold P))
mapProc-swap P = cong Fold (mapProc'-eq' _ _ _ (Unfold P))

-- Some useful definitions for checking whether two processes can
-- synchronize.
data CanSynchL? {n : ℕ} : Act n → Act n → Set where
  local : ∀ {a a'} → a ≡ a' → CanSynchL? (out a) (inp a')
  nope : ∀ {p q} → CanSynchL? p q

canSynchL? : {n : ℕ} → (p : Act n) → (q : Act n) → CanSynchL? p q
canSynchL? τ           _ = nope
canSynchL? (inp _) _ = nope
canSynchL? (out a) (inp a') with decName a a'
... | no _    = nope
... | yes ceq = local ceq
canSynchL? _ _ = nope

-- Some useful definitions for checking whether a process can
-- transition under restriction.
data CannotNu {n : ℕ} : Act (suc n) → Set where
  out : ∀ {a'} → a' ≡ fresh _ → CannotNu (out a')
  inp : ∀ {a'} → a' ≡ fresh _ → CannotNu (inp a')

data CanNu? {n : ℕ} : Act (suc n) → Set where
  out : ∀ {a a'} → a' ≡ ι a → CanNu? (out a')
  inp : ∀ {a a'} → a' ≡ ι a → CanNu? (inp a')
  τ : CanNu? τ
  nope : ∀{a} → CannotNu a → CanNu? a

canNu? : ∀ {n} → (a : Act (suc n)) → CanNu? a
canNu? (out a) with decName a (fresh _)
... | yes r = nope (out (r))
... | no ¬r = out ((sym (ι-down ¬r)))
canNu? (inp a) with decName a (fresh _)
... | yes r = nope (inp (r))
... | no ¬r = inp ((sym (ι-down ¬r)))
canNu? τ = τ

-- We want to define an CCS-algebra structure on Proc. This will be
-- defined by guarded recursion (i.e. using fix). Instead of defining
-- all the relevant operations directly on Proc, we do it on a general
-- type family X : ℕ → Set, which is endowed with a CCS-algebra
-- structure "in the next time step", which also acts on renaming.
module StepLemmata
  (X : ℕ → Set)
  (X-alg : ▹ (∀ n → isCCS-alg X n))
  (mapX : ∀ {n m} → (Name m → Name n) → X m → X n)
  where

  parX' : ▹ (∀ {n} → X n → X n → X n)
  parX' α {n} = X-alg α n .isCCS-alg.parX

  νX' : ▹ (∀ {n} → X (suc n) → X n)
  νX' α {n} = X-alg α n .isCCS-alg.νX

-- The stepL operation, which is the semantic counterpart of the rule
-- PAR: If a process p steps to p' with label 'a', then the (semantic)
-- parallel composition of p and q steps with label 'a' to the
-- parallel composition of p' and q. 
  stepL' : ∀ {n} → F' n (\ _ → X) → ▹ X n → F' n (\ _ → X)
  stepL' sp q = mapP∞ (λ p → theLabel p , λ α → parX' α (theX p α) (q α)) sp

  stepL : ∀ {n} → F' n (\ _ → X) → X n → F' n (\ _ → X)
  stepL sp q = stepL' sp (λ _ → q)

-- The symmetric of stepL.
  stepR : ∀ {n} → X n → F' n (\ _ → X) → F' n (\ _ → X)
  stepR p sq = mapP∞ (λ q → theLabel q , λ α → parX' α p (theX q α)) sq

-- The synch operation, the semantic counterpart of the rule
-- COM. First we check if the two processes can synchronize (via
-- CanSynchL?), if they can their parallel composition steps with a
-- silent action to the parallel composition of the new processes.
  module Synch' (parX : ▹ (∀ {n} → X n → X n → X n)) where

    synch'-aux : ∀ {n} (p q : Step (\ n → ▹ X n) n)
      → CanSynchL? (theLabel p) (theLabel q) → F' n (\ _ → X)
    synch'-aux (a , p') (b , q') (local _) = η (τ , \ α → parX α (p' α) (q' α))
    synch'-aux (a , p') (b , q') nope   = ø

    synch' : ∀ {n} → Step (\ n → ▹ X n) n → Step (\ n → ▹ X n) n → F' n (\ _ → X)
    synch' p@(a , p') q@(b , q') = synch'-aux p q (canSynchL? a b)

    synchF' : ∀ {n} → (a b : F' n (\ _ → X)) → F' n (\ _ → X)
    synchF' a b = bind a \ a' → bind b \ b' → synch' a' b'

  open Synch'

  synch : ∀ {n} → Step (\ n → ▹ X n) n → Step (\ n → ▹ X n) n → F' n (\ _ → X)
  synch {n} p q = synch' parX' p q ∪ synch' (\ α p' q' → parX' α q' p') q p

  synchF : ∀ {n} → (a b : F' n (\ _ → X)) → F' n (\ _ → X)
  synchF a b = bind a \ a' → bind b \ b' → synch a' b'

-- The parallel composition in the semantics. Given a processes p
-- stepping to sp (a countable set of pairs of actions and new
-- processes, i.e. the processes reachable from p in one step) and a
-- process q stepping to sq, their parallel composition is given by
-- the union of all the possibilities where p steps and q does not,
-- q steps but p does not, and p and q synchronize.
  par : ∀ {n} → X n → F' n (\ _ → X) → X n → F' n (\ _ → X) → F' n (\ _ → X)
  par p sp q sq = (stepL sp q ∪ stepR p sq) ∪ (bind sp \ sp → bind sq \ sq → synch sp sq)

-- The semantic restriction operator. When p steps to p' with action
-- 'a', then the restriction of p steps to the restriction of p'
-- provided that 'a' is not fresh (as in the rule RES).
  stepν : ∀ {n} → Step (\ n → ▹ X n) (suc n) → F' n \ _ → X
  stepν (a , p) with canNu? a
  stepν (.(out _) , p) | out {a = a} x  = η (`out a (λ α → νX' α (p α)))
  stepν (.(inp _) , p) | inp {a = a} x = η (`inp a (λ α → νX' α (p α)))
  stepν (.τ , p) | τ = η (`τ (λ α → νX' α (p α)))
  stepν (a , p) | nope _ = ø

  stepνF : ∀ {n} → F' (suc n) (\ _ → X) → F' n \ _ → X
  stepνF p = bind p stepν

-- The same operations in the module StepLemmata above can be defined
-- directly for CCS.
module StepLemmataCCS where

  stepL : ∀ {n} → F n CCS → CCS n → F n CCS
  stepL sp q = mapP∞ (λ p → theLabel p , theX p ∣∣ q) sp

  stepR : ∀ {n} → CCS n → F n CCS → F n CCS
  stepR p sq = mapP∞ (λ q → theLabel q , p ∣∣ theX q) sq

  module Synch' (parX : ∀ {n} → CCS n → CCS n → CCS n) where

    synch'-aux : ∀ {n} (p q : Step CCS n) 
      → CanSynchL? (theLabel p) (theLabel q) → F n CCS
    synch'-aux (a , p') (b , q') (local _) = η (τ , parX p' q')
    synch'-aux (a , p') (b , q') nope   = ø

    synch' : ∀ {n} → Step CCS n → Step CCS n → F n CCS
    synch' p@(a , p') q@(b , q') = synch'-aux p q (canSynchL? a b)

    synchF' : ∀ {n} (a b : F n CCS) → F n CCS
    synchF' a b = bind a \ a' → bind b \ b' → synch' a' b'

  open Synch'
  
  synch : ∀ {n} → Step CCS n → Step CCS n → F n CCS
  synch {n} p q = synch' _∣∣_ p q ∪ synch' (λ x y → y ∣∣ x) q p

  synchF : ∀ {n} → (a b : F n CCS) → F n CCS
  synchF a b = bind a \ a' → bind b \ b' → synch a' b'

  par : ∀ {n} → CCS n → F n CCS → CCS n → F n CCS → F n CCS
  par p sp q sq = (stepL sp q ∪ stepR p sq) ∪ (bind sp \ sp → bind sq \ sq → synch sp sq)

  stepν : ∀ {n} → Step CCS (suc n) → F n CCS
  stepν (a , p) with canNu? a
  stepν (.(out _) , p) | out {a = a} x  = η (`out a (ν p))
  stepν (.(inp _) , p) | inp {a = a} x = η (`inp a (ν p))
  stepν (.τ , p) | τ = η (`τ (ν p))
  stepν (a , p) | nope _ = ø

  stepνF : ∀ {n} → F (suc n) CCS → F n CCS
  stepνF p = bind p stepν


-- We obtain a CCS-algebra structure on Proc by guarded recursion.
module _ (ih : ▹ ((n : ℕ) → isCCS-alg Proc n)) where

  open isCCS-alg
  open StepLemmata Proc ih (mapProc _ _)

  !F : ∀ {n} → Proc n → ▹ F' n (λ _ → Proc) → F' n (λ _ → Proc)
  !F p !p = stepL' (Unfold p ∪ synchF (Unfold p) (Unfold p)) λ α → Fold (!p α)

  ProcCCS-algF : (n : ℕ) → isCCS-alg Proc n
  endX (ProcCCS-algF n) = Fold ø
  actX (ProcCCS-algF n) a p = Fold (η (a , (λ _ → p)))
  sumX (ProcCCS-algF n) p q = Fold (Unfold p ∪ Unfold q)
  parX (ProcCCS-algF n) p q = Fold (par p (Unfold p) q (Unfold q))
  νX (ProcCCS-algF n) p = Fold (stepνF (Unfold p))
  !X (ProcCCS-algF n) p = Fold (fix (!F p))

ProcCCS-alg : ∀ n → isCCS-alg Proc n
ProcCCS-alg = fix ProcCCS-algF

-- We give names to the CCS operations in Proc.
endProc : ∀ {n} → Proc n
endProc {n} = ProcCCS-alg n .isCCS-alg.endX

actProc : ∀ {n} (a : Act n) (p : Proc n) → Proc n
actProc {n} = ProcCCS-alg n .isCCS-alg.actX

sumProc : ∀ {n} → Proc n → Proc n → Proc n
sumProc {n} = ProcCCS-alg n .isCCS-alg.sumX

parProc : ∀ {n} → Proc n → Proc n → Proc n
parProc {n} = ProcCCS-alg n .isCCS-alg.parX

νProc : ∀ {n} → Proc (suc n) → Proc n
νProc {n} = ProcCCS-alg n .isCCS-alg.νX

!Proc : ∀ {n} → Proc n → Proc n
!Proc {n} = ProcCCS-alg n .isCCS-alg.!X

-- The unfolding equation of !Proc.
module _ where
  open StepLemmata Proc (\ α n → ProcCCS-alg n) (mapProc _ _)

  !Proc-eq : ∀ {n} {P : Proc n}
    → !Proc P ≡ Fold (stepL (Unfold P) (!Proc P) ∪ stepL (synchF (Unfold P) (Unfold P)) (!Proc P))
  !Proc-eq {n} {P} =
    cong′ (λ x → isCCS-alg.!X (x n) P) (fix-eq ProcCCS-algF) ∙ cong Fold (fix-eq d) ∙ cong Fold (cong₂ _∪_ (cong (stepL (Unfold P))
          (sym (cong′ (λ x → isCCS-alg.!X (x n) P) (fix-eq ProcCCS-algF))))
          (cong (stepL (synchF (Unfold P) (Unfold P))) (sym (cong′ (λ x → isCCS-alg.!X (x n) P) (fix-eq ProcCCS-algF)))))
    where
      d = λ !p → stepL' (Unfold P ∪ synchF (Unfold P) (Unfold P)) (λ α → Fold (!p α))
