{-# OPTIONS --cubical --guarded #-}

open import Cubical.Data.Sum as Sum hiding (inl; inr) 
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (act;lift;assoc)
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.Relation.Nullary
open import LaterPrims hiding (_∙_)
open import CountablePowerSet
open import Basic
open import AbsNames

module pi-calculus.semantics.Algebra (ns : Names) where

open Names ns
open OpNames ns
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
open import pi-calculus.Syntax ns
open import pi-calculus.Algebra ns

-- The type of steps, which are pairs of an action and an element of X
-- n (think of X as a Pi-algebra or the type of semantic processes)
record Step (X : ℕ → Set) (n : ℕ) : Set where
  constructor _,_
  field
    {theM} : ℕ
    theLabel : Label n theM
    theX    : X theM

open Step public

StepPath : ∀ {X : ℕ → Set} {n} {x y : Step X n} (m : theM x ≡ theM y)
  → PathP (\ i → Label n (m i)) (theLabel x) (theLabel y)
  → PathP (\ i → X (m i)) (theX x) (theX y) → x ≡ y
StepPath m a xy = \ i → a i , xy i

pattern `τ p = τ , p
pattern `out ch z p = out ch z , p
pattern `bout ch p  = bout ch , p
pattern `inp ch v p = inp ch v , p
pattern `binp ch p = binp ch , p

mapStep : ∀ {X Y}{n} → (f : ∀ m → Inj n m → X m → Y m)
  → Step X n → Step Y n
mapStep f (a , x') = a , f _ (labelInj a) x'

-- The functor F, describing one step of the transition relation, so
-- that a coalgebra c : ∀{n} → X n → F n X takes processes to the
-- collection of reachable processes (in the next time step).
F' : ∀ n (X : ▹ (ℕ → Set)) → Set
F' n X = P∞ (Step (\ m → ▸ \ α → X α m) n)

mapF' : ∀ {X Y} {n} (f : ▸ (\ α → ∀ m → Inj n m → X α m → Y α m))
  → F' n X → F' n Y
mapF' f sp = mapP∞ (mapStep (\ m i x α → f α m i (x α))) sp

-- Variant of F without later modality.
F : ℕ → (ℕ → Set) → Set
F n X = P∞ (Step X n)

mapF : ∀ {X Y : ℕ → Set} {n} (f : ∀ m → Inj n m → X m → Y m) → F n X → F n Y
mapF f x = mapP∞ (mapStep f) x

-- A denotational domain of processes. Notice that this is an
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
isSetProc n = isSetRetract Unfold Fold (\ _ → refl) trunc

-- Estensional equality in Proc.
_←_ : ∀ {n} aQ → (P : Proc n) → Set
aQ ← (Fold P) = ⟨ aQ ∈ P ⟩

abstract
  Proc-ext : ∀ {n} {P : Proc n} {Q}
    → (∀ x → x ← P → x ← Q) → (∀ x → x ← Q → x ← P)
    → P ≡ Q
  Proc-ext p q = cong Fold (P∞-ext (p , q))

data Binp? {n} : ∀ {m} → Label n m → Set where
  binp : ∀ {ch} → Binp? (binp ch)
  nope : ∀ {m p} → Binp? {n} {m} p

binp? : ∀ {n m} → (l : Label n m) → Binp? l
binp? (binp ch) = binp
binp? _ = nope

-- F' (when applied to type family (λ _ → Proc)) acts on renamings.
-- The action is defined via the fixpoint operator.
module _ (ih : ▹ (∀ n m → (f : Name n → Name m) → F' n (λ _ → Proc) → F' m (λ _ → Proc)))
       where
  abstract
    inps' : ∀ {n m} (f : Name n → Name m) → Name n → ▹ Proc (suc n) → F' m (λ _ → Proc)
    inps' f ch Q =
      bind (neg (image f) (image-fn _))
        \ z → η (inp (f ch) z , \ α → Fold (ih α _ _ (snoc f z) (Unfold (Q α))) )

    inps'-eq : ∀ {n m} (f : Name n → Name m) (ch : Name n) (Q : ▹ Proc (suc n))
      → inps' f ch Q ≡
        bind (neg (image f) (image-fn _))
          \ z → η (inp (f ch) z , \ α → Fold (ih α _ _ (snoc f z) (Unfold (Q α))))
    inps'-eq f ch Q = refl
  
  inps : ∀ {n m} (f : Name n → Name m) → Step (\ n → ▹ Proc n) n
    → F' m (\ _ → Proc) → F' m (λ _ → Proc)
  inps f (a , Q) x with binp? a
  ... | binp {ch} = x ∪ inps' f ch Q
  ... | nope = x

  mapProcF : ∀ n m (f : Name n → Name m) → F' n (λ _ → Proc) → F' m (λ _ → Proc)
  mapProcF n m f p =
    bind p
      λ aq → inps f aq
                    (η (mapLabel f (theLabel aq) ,
                        λ α → Fold (ih α _ _ (labelRen (theLabel aq) _ f) (Unfold (theX aq α)))))

abstract
  mapProc' : ∀ n m → (f : Name n → Name m) → F' n (λ _ → Proc) → F' m (λ _ → Proc)
  mapProc' = fix mapProcF

  mapProc'-eq : mapProc' ≡ mapProcF (next mapProc')
  mapProc'-eq = fix-eq mapProcF

  inps-ι : ∀ {n} → (ch : Name n) (Q : ▹ Proc (suc n))
    → inps' (\ _ → mapProc') ι ch Q ≡ η (inp (ι ch) (fresh _) , \ α → Fold (mapProc' _ _ (snoc ι (fresh _)) (Unfold (Q α))) )
  inps-ι ch Q = cong₂ bind (neg-image-ι) refl

inps'2 : ∀ {n m} → (f : Name n → Name m) (aQ : Step (\ n → ▹ Proc n) n) → F' m (\ _ → Proc)
inps'2 f (a , Q) with binp? a
... | binp {ch} = inps' (\ _ → mapProc') f ch Q
... | nope = ø

-- Proc acts on (injective) renamings, functorially.
mapProc : ∀ n m → (f : Name n → Name m) → Proc n → Proc m
mapProc n m f p .Unfold = mapProc' n m f (Unfold p)

mapProc'-eq' : ∀ n m f p → mapProc' n m f p ≡ mapProcF (next mapProc') n m f p
mapProc'-eq' n m f p i = mapProc'-eq i n m f p

mapProc-Inj : ∀ n m (f : Inj n m) → Proc n → Proc m
mapProc-Inj n m (f , _) = mapProc n m f

-- Step also has its own action on renamings.
mapSProc : ∀ n m (f : Name n → Name m) → Step (\ n → ▹ Proc n) n → F' m (λ _ → Proc)
mapSProc n m f aq = mapProcF (next mapProc') _ _ f (η aq)

mapSProc' : ∀ n m (f : Name n → Name m) → Step (\ n → ▹ Proc n) n → Step (\ n → ▹ Proc n) m
mapSProc' n m f (a , Q) = mapLabel f a , λ α → Fold (mapProc' _ _ (labelRen a _ f) (Unfold (Q α)))

inps-eq : ∀ {n m} (f : Name n → Name m) (aQ : Step (\ n → ▹ Proc n) n)
  → (x : F' m (\ _ → Proc)) → inps (\ _ → mapProc') f aQ x ≡ x ∪ inps'2 f aQ
inps-eq f (a , Q) x with binp? a
inps-eq f (.(binp _) , Q) x | binp = refl
inps-eq f (a , Q) x | nope = sym (unit _)

inps'2-id : ∀ {m} aQ → inps'2 (\ (x : Name m) → x) aQ ≡ ø
inps'2-id (a , Q) with binp? a
... | binp {ch} = inps'-eq _ _ _ Q ∙ cong₂ bind neg-image-id refl
... | nope = refl

inps'2-swap : ∀ {m} aQ → inps'2 (swap {m}) aQ ≡ ø
inps'2-swap (a , Q) with binp? a
... | binp {ch} = inps'-eq _ _ _ Q ∙ cong₂ bind (neg-image-swap) refl
... | nope = refl

mapSProc'-id : ∀ (ih : ▹ ((m₁ : ℕ) (Q₁ : Proc m₁) → mapProc m₁ m₁ (λ x → x) Q₁ ≡ Q₁))
  → ∀ m Q → mapSProc' m m (\ x → x) Q ≡ Q
mapSProc'-id ih m (`out x x₁ Q) = StepPath refl refl (later-ext (\ α → ih α _ _))
mapSProc'-id ih m (`bout x Q) =
  StepPath refl refl (later-ext (\ α → cong₂ (mapProc _ _) (funExt lift-id) refl ∙ ih α _ _))
mapSProc'-id ih m (`inp x x₁ Q) = StepPath refl refl (later-ext (\ α → ih α _ _))
mapSProc'-id ih m (`binp x Q) =
  StepPath refl refl (later-ext (\ α → cong₂ (mapProc _ _) (funExt lift-id) refl ∙ ih α _ _))
mapSProc'-id ih m (`τ Q) = StepPath refl refl (later-ext (\ α → ih α _ _))

mapProc-id : ∀ m Q → mapProc m m (\ x → x) Q ≡ Q
mapProc-id = fix \ ih m Q → cong Fold (
  mapProc'-eq' _ _ _ _)
  ∙ cong Fold (cong′ (bind (Unfold Q)) (funExt \ aq →
         inps-eq (\ x → x) aq _
         ∙ cong₂ _∪_ refl (inps'2-id aq)
         ∙ unit _ ∙ cong′ η (mapSProc'-id ih _ aq)))
  ∙ cong Fold (bind-η (Unfold Q))

mapmapProc' : ∀ l m n (f : Inj _ _) (g : Name _ → Name _) p
  → mapProc n m (fst f) (mapProc l n g p) ≡ mapProc _ m (\ x → fst f (g x)) p
mapmapProc' = fix \ where
  ih l m n f'@(f , f-inj) g'@(g) p →
    cong (mapProc _ _ _) (cong Fold (mapProc'-eq' _ _ _ _))
    ∙ cong Fold (mapProc'-eq' _ _ _ _)
    ∙ cong Fold (bind-bind (Unfold p) _ _ ∙ cong′ (bind (Unfold p)) (funExt
      (λ { (`τ q) → cong′ η (StepPath refl refl (later-ext (λ α → ih α _ _ _ f' g' (q α))))
         ; (`out ch z q) → cong′ η (StepPath refl refl (later-ext (λ α → ih α _ _ _ f' g' (q α))))
         ; (`inp ch v q) → cong′ η (StepPath refl refl (later-ext (λ α → ih α _ _ _ f' g' (q α))))
         ; (`bout ch q) → cong′ η (StepPath refl refl (later-ext (λ α → ih α _ _ _ (lift f , lift-inj f') (lift g) (q α) ∙
           cong Fold (cong′ (λ k → mapProc' _ _ k (Unfold (q α))) (λ i v → liftlift f g v i)))))
         ; (`binp ch q) → sym (assoc _ _ _) ∙ cong₂ _∪_
           (cong′ η (cong′ (`binp (f (g ch)))
             (later-ext (λ α → ih α _ _ _ (lift f , lift-inj f') (lift g) (q α) ∙ cong Fold (cong′ (λ k → mapProc' _ _ k (Unfold (q α))) (λ i v → liftlift f g v i))))))
           ( (cong₂ _∪_ (inps'-eq _ _ _ _ ∙ cong-bind (neg (image f) (image-fn _)) (\ z mz → cong′ η (cong′ (`inp (f (g ch)) z)
             (later-ext \ α → ih α _ _ _ (snoc f z , snoc-inj f' z mz) (labelRen (binp ch) n g) (q α) ∙ cong₂ (mapProc _ _) (funExt \ x → snoc-lift f g z x) refl))))
                      (cong₂ bind (inps'-eq _ _ _ q) refl ∙ bind-bind (neg (image g) (image-fn _)) _ _)
            ∙ (cong₂ _∪_ refl (cong-bind (neg (image g) (image-fn _)) (\ a ma → cong′ η (StepPath refl refl (later-ext \ α → ih α _ _ _ f' (_) (q α)
                                                                   ∙ cong₂ (mapProc _ _) (funExt \ v → snoc-∘ f g a v) refl )))
              ∙ sym (bind-map (neg (image g) (image-fn _)) _ _)) ∙ cong₂ bind (sym (neg-image-∘ f' g' )) refl)
            ∙ sym (inps'-eq _ _ _ q)) )
           })))
    ∙ sym (cong Fold (mapProc'-eq' _ _ _ _))

mapmapProc : ∀ l m n (f : Inj _ _) (g : Inj _ _) p
  → mapProc n m (fst f) (mapProc l n (fst g) p) ≡ mapProc _ m (\ x → fst f (fst g x)) p
mapmapProc l m n f (g , _) p = mapmapProc' l m n f g p

∪-map : ∀ {n m} (f : Name n → Name m) P Q
  → mapProc' n m f (P ∪ Q) ≡ mapProc' n m f P ∪ mapProc' n m f Q
∪-map f P Q =
  mapProc'-eq' _ _ _ _
  ∙ cong₂ _∪_ (sym (mapProc'-eq' _ _ _ _)) (sym (mapProc'-eq' _ _ _ _))

mapProc-swap : ∀ {m} (P : Proc (suc (suc m)))
  → mapProc _ _ swap P ≡ Fold (mapP∞ (mapSProc' _ _ swap) (Unfold P))
mapProc-swap P =
  cong Fold (mapProc'-eq' _ _ _ (Unfold P)
            ∙ cong′ (bind (Unfold P))
                (funExt \ aq → inps-eq _ aq _ ∙ cong₂ _∪_ refl (inps'2-swap aq) ∙ unit _)
            ∙ sym (mapP∞-is-bind (Unfold P)))

-- Some useful definitions for checking whether two processes can
-- synchronize.
data CanSynchL? {n : ℕ} : ∀ {m m'} → Label n m → Label n m' → Set where
  local : ∀ {ch z ch' z'} → ch ≡ ch' → z ≡ z' → CanSynchL? (out ch z) (inp ch' z')
  bound : ∀ {ch ch'} → ch ≡ ch'  → CanSynchL? (bout ch) (binp ch')
  nope : ∀ {m m' p q} → CanSynchL? {n = n} {m} {m'} p q

canSynchL? : {n m m' : ℕ} → (p : Label n m) → (q : Label n m') → CanSynchL? p q
canSynchL? τ           _ = nope
canSynchL? (inp _ _) _ = nope
canSynchL? (binp _)   _ = nope
canSynchL? (out ch z) (inp ch' v') with decName ch ch' | decName z v'
... | no _    | _       = nope
... | yes ceq | no _    = nope
... | yes ceq | yes zeq = local ceq zeq
canSynchL? (bout ch) (binp ch') with decName ch ch'
... | no _ = nope
... | yes ceq = bound ceq
canSynchL? _ _ = nope

data CannotNu {n : ℕ} : ∀ {m} → Label (suc n) m → Set where
  out : ∀ {ch' z'} → ch' ≡ fresh _ → CannotNu (out ch' z')
  inp : ∀ {ch' z'} → (ch' ≡ fresh _) ⊎ (z' ≡ fresh _) → CannotNu (inp ch' z')
  bout : ∀ {ch'} → ch' ≡ fresh _ → CannotNu (bout ch')
  binp : ∀ {ch'} → ch' ≡ fresh _ → CannotNu (binp ch')

data CanNu? {n : ℕ} : ∀ {m} → Label (suc n) m → Set where
  out : ∀ {ch' z' ch z} → ch' ≡ ι ch → z' ≡ ι z → CanNu? (out ch' z')
  out2 : ∀ {ch' z' ch} → ch' ≡ ι ch → z' ≡ fresh _ → CanNu? (out ch' z')
  inp : ∀ {ch' z' ch z} → ch' ≡ ι ch → z' ≡ ι z → CanNu? (inp ch' z')
  bout : ∀ {ch' ch} → ch' ≡ ι ch → CanNu? (bout ch')
  binp : ∀ {ch' ch} → ch' ≡ ι ch → CanNu? (binp ch')
  τ : CanNu? τ
  nope : ∀ {m p} → CannotNu p → CanNu? {_} {m} p

canNu? : ∀ {n m} → (a : Label (suc n) m) → CanNu? a
canNu? (out ch z ) with decName ch (fresh _) | decName z (fresh _)
canNu? (out ch z ) | yes r | _ = nope (out r)
canNu? (out ch z ) | no ¬r | yes p = out2 ((sym (ι-down ¬r))) (p)
canNu? (out ch z ) | no ¬r | no ¬p = out ((sym (ι-down ¬r))) ((sym (ι-down ¬p)))
canNu? (bout ch ) with decName ch (fresh _)
canNu? (bout ch ) | yes r = nope (bout (r))
canNu? (bout ch ) | no ¬r = bout ((sym (ι-down ¬r)))
-- we swapped the order of the binders, so we have to swap vars
canNu? (binp ch ) with decName ch (fresh _)
canNu? (binp ch ) | yes r = nope (binp (r))
canNu? {n} (binp ch ) | no ¬r = binp ((sym (ι-down ¬r)))
-- we swapped the order of the binders, so we have to swap vars
canNu? {n} (inp ch v ) with decName ch (fresh n) | decName v (fresh n)
canNu? (inp ch v ) | yes r | _ = nope (inp (_⊎_.inl ((r))))
canNu? (inp ch v ) | no ¬r | yes s = nope (inp (_⊎_.inr ((s))))
canNu? (inp ch v ) | no ¬r | no ¬s = inp ((sym (ι-down ¬r))) ((sym (ι-down ¬s)))
canNu? (τ ) = τ

-- We want to define an Pi-algebra structure on Proc. This will be
-- defined by guarded recursion (i.e. using fix). Instead of defining
-- all the relevant operations directly on Proc, we do it on a general
-- type family X : ℕ → Set, which is endowed with a Pi-algebra
-- structure "in the next time step", which also acts on renaming.
module StepLemmata
  (X : ℕ → Set)
  (X-alg : ▹ (∀ n → isPi-alg X n))
  (mapX : ∀ {n m} → (Name m → Name n) → X m → X n)
  where

  stepguard : ∀ {n} (x y : Name n) → F' n (\ _ → X) → F' n (\ _ → X)
  stepguard x y p =
    case decName x y return const _ of \ { (yes _) → p ; (no ¬p) → ø }

  parX' : ▹ (∀ {n} → X n → X n → X n)
  parX' α {n} = X-alg α n .isPi-alg.parX

  νX' : ▹ (∀ {n} → X (suc n) → X n)
  νX' α {n} = X-alg α n .isPi-alg.νX

-- The stepL operation, which is the semantic counterpart of the rule
-- PAR: If a process p steps to p' with label 'a', then the (semantic)
-- parallel composition of p and q steps with label 'a' to the
-- parallel composition of p' and q. 
  stepL' : ∀ {n} → F' n (\ _ → X) → ▹ X n → F' n (\ _ → X)
  stepL' sp q = mapF' (\ α m i p → parX' α p (mapX (fst i) (q α))) sp

  stepL : ∀ {n} → F' n (\ _ → X) → X n → F' n (\ _ → X)
  stepL sp q = stepL' sp (λ _ → q)

-- The symmetric of stepL.
  stepR : ∀ {n} → X n → F' n (\ _ → X) → F' n (\ _ → X)
  stepR p sq = mapF' (λ α m i q → parX' α (mapX (fst i) p) q) sq

-- The synch operation, the semantic counterpart of the rule COM.
-- First we check if the two processes can synchronize (via
-- CanSynchL?), if they can their parallel composition steps with a
-- silent action to the parallel composition of the new processes.
  module Synch' (parX : ▹ (∀ {n} → X n → X n → X n))
                (νX : ▹ (∀ {n} → X (suc n) → X n)) where

    synch'-aux : ∀ {n} (p q : Step (\ n → ▹ X n) n)
      → CanSynchL? (theLabel p) (theLabel q) → F' n (\ _ → X)
    synch'-aux (a , p') (b , q') (local _ _) = η (`τ (\ α → parX α (p' α) (q' α)))
    synch'-aux (a , p') (b , q') (bound _)   = η (`τ (\ α → νX α (parX α (p' α) (q' α))))
    synch'-aux (a , p') (b , q') nope   = ø

    synch' : ∀ {n} → Step (\ n → ▹ X n) n → Step (\ n → ▹ X n) n → F' n (\ _ → X)
    synch' p@(a , p') q@(b , q') = synch'-aux p q (canSynchL? a b)

    synchF' : ∀ {n} → (a b : F' n (\ _ → X)) → F' n (\ _ → X)
    synchF' a b = bind a \ a' → bind b \ b' → synch' a' b'

  open Synch'

  synch : ∀ {n} → Step (\ n → ▹ X n) n → Step (\ n → ▹ X n) n → F' n (\ _ → X)
  synch {n} p q = synch' parX' νX' p q ∪ synch' (\ α p' q' → parX' α q' p') νX' q p

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
  stepν (.(out _ _) , p) | out {ch = ch} {z = z} x x₁ = η (`out ch z (\ α → νX' α (p α)))
  stepν (.(out _ _) , p) | out2 {ch = ch} x x₁ = η (`bout ch p)
  stepν (.(inp _ _) , p) | inp {ch = ch} {z = z} x x₁ = η (`inp ch z λ α → νX' α (p α))
  stepν (.(bout _) , p) | bout {ch = ch} x = η (`bout ch λ α → νX' α (mapX swap (p α)))
  stepν (.(binp _) , p) | binp {ch = ch} x = η (`binp ch λ α → νX' α {suc _} (mapX swap (p α)))
  stepν (.τ , p) | τ = η (`τ λ α → νX' α (p α))
  stepν (a , p) | nope _ = ø

  stepνF : ∀ {n} → F' (suc n) (\ _ → X) → F' n \ _ → X
  stepνF p = bind p stepν

-- The same operations in the module StepLemmata above can be defined
-- directly for Pi.
module StepLemmataPi where

  stepguard : ∀ {n} (x y : Name n) → F n Pi → F n Pi
  stepguard x y p = case decName x y return const _ of \ { (yes _) → p ; (no ¬p) → ø }

  stepL' : ∀ {n} → F n Pi → Pi n → F n Pi
  stepL' sp q = mapF (\ m i p → p ∣∣ mapPi (fst i) q) sp
    
  stepL : ∀ {n} → F n Pi → Pi n → F n Pi
  stepL sp q = stepL' sp (q)

  stepR : ∀ {n} → Pi n → F n Pi → F n Pi
  stepR p sq = mapF (λ m i q → mapPi (fst i) p ∣∣ q) sq

  module Synch' (parX : ∀ {n} → Pi n → Pi n → Pi n)
                (νX : ∀ {n} → Pi (suc n) → Pi n) where

    synch'-aux : ∀ {n} (p q : Step Pi n) → CanSynchL? (theLabel p) (theLabel q) → F n Pi
    synch'-aux (a , p') (b , q') (local _ _) = η (`τ (parX (p') (q')))
    synch'-aux (a , p') (b , q') (bound _)   = η (`τ (νX (parX (p') (q'))))
    synch'-aux (a , p') (b , q') nope   = ø

    synch' : ∀ {n} → Step Pi n → Step Pi n → F n Pi
    synch' {n} p@(a , p') q@(b , q') = synch'-aux p q (canSynchL? a b)

    synchF' : ∀ {n} → (a b : F n Pi) → F n Pi
    synchF' a b = bind a \ a' → bind b \ b' → synch' a' b'

  open Synch'
  
  synch : ∀ {n} → Step Pi n → Step Pi n → F n Pi
  synch {n} p q = synch' _∣∣_ ν p q ∪ synch' (λ x y → y ∣∣ x) ν q p

  synchF : ∀ {n} → (a b : F n Pi) → F n Pi
  synchF a b = bind a \ a' → bind b \ b' → synch a' b'

  par : ∀ {n} → Pi n → F n Pi → Pi n → F n Pi → F n Pi
  par p sp q sq = (stepL sp q ∪ stepR p sq) ∪ (bind sp \ sp → bind sq \ sq → synch sp sq)

  stepν : ∀ {n} → Step Pi (suc n) → F n Pi
  stepν (a , p) with canNu? a
  stepν (.(out _ _) , p) | out {ch = ch} {z = z} x x₁ = η (`out ch z (ν (p)))
  stepν (.(out _ _) , p) | out2 {ch = ch} x x₁ = η (`bout ch p)
  stepν (.(inp _ _) , p) | inp {ch = ch} {z = z} x x₁ = η (`inp ch z (ν (p)))
  stepν (.(bout _) , p) | bout {ch = ch} x = η (`bout ch (ν (mapPi swap (p))))
  stepν (.(binp _) , p) | binp {ch = ch} x = η (`binp ch (ν {suc _} (mapPi swap (p))))
  stepν (.τ , p) | τ = η (`τ (ν (p)))
  stepν (a , p) | nope _ = ø

  stepνF : ∀ {n} → F (suc n) Pi → F n Pi
  stepνF p = bind p stepν


-- We obtain a Pi-algebra structure on Proc by guarded recursion.
module _ (ih : ▹ ((n : ℕ) → isPi-alg Proc n)) where

  open isPi-alg
  open StepLemmata Proc ih (mapProc _ _)

  !F : ∀ {n} → Proc n → ▹ F' n (λ _ → Proc) → F' n (λ _ → Proc)
  !F p !p = stepL' (Unfold p ∪ synchF (Unfold p) (Unfold p)) λ α → Fold (!p α)

  ProcPi-algF : (n : ℕ) → isPi-alg Proc n
  endX (ProcPi-algF n) = Fold ø
  actX (ProcPi-algF n) τ p = Fold (η (`τ \ _ → p))
  actX (ProcPi-algF n) (out ch x) p =  Fold (η ((`out ch x (\ _ → p))))
  actX (ProcPi-algF n) (inp ch) p =
    Fold (bind enum (\ v → η ((`inp ch v \ α →  mapProc _ _ (v for-fresh_) p)))
          ∪ η (`binp ch \ α → p))
  sumX (ProcPi-algF n) p q = Fold (Unfold p ∪ Unfold q)
  parX (ProcPi-algF n) p q = Fold (par p (Unfold p) q (Unfold q))
  νX (ProcPi-algF n) p = Fold (stepνF (Unfold p))
  !X (ProcPi-algF n) p = Fold (fix (!F p))
  guardX (ProcPi-algF n) x y p = Fold (stepguard x y (Unfold p))

ProcPi-alg : ∀ n → isPi-alg Proc n
ProcPi-alg = fix ProcPi-algF

-- We give names to the Pi operations in Proc.
endProc : ∀ {n} → Proc n
endProc {n} = ProcPi-alg n .isPi-alg.endX

actProc : ∀ {n m} (a : Act n m) (p : Proc m) → Proc n
actProc {n} = ProcPi-alg n .isPi-alg.actX

sumProc : ∀ {n} → Proc n → Proc n → Proc n
sumProc {n} = ProcPi-alg n .isPi-alg.sumX

parProc : ∀ {n} → Proc n → Proc n → Proc n
parProc {n} = ProcPi-alg n .isPi-alg.parX

νProc : ∀ {n} → Proc (suc n) → Proc n
νProc {n} = ProcPi-alg n .isPi-alg.νX

!Proc : ∀ {n} → Proc n → Proc n
!Proc {n} = ProcPi-alg n .isPi-alg.!X

guardProc : ∀ {n} (x y : Name n) → Proc n → Proc n
guardProc {n} = ProcPi-alg n .isPi-alg.guardX

-- The unfolding equation of !Proc.
module _ where
  open StepLemmata Proc (\ α n → ProcPi-alg n) (mapProc _ _)

  !Proc-eq : ∀ {n} {P : Proc n}
    → !Proc P ≡ Fold (stepL (Unfold P) (!Proc P) ∪ stepL (synchF (Unfold P) (Unfold P)) (!Proc P))
  !Proc-eq {n} {P} =
    cong′ (λ x → isPi-alg.!X (x n) P) (fix-eq ProcPi-algF) ∙ cong Fold (fix-eq d) ∙ cong Fold (cong₂ _∪_ (cong (stepL (Unfold P))
          (sym (cong′ (λ x → isPi-alg.!X (x n) P) (fix-eq ProcPi-algF))))
          (cong (stepL (synchF (Unfold P) (Unfold P))) (sym (cong′ (λ x → isPi-alg.!X (x n) P) (fix-eq ProcPi-algF)))))
    where
      d = λ !p → stepL' (Unfold P ∪ synchF (Unfold P) (Unfold P)) (λ α → Fold (!p α))
