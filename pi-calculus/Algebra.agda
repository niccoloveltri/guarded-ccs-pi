{-# OPTIONS --cubical #-}

open import AbsNames

module pi-calculus.Algebra (ns : Names) where

open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open Names ns
open OpNames ns
open import pi-calculus.Syntax ns

-- The notion of algebra for the π-calculus, i.e. a type family X n
-- with all the operations of Pi.
record isPi-alg (X : ℕ → Set) (n : ℕ) : Set where
  constructor alg
  field
    endX : X n
    actX : ∀ {m} → (a : Act n m) → (p : X m) → X n
    sumX parX : (p : X n) → (q : X n) → X n
    νX : (p : X (suc n)) → X n
    guardX : Name n → Name n → X n → X n
    !X : (p : X n) → X n

module _ {X : ℕ → Set} (X-alg : ∀ n → isPi-alg X n)  where

  open isPi-alg

-- Evaluation of Pi-programs into the algebra.
  evalX : ∀ {n} → Pi n → X n
  evalX end = endX (X-alg _)
  evalX (a · p) = actX (X-alg _) a (evalX p)
  evalX (p ⊕ q) = sumX (X-alg _) (evalX p) (evalX q)
  evalX (p ∣∣ q) = parX (X-alg _) (evalX p) (evalX q)
  evalX (ν p) = νX (X-alg _) (evalX p)
  evalX (guard x y p) = guardX (X-alg _) x y (evalX p)
  evalX (! p) = !X (X-alg _) (evalX p)

-- The notion of structural congruence for a Pi-algebra. The
-- definition requires the type family X to act on renamings.
  module _ (mapX : ∀ {m n} → (Name m → Name n) → X m → X n) where
  
    record StructCong (Eq : {n : ℕ} (P Q : X n) → Set) : Set where
      field
        refl≈X : ∀ {n} {P : X n} → Eq P P
        sym≈X : ∀ {n} {P Q : X n} → Eq P Q → Eq Q P
        _∙≈X_ : ∀ {n} {P Q R : X n} → Eq P Q → Eq Q R → Eq P R
        cong·X : ∀ {n m} {P Q : X m} {a : Act n m} → Eq P Q
          → Eq (actX (X-alg _) a P) (actX (X-alg _) a Q)
        cong⊕X : ∀ {n} {P P' Q Q' : X n} → Eq P P' → Eq Q Q'
          → Eq (sumX (X-alg _) P Q) (sumX (X-alg _) P' Q')
        cong∣∣X : ∀ {n} {P P' Q Q' : X n} → Eq P P' → Eq Q Q'
          → Eq (parX (X-alg _) P Q) (parX (X-alg _) P' Q')
        congνX : ∀ {n} {P Q : X (suc n)} → Eq P Q
          → Eq (νX (X-alg _) P) (νX (X-alg _) Q)
        congguardX : ∀ {n x y} {P Q : X n} → Eq P Q
          → Eq (guardX (X-alg _) x y P) (guardX (X-alg _) x y Q)
        cong!X : ∀ {n} {P Q : X n} → Eq P Q
          → Eq (!X (X-alg _) P) (!X (X-alg _) Q)
        unit⊕X : ∀ {n} {P : X n} → Eq (sumX (X-alg _) P (endX (X-alg _))) P
        comm⊕X : ∀ {n} {P Q : X n} → Eq (sumX (X-alg _) P Q) (sumX (X-alg _) Q P)
        assoc⊕X : ∀ {n} {P Q R : X n}
          → Eq (sumX (X-alg _) (sumX (X-alg _) P Q) R) (sumX (X-alg _) P (sumX (X-alg _) Q R))
        unit∣∣X : ∀ {n} {P : X n} → Eq (parX (X-alg _) P (endX (X-alg _))) P
        comm∣∣X : ∀ {n} {P Q : X n} → Eq (parX (X-alg _) P Q) (parX (X-alg _) Q P)
        assoc∣∣X : ∀ {n} {P Q R : X n}
          → Eq (parX (X-alg _) (parX (X-alg _) P Q) R) (parX (X-alg _) P (parX (X-alg _) Q R))
        replX : ∀ {n} {P : X n} → Eq (!X (X-alg _) P) (parX (X-alg _) P (!X (X-alg _) P))
        guardreflX : ∀ {n x} {P : X n} → Eq (guardX (X-alg _) x x P) P
        ν∣∣X : ∀ {n} {P : X (suc n)} {Q : X n}
          → Eq (νX (X-alg _) (parX (X-alg _) P (mapX ι Q))) (parX (X-alg _) (νX (X-alg _) P) Q)
        swapνX : ∀ {n} {P : X (suc (suc n))}
          → Eq (νX (X-alg _) (νX (X-alg _) P)) (νX (X-alg _) (νX (X-alg _) (mapX swap P)))
        νendX : ∀ {n} → Eq (νX (X-alg _) (endX (X-alg _))) (endX (X-alg n))

      ≡→Eq : ∀ {n} {P Q : X n} → P ≡ Q → Eq P Q
      ≡→Eq {P = P} eq = subst (Eq P) eq refl≈X
  
-- The notion of dynamics, or operational semantics, for a
-- Pi-algebra.

    swap?X : ∀ {n m} → Label n m → X (suc m) → X (suc m)
    swap?X (out ch z) P = P
    swap?X (bout ch) P = mapX swap P
    swap?X (inp ch z) P = P
    swap?X (binp ch) P = mapX swap P
    swap?X τ P = P

    record Dynamics (Eq : {n : ℕ} (P Q : X n) → Set) (Trans : {n m : ℕ} (P : X n) (σ : Label n m) (Q : X m) → Set) : Set where
      field
        outX : ∀ {n} {P : X n} ch v
          → Trans (actX (X-alg _) (out ch v) P) (out ch v) P
        inpX : ∀ {n} {P : X (suc n)} ch v
          → Trans (actX (X-alg _) (inp ch) P) (inp ch v) (mapX (for-fresh v) P)
        binpX : ∀ {n} {P : X (suc n)} ch
           → Trans (actX (X-alg _) (inp ch) P) (binp ch) P
        τX : ∀ {n} {P : X n} → Trans (actX (X-alg _) τ P) τ P
        sumtrX : ∀ {n m} {P Q : X n} {P' : X m} {a : Label n m}
          → Trans P a P' → Trans (sumX (X-alg _) P Q) a P'
        partrX : ∀ {n m} {P Q : X n} {P' : X m} {a : Label n m}
          → Trans P a P'
          → Trans (parX (X-alg _) P Q) a (parX (X-alg _) P' (mapX (labelInj a .fst) Q))
        comX : ∀ {n} {P Q P' Q' : X n} {ch v}
          → Trans P (out ch v) P' → Trans Q (inp ch v) Q'
          → Trans (parX (X-alg _) P Q) τ (parX (X-alg _) P' Q')
        closeX : ∀ {n} {P Q : X n} {P' Q' : X (suc n)} {ch}
          → Trans P (bout ch) P' → Trans Q (binp ch) Q'
          → Trans (parX (X-alg _) P Q) τ (νX (X-alg _) (parX (X-alg _) P' Q'))
        resX : ∀ {n m} {P P'} {a : Label n m}
          → Trans P (mapLabelι a) P' → Trans (νX (X-alg _) P) a (νX (X-alg _) (swap?X a P'))
        opnX : ∀ {n} {P P'} {ch : Name n}
          → Trans P (out (ι ch) (fresh n)) P' → Trans (νX (X-alg _) P) (bout ch) P'
        convX : ∀ {n m} {P P' Q Q'} {a : Label n m}
          → Trans P a Q → Eq P P' → Eq Q Q' → Trans P' a Q'

-- Notion of Pi-model. This is a Pi-algebra X with an action mapX on
-- renamings, which is functorial and preserves the Pi operations. It
-- must also have a structural congruence and an operational
-- semantics.

record isPi-model (X : ℕ → Set) : Set₁ where
  field
    algX : ∀ n → isPi-alg X n
    mapX : ∀ {n m} → (Name m → Name n) → X m → X n
    EqX : {n : ℕ} (P Q : X n) → Set
    congX : StructCong algX mapX EqX
    TransX : {n m : ℕ} (P : X n) (σ : Label n m) (Q : X m) → Set
    dynX : Dynamics algX mapX EqX TransX
    mapX-id : ∀ {n} (P : X n) → mapX (\ x → x) P ≡ P
    mapX-∘ : ∀ {m n o} {f : _ → Name o} {g : _ → Name n} (P : X m)
      → mapX f (mapX g P) ≡ mapX (\ x → f (g x)) P
    map-evalX : ∀ {n m} (f : Name m → Name n) (p : Pi m)
      → evalX algX (mapPi f p) ≡ mapX f (evalX algX p)

  open StructCong congX
  open Dynamics dynX

-- Evaluation of structural congruence rules in a Pi-model.
  evalX≈ : ∀ {n} {P Q : Pi n} → P ≈ Q → EqX (evalX algX P) (evalX algX Q)
  evalX≈ refl≈ = refl≈X
  evalX≈ (sym≈ c) = sym≈X (evalX≈ c)
  evalX≈ (c ∙≈ c₁) = (evalX≈ c) ∙≈X (evalX≈ c₁)
  evalX≈ (cong· c) = cong·X (evalX≈ c)
  evalX≈ (cong⊕ c c₁) = cong⊕X (evalX≈ c) (evalX≈ c₁)
  evalX≈ (cong∣∣ c c₁) = cong∣∣X (evalX≈ c) (evalX≈ c₁)
  evalX≈ (congν c) = congνX (evalX≈ c)
  evalX≈ (congguard c) = congguardX (evalX≈ c)
  evalX≈ (cong! c) = cong!X (evalX≈ c)
  evalX≈ unit⊕ = unit⊕X
  evalX≈ comm⊕ = comm⊕X
  evalX≈ assoc⊕ = assoc⊕X
  evalX≈ unit∣∣ = unit∣∣X
  evalX≈ comm∣∣ = comm∣∣X
  evalX≈ assoc∣∣ = assoc∣∣X
  evalX≈ repl = replX
  evalX≈ guardrefl = guardreflX
  evalX≈ (ν∣∣ {P} {Q}) =
    transport (cong₂ EqX (cong (isPi-alg.νX (algX _)) (cong (isPi-alg.parX (algX _) (evalX algX P)) (sym (map-evalX ι Q)))) refl) ν∣∣X
  evalX≈ (swapν {P}) = swapνX ∙≈X congνX (congνX (sym≈X (≡→Eq (map-evalX swap P))))
  evalX≈ νend = νendX

-- Evaluation of operational semantics rules in a Pi-model.
  evalX↦ : ∀ {n m} {P} {a : Label n m} {Q : Pi m}
    → P [ a ]↦ Q → TransX (evalX algX P) a (evalX algX Q)
  evalX↦ (out ch v) = outX ch v
  evalX↦ (inp {_} {P} ch v) =
    transport (cong (TransX _ _) (sym (map-evalX (for-fresh v) P))) (inpX ch v)
  evalX↦ (binp ch) = binpX ch
  evalX↦ τ = τX
  evalX↦ (sumtr tr) = sumtrX (evalX↦ tr)
  evalX↦ (partr {Q = Q} tr) =
    transport (cong (TransX _ _) (cong₂ (isPi-alg.parX (algX _)) refl (sym (map-evalX _ Q))))
              (partrX (evalX↦ tr))
  evalX↦ (com tr tr₁) = comX (evalX↦ tr) (evalX↦ tr₁)
  evalX↦ (close tr tr₁) = closeX (evalX↦ tr) (evalX↦ tr₁)
  evalX↦ (res {P = P} {P'} {a} tr) =
    transport (cong (TransX _ _) (cong (isPi-alg.νX (algX _)) (lemma a))) (resX (evalX↦ tr))
    where
      lemma : ∀ {n m P'} (a : Label n m)
        → swap?X algX mapX a (evalX algX P') ≡ evalX algX (swap? a P')
      lemma (out x x₁) = refl
      lemma {P' = P'} (bout x) = sym (map-evalX swap P')
      lemma (inp x x₁) = refl
      lemma {P' = P'} (binp x) = sym (map-evalX swap P')
      lemma τ = refl
  evalX↦ (opn tr) = opnX (evalX↦ tr)
  evalX↦ (conv tr c c₁) = convX (evalX↦ tr) (evalX≈ c) (evalX≈ c₁)

-- Of course the Pi syntax is a Pi-algebra with structural
-- congruence and operational semantics.
module _ where
  open isPi-alg
  open StructCong
  open Dynamics

  InitPi-alg : ∀ n → isPi-alg Pi n
  isPi-alg.endX (InitPi-alg n) = end
  isPi-alg.actX (InitPi-alg n) = _·_
  isPi-alg.sumX (InitPi-alg n) = _⊕_
  isPi-alg.parX (InitPi-alg n) = _∣∣_
  isPi-alg.νX (InitPi-alg n) = ν
  isPi-alg.guardX (InitPi-alg n) = guard
  isPi-alg.!X (InitPi-alg n) = !_
  
  InitPi-≈ : StructCong InitPi-alg mapPi _≈_
  StructCong.refl≈X InitPi-≈ = refl≈
  StructCong.sym≈X InitPi-≈ = sym≈
  StructCong._∙≈X_ InitPi-≈ = _∙≈_
  StructCong.cong·X InitPi-≈ = cong·
  StructCong.cong⊕X InitPi-≈ = cong⊕
  StructCong.cong∣∣X InitPi-≈ = cong∣∣
  StructCong.congνX InitPi-≈ = congν
  StructCong.congguardX InitPi-≈ = congguard
  StructCong.cong!X InitPi-≈ = cong!
  StructCong.unit⊕X InitPi-≈ = unit⊕
  StructCong.comm⊕X InitPi-≈ = comm⊕
  StructCong.assoc⊕X InitPi-≈ = assoc⊕
  StructCong.unit∣∣X InitPi-≈ = unit∣∣
  StructCong.comm∣∣X InitPi-≈ = comm∣∣
  StructCong.assoc∣∣X InitPi-≈ = assoc∣∣
  StructCong.replX InitPi-≈ = repl
  StructCong.guardreflX InitPi-≈ = guardrefl
  StructCong.ν∣∣X InitPi-≈ = ν∣∣
  StructCong.swapνX InitPi-≈ = swapν
  StructCong.νendX InitPi-≈ = νend
  
  InitPi-Dyn : Dynamics InitPi-alg mapPi _≈_ _[_]↦_
  Dynamics.outX InitPi-Dyn = out
  Dynamics.inpX InitPi-Dyn = inp
  Dynamics.binpX InitPi-Dyn = binp
  Dynamics.τX InitPi-Dyn = τ
  Dynamics.sumtrX InitPi-Dyn = sumtr
  Dynamics.partrX InitPi-Dyn = partr
  Dynamics.comX InitPi-Dyn = com
  Dynamics.closeX InitPi-Dyn = close
  Dynamics.resX InitPi-Dyn {a = out x₁ x₂} x = res x
  Dynamics.resX InitPi-Dyn {a = bout x₁} x = res x
  Dynamics.resX InitPi-Dyn {a = inp x₁ x₂} x = res x
  Dynamics.resX InitPi-Dyn {a = binp x₁} x = res x
  Dynamics.resX InitPi-Dyn {a = τ} x = res x
  Dynamics.opnX InitPi-Dyn = opn
  Dynamics.convX InitPi-Dyn = conv
