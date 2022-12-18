{-# OPTIONS --cubical #-}

open import AbsNames

module ccs.Algebra (ns : Names) where

open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open Names ns
open OpNames ns
open import ccs.Syntax ns

-- The notion of algebra for CCS, i.e. a type family X n with all the
-- operations of CCS.
record isCCS-alg (X : ℕ → Set) (n : ℕ) : Set where
  constructor alg
  field
    endX : X n
    actX : (a : Act n) → (p : X n) → X n
    sumX parX : (p : X n) → (q : X n) → X n
    νX : (p : X (suc n)) → X n
    !X : (p : X n) → X n

module _ {X : ℕ → Set} (X-alg : ∀ n → isCCS-alg X n)  where

  open isCCS-alg

-- Evaluation of CCS-programs into the algebra.
  evalX : ∀ {n} → CCS n → X n
  evalX end = endX (X-alg _)
  evalX (a · p) = actX (X-alg _) a (evalX p)
  evalX (p ⊕ q) = sumX (X-alg _) (evalX p) (evalX q)
  evalX (p ∣∣ q) = parX (X-alg _) (evalX p) (evalX q)
  evalX (ν p) = νX (X-alg _) (evalX p)
  evalX (! p) = !X (X-alg _) (evalX p)

-- The notion of structural congruence for a CCS-algebra. The
-- definition requires the type family X to act on injective
-- renamings.
  module _ (mapX : ∀ {m n} → Inj m n → X m → X n) where
    record StructCong (Eq : {n : ℕ} (P Q : X n) → Set) : Set where
      field
        refl≈X : ∀ {n} {P : X n} → Eq P P
        sym≈X : ∀ {n} {P Q : X n} → Eq P Q → Eq Q P
        _∙≈X_ : ∀ {n} {P Q R : X n} → Eq P Q → Eq Q R → Eq P R
        cong·X : ∀ {n} {P Q : X n} {a : Act n} → Eq P Q → Eq (actX (X-alg _) a P) (actX (X-alg _) a Q)
        cong⊕X : ∀ {n} {P P' Q Q' : X n} → Eq P P' → Eq Q Q' → Eq (sumX (X-alg _) P Q) (sumX (X-alg _) P' Q')
        cong∣∣X : ∀ {n} {P P' Q Q' : X n} → Eq P P' → Eq Q Q' → Eq (parX (X-alg _) P Q) (parX (X-alg _) P' Q')
        congνX : ∀ {n} {P Q : X (suc n)} → Eq P Q → Eq (νX (X-alg _) P) (νX (X-alg _) Q)
        cong!X : ∀ {n} {P Q : X n} → Eq P Q → Eq (!X (X-alg _) P) (!X (X-alg _) Q)
        unit⊕X : ∀ {n} {P : X n} → Eq (sumX (X-alg _) P (endX (X-alg _))) P
        comm⊕X : ∀ {n} {P Q : X n} → Eq (sumX (X-alg _) P Q) (sumX (X-alg _) Q P)
        assoc⊕X : ∀ {n} {P Q R : X n} → Eq (sumX (X-alg _) (sumX (X-alg _) P Q) R) (sumX (X-alg _) P (sumX (X-alg _) Q R))
        unit∣∣X : ∀ {n} {P : X n} → Eq (parX (X-alg _) P (endX (X-alg _))) P
        comm∣∣X : ∀ {n} {P Q : X n} → Eq (parX (X-alg _) P Q) (parX (X-alg _) Q P)
        assoc∣∣X : ∀ {n} {P Q R : X n} → Eq (parX (X-alg _) (parX (X-alg _) P Q) R) (parX (X-alg _) P (parX (X-alg _) Q R))
        replX : ∀ {n} {P : X n} → Eq (!X (X-alg _) P) (parX (X-alg _) P (!X (X-alg _) P))
        ν∣∣X : ∀ {n} {P : X (suc n)} {Q : X n}
          → Eq (νX (X-alg _) (parX (X-alg _) P (mapX (ι , ι-inj) Q))) (parX (X-alg _) (νX (X-alg _) P) Q)
        swapνX : ∀ {n} {P : X (suc (suc n))} → Eq (νX (X-alg _) (νX (X-alg _) P)) (νX (X-alg _) (νX (X-alg _) (mapX (swap , swap-inj) P)))
        νendX : ∀ {n} → Eq (νX (X-alg _) (endX (X-alg _))) (endX (X-alg n))
  
      ≡→Eq : ∀ {n} {P Q : X n} → P ≡ Q → Eq P Q
      ≡→Eq {P = P} eq = subst (Eq P) eq refl≈X

-- The notion of dynamics, or operational semantics, for a
-- CCS-algebra.
  record Dynamics (Eq : {n : ℕ} (P Q : X n) → Set)
                  (Trans : {n : ℕ} (P : X n) (σ : Act n) (Q : X n) → Set)
                  : Set where
    field
      actX : ∀ {n} {P : X n} a
        → Trans (actX (X-alg _) a P) a P
      sumtrX : ∀ {n} {P Q : X n} {P' : X n} {a : Act n}
        → Trans P a P' → Trans (sumX (X-alg _) P Q) a P'
      partrX : ∀ {n} {P Q : X n} {P' : X n} {a : Act n}
        → Trans P a P' → Trans (parX (X-alg _) P Q) a (parX (X-alg _) P' Q)
      comX : ∀ {n} {P Q P' Q' : X n} {a}
        → Trans P (out a) P' → Trans Q (inp a) Q' → Trans (parX (X-alg _) P Q) τ (parX (X-alg _) P' Q')
      resX : ∀ {n} {P P'} {a : Act n}
        → Trans P (mapAct ι a) P' → Trans (νX (X-alg _) P) a (νX (X-alg _) P')
      convX : ∀ {n} {P P' Q Q'} {a : Act n}
        → Trans P a Q → Eq P P' → Eq Q Q' → Trans P' a Q'

-- Notion of CCS model. This is a CCS-algebra X with an action mapX on
-- injective renamings, which is functorial and preserves the CCS
-- operations. It must also have a structural congruence and an
-- operational semantics.
record isCCS-model (X : ℕ → Set) : Set₁ where
  field
    algX : ∀ n → isCCS-alg X n
    
    mapX : ∀ {n m} → Inj n m → X n → X m
    mapX-id : ∀ {n} (P : X n)
      → mapX ((\ x → x) , λ _ _ p → p) P ≡ P
    mapX-∘ : ∀ {m n o} {f : Inj n o} {g : Inj m n} (P : X m)
      → mapX f (mapX g P) ≡
           mapX ((\ x → fst f (fst g x)) , λ _ _ p → snd g _ _ (snd f _ _ p)) P
    map-evalX : ∀ {n m} (f : Inj m n) (p : CCS m)
      → evalX algX (mapCCS (fst f) p) ≡ mapX f (evalX algX p)
           
    EqX : {n : ℕ} (P Q : X n) → Set
    congX : StructCong algX mapX EqX
    
    TransX : {n : ℕ} (P : X n) (σ : Act n) (Q : X n) → Set
    dynX : Dynamics algX EqX TransX
    

  open StructCong congX
  open Dynamics dynX

-- Evaluation of structural congruence rules in a CCS-model.
  evalX≈ : ∀ {n} {P Q : CCS n} → P ≈ Q → EqX (evalX algX P) (evalX algX Q)
  evalX≈ refl≈ = refl≈X
  evalX≈ (sym≈ c) = sym≈X (evalX≈ c)
  evalX≈ (c ∙≈ c₁) = (evalX≈ c) ∙≈X (evalX≈ c₁)
  evalX≈ (cong· c) = cong·X (evalX≈ c)
  evalX≈ (cong⊕ c c₁) = cong⊕X (evalX≈ c) (evalX≈ c₁)
  evalX≈ (cong∣∣ c c₁) = cong∣∣X (evalX≈ c) (evalX≈ c₁)
  evalX≈ (congν c) = congνX (evalX≈ c)
  evalX≈ (cong! c) = cong!X (evalX≈ c)
  evalX≈ unit⊕ = unit⊕X
  evalX≈ comm⊕ = comm⊕X
  evalX≈ assoc⊕ = assoc⊕X
  evalX≈ unit∣∣ = unit∣∣X
  evalX≈ comm∣∣ = comm∣∣X
  evalX≈ assoc∣∣ = assoc∣∣X
  evalX≈ repl = replX
  evalX≈ (ν∣∣ {P} {Q}) =
    transport
      (cong₂ EqX
        (cong (isCCS-alg.νX (algX _))
              (cong (isCCS-alg.parX (algX _) (evalX algX P))
                    (sym (map-evalX (ι , ι-inj) Q))))
        refl)
      ν∣∣X
  evalX≈ (swapν {P}) =
    swapνX
    ∙≈X congνX (congνX (sym≈X (≡→Eq (map-evalX (swap , swap-inj) P))))
  evalX≈ νend = νendX

-- Evaluation of operational semantics rules in a CCS-model.
  evalX↦ : ∀ {n} {P} {a : Act n} {Q : CCS n}
    → P [ a ]↦ Q → TransX (evalX algX P) a (evalX algX Q)
  evalX↦ (act a) = actX a
  evalX↦ (sumtr tr) = sumtrX (evalX↦ tr)
  evalX↦ (partr tr) = partrX (evalX↦ tr)
  evalX↦ (com tr tr₁) = comX (evalX↦ tr) (evalX↦ tr₁)
  evalX↦ (res {P = P} {P'} {a} tr) = resX (evalX↦ tr)
  evalX↦ (conv tr c c₁) = convX (evalX↦ tr) (evalX≈ c) (evalX≈ c₁)

-- Of course the CCS syntax is a CCS-algebra with structural
-- congruence and operational semantics.
module _ where
  open isCCS-alg
  open StructCong
  open Dynamics
  
  InitCCS-alg : ∀ n → isCCS-alg CCS n
  endX (InitCCS-alg n) = end
  actX (InitCCS-alg n) = _·_
  sumX (InitCCS-alg n) = _⊕_
  parX (InitCCS-alg n) = _∣∣_
  νX (InitCCS-alg n) = ν
  !X (InitCCS-alg n) = !_
  
  InitCCS-≈ : StructCong InitCCS-alg (λ f → mapCCS (f .fst)) _≈_
  refl≈X InitCCS-≈ = refl≈
  sym≈X InitCCS-≈ = sym≈
  _∙≈X_ InitCCS-≈ = _∙≈_
  cong·X InitCCS-≈ = cong·
  cong⊕X InitCCS-≈ = cong⊕
  cong∣∣X InitCCS-≈ = cong∣∣
  congνX InitCCS-≈ = congν
  cong!X InitCCS-≈ = cong!
  unit⊕X InitCCS-≈ = unit⊕
  comm⊕X InitCCS-≈ = comm⊕
  assoc⊕X InitCCS-≈ = assoc⊕
  unit∣∣X InitCCS-≈ = unit∣∣
  comm∣∣X InitCCS-≈ = comm∣∣
  assoc∣∣X InitCCS-≈ = assoc∣∣
  replX InitCCS-≈ = repl
  ν∣∣X InitCCS-≈ = ν∣∣
  swapνX InitCCS-≈ = swapν
  νendX InitCCS-≈ = νend
  
  InitCCS-Dyn : Dynamics InitCCS-alg _≈_ _[_]↦_
  actX InitCCS-Dyn = act
  sumtrX InitCCS-Dyn = sumtr
  partrX InitCCS-Dyn = partr
  comX InitCCS-Dyn = com
  resX InitCCS-Dyn = res
  convX InitCCS-Dyn = conv

