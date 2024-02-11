{-# OPTIONS --cubical --guarded #-}

open import Cubical.Data.Sum hiding (inl; inr) 
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (lift;assoc)
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc)
open import Cubical.Relation.Nullary
open import CountablePowerSet
open import Basic
open import AbsNames
open import LaterPrims hiding (_∙_)

module pi-calculus.semantics.Model (ns : Names) where

open Names ns
open OpNames ns
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import pi-calculus.Syntax ns
open import pi-calculus.Algebra ns
open import pi-calculus.semantics.Algebra ns
open import pi-calculus.semantics.MapProcLemmata ns
open import pi-calculus.semantics.StructuralCongruence ns
open import pi-calculus.semantics.Dynamics ns

-- A different semantic domain. Elements of PiMod are families of
-- processes indexed by renamings, satisfying a naturality condition.
record PiMod (n : ℕ) : Set where
  constructor pimod
  field
    elem : ∀ m (ρ : Name n → Name m) → Proc m
    elem-nat : ∀ {m m'} (f : Inj m m') (ρ : Name n → Name m)
      → mapProc _ _ (fst f) (elem m ρ) ≡ elem m' (\ x → f .fst (ρ x))
              
open PiMod

PiMod-ext : ∀ {n} {x y : PiMod n} → elem x ≡ elem y → x ≡ y
PiMod-ext eq i .elem = eq i
PiMod-ext {x = x} {y} eq i .elem-nat = 
  isOfHLevel→isOfHLevelDep 1
   (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → isSetProc _ _ _)))
   (x .elem-nat) (y .elem-nat)
   eq i

PiMod-eq : ∀ {n} {x y : PiMod n} → (∀ m ρ → elem x m ρ ≡ elem y m ρ) → x ≡ y
PiMod-eq eq = PiMod-ext (\ i m f → eq m f i)

isSetPiMod : ∀ n → isSet (PiMod n)
isSetPiMod n =
  isSetRetract (λ x → x .elem , (\ m m' → x .elem-nat {m} {m'}))
               (λ (p : Σ _ (\ e → ∀ m m' → _)) → pimod (p .fst) (p .snd _ _))
               (λ _ → refl)
               (isSetΣ (isSetΠ λ _ → isSetΠ λ _ → isSetProc _)
                       λ _ → isSetΠ λ _ → isSetΠ λ _ → isSetΠ λ _ → isSetΠ λ _ → isProp→isSet (isSetProc _ _ _) )


mapPiMod : {n m : ℕ} → (Name m → Name n) → PiMod m → PiMod n
mapPiMod f x = record
  { elem = \ m g → x .elem m (\ v → g (f v))
  ; elem-nat = \ i ρ → x .elem-nat i (λ v → ρ (f v)) }


actPiMod : ∀ {n m} → (a : Act n m) → PiMod m → PiMod n
actPiMod (out ch x) p .elem m g = Fold (η (`out (g ch) (g x) (\ _ → p .elem m g)))
actPiMod (out ch x) p .elem-nat f ρ = (cong Fold (mapProc'-eq' _ _ _ _ ∙ cong η (StepPath refl refl (later-ext \ α → p .elem-nat f _) )))
actPiMod (inp ch) p .elem m g = Fold ((bind enum \ v → η ((`inp (g ch) v \ α → p .elem _ (snoc g v))))
                                                        ∪ (η (`binp (g ch) \ α → p .elem _ (lift g))))
actPiMod (inp ch) p .elem-nat f ρ = cong Fold (mapProc'-eq' _ _ _ _ ∙  cong₂ _∪_ refl (comm _ _) ∙ assoc _ _ _
           ∙ cong₂ _∪_ (cong₂ _∪_ (bind-bind enum _ _ ∙ cong (bind enum) (funExt \ v → cong η (StepPath refl refl (later-ext \ α → p .elem-nat f (snoc ρ v)
                              ∙ cong (p .elem _) (funExt (f-snoc (fst f)))))) ∙ sym
                       (bind-map enum (\ v → η (`inp (fst f (ρ ch)) v (\ α → p .elem _ (snoc (\ x → fst f (ρ x)) v)))) (fst f)))
                       (inps'-eq (λ _ → mapProc') _ _ _ ∙ (cong-bind (neg (image (fst f)) (image-fn _)) (\ v v∈ → cong η (StepPath refl refl (later-ext \ _ →
                         p .elem-nat (_ , snoc-inj f v v∈) _ ∙ cong (p .elem _) (funExt \ x → snoc-lift _ _ _ x) )))))
                       ∙ cong₂ bind (neg-∪ {x = (image (fst f))}) refl)
                   (cong η (StepPath refl refl (later-ext \ α → p .elem-nat (_ , lift-inj f) _ ∙ cong (p .elem _) (funExt (liftlift _ _))))) )
actPiMod τ p .elem m g = Fold (η (`τ (\ _ → p .elem m g)))
actPiMod τ p .elem-nat f ρ = cong Fold (mapProc'-eq' _ _ _ _ ∙ cong η (StepPath refl refl (later-ext \ α → p .elem-nat f _)))

-- We give names to the other Pi operations in PiMod.
endPiMod : ∀ {n} → PiMod n
endPiMod .elem m g = endProc
endPiMod .elem-nat f _ = end-map (fst f)

sumPiMod : ∀ {n} → PiMod n → PiMod n → PiMod n
sumPiMod p q .elem m x = sumProc (p .elem m x) (q .elem m x)
sumPiMod p q .elem-nat f ρ = sum-map (fst f) _ _ ∙ cong₂ sumProc (p .elem-nat f ρ) (q .elem-nat f ρ)

parPiMod : ∀ {n} → PiMod n → PiMod n → PiMod n
parPiMod p q .elem m x = parProc (p .elem m x) (q .elem m x)
parPiMod p q .elem-nat f ρ = par-map _ _ f _ _ ∙ cong₂ parProc (p .elem-nat f ρ) (q .elem-nat f ρ)

νPiMod : ∀ {n} → PiMod (suc n) → PiMod n
νPiMod p .elem m x = νProc (p .elem (suc m) (lift x))
νPiMod p .elem-nat f ρ =
  ν-map _ _ f _ ∙ cong νProc (p .elem-nat (_ , lift-inj f) _ ∙ cong (p .elem (suc _)) (funExt (liftlift (fst f) ρ)))

!PiMod : ∀ {n} → PiMod n → PiMod n
!PiMod p .elem m x = !Proc (p .elem _ x)
!PiMod p .elem-nat f ρ = rep-map f (p .elem _ ρ) ∙ cong !Proc (p .elem-nat f ρ)

guardPiMod : ∀ {n} (x y : Name n) → PiMod n → PiMod n
guardPiMod a b p .elem m g = guardProc (g a) (g b) (p .elem m g)
guardPiMod a b p .elem-nat f ρ = guard-map f (ρ a) (ρ b) (p. elem _ ρ) ∙ congS (guardProc _ _) (p .elem-nat f ρ)

PiMod-alg : ∀ n → isPi-alg PiMod n
PiMod-alg n = record
  { endX   = endPiMod
  ; actX   = actPiMod
  ; sumX   = sumPiMod
  ; parX   = parPiMod
  ; νX     = νPiMod
  ; guardX = guardPiMod
  ; !X     = !PiMod
  }


open StructCong 

PiModStructCong : StructCong PiMod-alg mapPiMod _≡_
PiModStructCong = record
  { refl≈X = refl
  ; sym≈X = sym
  ; _∙≈X_ = _∙_
  ; cong·X = λ {_}{_}{_}{_}{a} → cong (actPiMod a)
  ; cong⊕X = λ eq eq' → cong₂ sumPiMod eq eq'
  ; cong∣∣X = λ eq eq' → cong₂ parPiMod eq eq'
  ; congνX = cong νPiMod
  ; congguardX = λ {_}{x}{y} → cong (guardPiMod x y)
  ; cong!X = cong !PiMod
  ; unit⊕X = PiMod-eq λ _ _ → unit⊕X ProcStructCong
  ; comm⊕X = PiMod-eq λ _ _ → comm⊕X ProcStructCong
  ; assoc⊕X = PiMod-eq λ _ _ → assoc⊕X ProcStructCong
  ; unit∣∣X = PiMod-eq λ _ _ → unit∣∣X ProcStructCong
  ; comm∣∣X = λ {_}{P} →
      PiMod-eq λ m f → comm∣∣X ProcStructCong {P = P .elem m f}
  ; assoc∣∣X = λ {_}{P} →
      PiMod-eq λ m f → assoc∣∣X ProcStructCong {P = P .elem m f}
  ; replX = λ {_}{P} →
      PiMod-eq λ m f → replX ProcStructCong {P = P .elem m f}
  ; guardreflX = PiMod-eq λ _ _ → guardreflX ProcStructCong
  ; ν∣∣X = λ {_}{_}{Q} → PiMod-eq λ _ f →
      cong νProc (cong₂ parProc refl
                                (cong (Q .elem _) (funExt (lift-ι f))
                                                  ∙ sym (Q .elem-nat (ι , ι-inj) f)))
                  ∙ ν∣∣X ProcStructCong 
  ; swapνX = λ {_}{P} → PiMod-eq λ _ f →
      swapνX ProcStructCong
      ∙ cong νProc (cong νProc
          (P .elem-nat (_ , swap-inj) (lift (lift f))
          ∙ sym (cong (P .elem _) (funExt (swap-lift f)))))
  ; νendX = PiMod-eq λ _ _ → νendX ProcStructCong
  }

_[_]~>_ : ∀ {n m} → PiMod n → Label n m → PiMod m → Set
p [ a ]~> q = ∀ m' (ρ : Name _ → Name m')
  → (mapLabel ρ a , next (q .elem (labelN a m') (labelRen a _ ρ))) ← (p .elem m' ρ)

subst← : ∀ {n} (P : Proc n) {Q Q' : _} → Q ≡ Q' →  Q' ← P   →   Q ← P
subst← P eq = subst (_← P) (sym eq)

map~> : ∀ {n m o} (f : Name n → Name o)
  → ∀ p (a : Label n m) q → p [ a ]~> q
  → mapPiMod f p [ mapLabel f a ]~> mapPiMod (labelRen a _ f) q
map~> f p (out x x₁) q paq m' ρ = paq _ (\ x → ρ (f x))
map~> f p (bout x) q paq m' ρ =
  subst← (p .elem m' (λ v → ρ (f v)))
          (StepPath refl refl (cong next (cong (q .elem _) (funExt (liftlift ρ f)))))
          (paq _ (\ x → ρ (f x)))
map~> f p (inp x x₁) q paq m' ρ = paq _ (\ x → ρ (f x))
map~> f p (binp x) q paq m' ρ =
  subst← (p .elem m' (λ v → ρ (f v)))
         (StepPath refl refl (cong next (cong (q .elem _) (funExt (liftlift ρ f)))))
         (paq _ (\ x → ρ (f x)))
map~> f p τ q paq m' ρ = paq _ (\ x → ρ (f x))

open Dynamics

PiModDynamics : Dynamics PiMod-alg mapPiMod _≡_ _[_]~>_
PiModDynamics .outX ch v m' ρ = ∣ refl ∣₁
PiModDynamics .inpX {P = P} ch v m' ρ =
  ∣ _⊎_.inl (bind-in _ _ enum (_ , enum-in (ρ v) , ∣ StepPath refl refl (cong next (cong (P .elem _) (funExt \ v' → cong ρ (snoc-for-fresh v v') ∙ f-snoc ρ v'))) ∣₁)) ∣₁
PiModDynamics .τX m' ρ = ∣ refl ∣₁
PiModDynamics .sumtrX {P = P}{Q} x m' ρ = sumtrX ProcDynamics {P = P .elem m' ρ}{Q .elem m' ρ} (x m' ρ)
PiModDynamics .partrX {P = P} {Q} {P'} {a = a} x m' ρ =
  subst← (parProc (P .elem m' ρ) (Q .elem m' ρ))
          (StepPath refl refl (later-ext \ α → cong₂ parProc refl (cong (Q .elem _) (funExt (\ v → labelRenInj ρ a)) ∙
                                        sym (Q .elem-nat (labelInj (mapLabel _ a)) _) )))
          (partrX ProcDynamics {P = P .elem m' ρ}{Q .elem m' ρ} (x m' ρ))
PiModDynamics .comX {P = P}{Q} x x₁ m' ρ = comX ProcDynamics {P = P .elem m' ρ}{Q .elem m' ρ} (x m' ρ) (x₁ m' ρ)
PiModDynamics .closeX {P = P}{Q} x x₁ m' ρ = closeX ProcDynamics {P = P .elem m' ρ}{Q .elem m' ρ} (x m' (labelRen τ m' ρ)) (x₁ m' (λ v → labelRen τ m' ρ v))
PiModDynamics .resX {P = P} {a = out x₁ x₂} x m' ρ =
  resX ProcDynamics {P = P .elem (suc m') (lift ρ)}
       (subst← (P .elem (suc m') (lift ρ))
                (StepPath refl (cong₂ out (sym (lift-ι _ _)) (sym (lift-ι _ _))) refl)
                (x (suc m') (lift ρ)))
PiModDynamics .resX {P = P} {P' = P'} {a = bout x₁} x m' ρ =
  subst← (νProc (P .elem (suc m') (lift ρ)))
          (StepPath refl refl (cong next (cong νProc (sym (P' .elem-nat (_ , swap-inj) _ ∙ cong (P' .elem _) (sym (funExt (swap-lift ρ))))))))
          (resX ProcDynamics {P = P .elem (suc m') (lift ρ)}
                (subst← (P .elem (suc m') (lift ρ))
                         (StepPath refl (cong bout (sym (lift-ι _ _))) refl)
                         (x (suc m') (lift ρ))))
PiModDynamics .resX {P = P} {a = inp x₁ x₂} x m' ρ =
  resX ProcDynamics {P = P .elem (suc m') (lift ρ)}
       (subst← (P .elem (suc m') (lift ρ))
                (StepPath refl (cong₂ inp (sym (lift-ι _ _)) (sym (lift-ι _ _))) refl)
                (x (suc m') (lift ρ)))
PiModDynamics .resX {P = P} {P' = P'} {a = binp ch} x m' ρ
  = subst← (νProc (P .elem (suc m') (lift ρ)))
           (StepPath refl refl (cong next (cong νProc (sym (P' .elem-nat (_ , swap-inj) _ ∙ cong (P' .elem _) (sym (funExt (swap-lift ρ))))))))
           (resX ProcDynamics {P = P .elem (suc m') (lift ρ)}
                 (subst← (P .elem (suc m') (lift ρ))
                          (StepPath refl (cong binp (sym (lift-ι _ _))) refl)
                          (x (suc m') (lift ρ))))
PiModDynamics .resX {P = P} {a = τ} x m' ρ = resX ProcDynamics {P = P .elem (suc m') (lift ρ)} (x _ _)
PiModDynamics .opnX {P = P} x m' ρ = 
  opnX ProcDynamics {P = P .elem (suc m') (lift ρ)}
       (subst← (P .elem (suc m') (lift ρ))
               (StepPath refl (cong₂ out (sym (lift-ι ρ _)) (sym (lift-fresh ρ))) refl)
               (x (suc m') (lift ρ)))
PiModDynamics .convX {a = a} P~>Q eqP eqQ  = transport (\ i → eqP i [ a ]~> eqQ i) P~>Q
PiModDynamics .binpX ch m' ρ = ∣ _⊎_.inr (0 , ∣ refl ∣₁) ∣₁

open isPi-model

mapPiMod-eval : ∀ {n m} (f : Name m → Name n) (p : Pi m) m' g
  → evalX PiMod-alg (mapPi f p) .elem m' g
      ≡ evalX PiMod-alg p .elem m' (λ v → g (f v))
mapPiMod-eval f end m' g = refl
mapPiMod-eval f (out ch x · p) m' g =
  cong Fold (cong η (StepPath refl refl (later-ext \ α → mapPiMod-eval f p m' g)))
mapPiMod-eval f (inp ch · p) m' g =
  cong Fold (cong₂ _∪_ (congS (bind enum) (funExt \ v → cong η (StepPath refl refl (later-ext
    \ α → mapPiMod-eval (lift f) p _ _ ∙ cong (evalX PiMod-alg p .elem _) ((funExt \ v' → cong (snoc g v) (lift-snoc _ _)
                                                                          ∙ f-snoc (snoc _ _) _ ∙ cong (\ f → f v') (cong₂ snoc (funExt \ v' → snoc-ι _ _ _)
                                                                           (snoc-fresh _ _))))))))
    (cong η (StepPath refl refl (later-ext \ α → mapPiMod-eval (lift f) p _ _ ∙ cong (evalX PiMod-alg p .elem _) (funExt (liftlift _ _))))))
mapPiMod-eval f (τ · p) m' g = cong Fold (cong η (StepPath refl refl (later-ext \ α → mapPiMod-eval f p m' g)))
mapPiMod-eval f (p ⊕ q) m' g = cong₂ sumProc (mapPiMod-eval f p _ _) (mapPiMod-eval f q _ _)
mapPiMod-eval f (p ∣∣ q) m' g = cong₂ parProc (mapPiMod-eval f p _ _) (mapPiMod-eval f q _ _)
mapPiMod-eval f (ν p) m' g = cong νProc (mapPiMod-eval (lift f) p _ _ ∙ cong₂ (evalX PiMod-alg p .elem) refl (funExt (liftlift _ _)) )
mapPiMod-eval f (guard x y p) m' g = cong (guardProc _ _) (mapPiMod-eval f p _ _)
mapPiMod-eval f (! p) m' g = cong !Proc (mapPiMod-eval f p _ _)

PiMod-model : isPi-model PiMod
PiMod-model .algX = PiMod-alg
PiMod-model .mapX = mapPiMod
PiMod-model .EqX = _≡_
PiMod-model .congX = PiModStructCong
PiMod-model .TransX p a q = p [ a ]~> q
PiMod-model .dynX = PiModDynamics
PiMod-model .mapX-id P = refl
PiMod-model .mapX-∘ P = refl
PiMod-model .map-evalX f p = PiMod-eq (mapPiMod-eval f p)

