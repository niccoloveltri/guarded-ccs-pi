{-# OPTIONS --cubical #-}

open import AbsNames

-- CCS syntax

module ccs.Syntax (ns : Names) where

open import Cubical.Core.Everything
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Sum hiding (inl; inr) 
open import Cubical.Foundations.Everything hiding (assoc;lift;act)
open import Cubical.Functions.Logic as Logic
open import Cubical.HITs.PropositionalTruncation as PT 
open import Basic
open import CountablePowerSet

open Names ns
open OpNames ns
open import Cubical.Foundations.Function
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma

infixr 12 !_
infix 11 _∣∣_

-- The type of actions. 
data Act (n : ℕ) : Set where
  out : Name n → Act n
  inp : Name n → Act n
  τ  : Act n

-- CCS syntax.
data CCS (n : ℕ) : Set where
  end : CCS n
  _·_ : (a : Act n) → (P : CCS n) → CCS n
  _⊕_ _∣∣_ : (P : CCS n) → (Q : CCS n) → CCS n
  ν : (P : CCS (suc n)) → CCS n
  !_ : (P : CCS n) → CCS n


-- Action of Act on renamings, establishing that Act is a functor (a
-- presheaf on renamings).
mapAct : ∀{n m} → (Name n → Name m) → (a : Act n) → Act m
mapAct f (out a) = out (f a)
mapAct f (inp a) = inp (f a)
mapAct f τ = τ

mapAct-id : ∀{n} (a : Act n) → mapAct (λ x → x) a ≡ a
mapAct-id (out a) = refl
mapAct-id (inp a) = refl
mapAct-id τ = refl

mapmapAct : ∀{n m k} {g : Name m → Name k} {f : Name n → Name m}
  → (a : Act n) → mapAct g (mapAct f a) ≡ mapAct (λ x → g (f x)) a
mapmapAct (out a) = refl
mapmapAct (inp a) = refl
mapmapAct τ = refl

-- Action of CCS on renamings.
mapCCS : ∀ {m n} → (Name m → Name n) → CCS m → CCS n
mapCCS f end = end
mapCCS f (a · P) = mapAct f a · mapCCS f P
mapCCS f (P ⊕ Q) = mapCCS f P ⊕ mapCCS f Q
mapCCS f (P ∣∣ Q) = mapCCS f P ∣∣ mapCCS f Q
mapCCS f (ν P) = ν (mapCCS (lift f) P)
mapCCS f (! P) = ! (mapCCS f P)

mapmapCCS : ∀ {n m o} (f : Name n → Name m) (g : Name o → Name n)
  → ∀ P → mapCCS f (mapCCS g P) ≡ mapCCS (\ x → f (g x)) P
mapmapCCS f g end = refl
mapmapCCS f g (out a · P) = cong (out _ ·_) (mapmapCCS f g P)
mapmapCCS f g (inp a · P) = cong (inp (f (g a)) ·_) (mapmapCCS f g P)
mapmapCCS f g (τ · P) = cong (τ ·_) (mapmapCCS f g P)
mapmapCCS f g (P ⊕ P₁) = cong₂ _⊕_ (mapmapCCS f g P) (mapmapCCS f g P₁)
mapmapCCS f g (P ∣∣ P₁) = cong₂ _∣∣_ (mapmapCCS f g P) (mapmapCCS f g P₁)
mapmapCCS f g (ν P) =
  cong ν (mapmapCCS (lift f) (lift g) P
  ∙ (cong mapCCS (funExt (liftlift f g)) <* P))
mapmapCCS f g (! P) = cong !_ (mapmapCCS f g P)

-- Structural congruence of terms.
infix 10 _≈_
data _≈_ {n : ℕ} : (P Q : CCS n) → Set where
  refl≈ : ∀ {P} → P ≈ P
  sym≈ : ∀ {P Q} → P ≈ Q → Q ≈ P
  _∙≈_ : ∀ {P Q R} → P ≈ Q → Q ≈ R → P ≈ R
  cong· : ∀ {P Q} {a : Act n} → P ≈ Q → a · P ≈ a · Q
  cong⊕ : ∀ {P P' Q Q'} → P ≈ P' → Q ≈ Q' → P ⊕ Q ≈ P' ⊕ Q'
  cong∣∣ : ∀ {P P' Q Q'} → P ≈ P' → Q ≈ Q' → P ∣∣ Q ≈ P' ∣∣ Q'
  congν : ∀ {P Q} → P ≈ Q → ν P ≈ ν Q
  cong! : ∀ {P Q} → P ≈ Q → ! P ≈ ! Q
  unit⊕ : ∀ {P} → P ⊕ end ≈ P
  comm⊕ : ∀ {P Q} → P ⊕ Q ≈ Q ⊕ P
  assoc⊕ : ∀ {P Q R} → (P ⊕ Q) ⊕ R ≈ P ⊕ (Q ⊕ R)
  unit∣∣ : ∀ {P} → P ∣∣ end ≈ P
  comm∣∣ : ∀ {P Q} → P ∣∣ Q ≈ Q ∣∣ P
  assoc∣∣ : ∀ {P Q R} → (P ∣∣ Q) ∣∣ R ≈ P ∣∣ (Q ∣∣ R)
  repl : ∀ {P} → ! P ≈ P ∣∣ ! P
  ν∣∣ : ∀ {P Q} → ν (P ∣∣ mapCCS ι Q) ≈ ν P ∣∣ Q
  swapν : ∀ {P} → ν (ν P) ≈ ν (ν (mapCCS swap P))
  νend : ν end ≈ end

≡→≈ : ∀ {n} {P Q : CCS n} → P ≡ Q → P ≈ Q
≡→≈ {P = P} eq = subst (λ Q → P ≈ Q) eq refl≈

-- Structural congruences is closed under renaming.
map≈ : ∀ {n m} {P Q : CCS n} (f : Name n → Name m) → P ≈ Q → mapCCS f P ≈ mapCCS f Q
map≈ f refl≈ = refl≈
map≈ f (sym≈ tr) = sym≈ (map≈ f tr)
map≈ f (tr ∙≈ tr₁) = map≈ f tr ∙≈ map≈ f tr₁
map≈ f (cong· {a = out a} tr) = cong· (map≈ f tr)
map≈ f (cong· {a = inp a} tr) = cong· (map≈ f tr)
map≈ f (cong· {a = τ} tr) = cong· (map≈ f tr)
map≈ f (cong⊕ tr tr₁) = cong⊕ (map≈ f tr) (map≈ f tr₁)
map≈ f (cong∣∣ tr tr₁) = cong∣∣ (map≈ f tr) (map≈ f tr₁)
map≈ f (congν tr) = congν (map≈ (lift f) tr)
map≈ f (cong! tr) = cong! (map≈ f tr)
map≈ f unit⊕ = unit⊕
map≈ f comm⊕ = comm⊕
map≈ f assoc⊕ = assoc⊕
map≈ f unit∣∣ =  unit∣∣
map≈ f comm∣∣ = comm∣∣
map≈ f assoc∣∣ = assoc∣∣
map≈ f repl = repl
map≈ f (ν∣∣ {Q = Q}) =
  transport (cong _≈_ (cong ν (cong₂ _∣∣_ refl (mapmapCCS _ _ Q ∙ (cong mapCCS (funExt (\ x → sym (lift-ι f x))) <* Q) ∙ sym (mapmapCCS _ _ Q)))) <* _) ν∣∣
map≈ f (swapν {P = P}) =
  swapν ∙≈ congν (congν (≡→≈ (mapmapCCS _ _ _ ∙ sym (mapmapCCS _ _ _ ∙ cong (λ g → mapCCS g P) (funExt (swap-lift f))))))
map≈ f νend = νend

-- CCS operational semantics.
infix 10 _[_]↦_
data _[_]↦_ {n : ℕ} : (P : CCS n) (σ : Act n) (Q : CCS n) → Set where
  act : ∀ {P} (a : Act n) → a · P [ a ]↦ P
  sumtr : ∀ {P Q P'} {a : Act n}
    → P [ a ]↦ P' → P ⊕ Q [ a ]↦ P'
  partr : ∀ {P Q P'} {a : Act n}
    → P [ a ]↦ P' → P ∣∣ Q [ a ]↦ P' ∣∣ Q
  com : ∀ {P Q P' Q'} {a : Name n}
    → P [ out a ]↦ P' → Q [ inp a ]↦ Q'
    → P ∣∣ Q [ τ ]↦ P' ∣∣ Q'
  res : ∀ {P P'} {a : Act n}
    → P [ mapAct ι a ]↦ P' → ν P [ a ]↦ ν P'
  conv : ∀ {P P' Q Q'} {a : Act n}
    → P [ a ]↦ Q → P ≈ P' → Q ≈ Q' → P' [ a ]↦ Q'

-- Reduction is closed under renaming.
map↦ : ∀ {n m} {P} {a : Act n} {Q} (f : Name n → Name m)
  → P [ a ]↦ Q → mapCCS f P [ mapAct f a ]↦ mapCCS f Q
map↦ f (act a) = act (mapAct f a)
map↦ f (sumtr tr) = sumtr (map↦ f tr)
map↦ f (partr tr) = partr (map↦ f tr)
map↦ f (com tr tr₁) = com (map↦ f tr) (map↦ f tr₁)
map↦ f (res tr) = res (subst (λ x → _ [ x ]↦ _) (mapmapAct _ ∙ cong₂ mapAct (funExt (lift-ι f)) refl ∙ sym (mapmapAct _)) (map↦ (lift f) tr))
map↦ f (conv tr x x₁) = conv (map↦ f tr) (map≈ f x) (map≈ f x₁)
