{-# OPTIONS --cubical #-}

module Basic where

--open import Agda.Primitive using (lzero)
open import Cubical.Core.Everything
open import Cubical.HITs.PropositionalTruncation as PT 
open import Cubical.Foundations.Everything hiding (assoc)
--open import Cubical.Functions.Logic using (⊥;_≡ₚ_;⇔toPath;inl;inr)
open import Cubical.Data.Nat
open import Cubical.Data.Empty 
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (inl; inr) renaming (elim to elim-⊎)
open import Cubical.Data.List

-- Some utilities

hProp₀ = hProp ℓ-zero

split-nat : ∀ {ℓ} {P : ℕ → Set ℓ} → P zero → (∀ n → P (suc n)) → ∀ n → P n
split-nat z s zero = z
split-nat z s (suc n) = s n

isProp→PathP' : ∀ {l lp} {X : Set l} {B : X → Set lp} → (∀ x → isProp (B x))
                → ∀ {x0 x1} → (eq : x0 ≡ x1) → ∀ b0 b1 → PathP (\ i → B (eq i)) b0 b1
isProp→PathP' pP eq = isProp→PathP (\ i → pP (eq i))

hLevelPi = isOfHLevelΠ 

propPi = isPropΠ

abstract
  _>>⊥_ : ∀ {A : Set} → ∥ A ∥₁ → (A → ⊥) → ⊥
  _>>⊥_ m f = PT.rec (\ ()) f m

abstract
  _>>PT_ : ∀ {A : Set} {B : Set} → ∥ A ∥₁ → (A → ∥ B ∥₁) → ∥ B ∥₁
  _>>PT_ m f = PT.rec squash₁ f m

_<*_ : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
  → f ≡ g → (x : A) → f x ≡ g x
p <* x = \ i → p i x

infixl 20 _<*_

ifunExt : ∀ {a b} {A : Set a} {B : A → Set b} {f g : {x : A} → B x} → ((x : A) → f {x} ≡ g {x}) → (\ {x} → f {x}) ≡ g
ifunExt p i {x} = p x i

_↔_ : (A B : Set) → Set
A ↔ B = (A → B) × (B → A)

Π= : ∀ {A : Set} → {P Q : A → Set} → (∀ x → P x ≡ Q x) → ((x : A) → P x) ≡ ((x : A) → Q x)
Π= {A} f i = (x : A) → f x i

iΠ= : ∀ {A : Set} → {P Q : A → Set} → (∀ x → P x ≡ Q x) → ({x : A} → P x) ≡ ({x : A} → Q x)
iΠ= {A} f i = {x : A} → f x i

¬≡suc : (n : ℕ) → n ≡ suc n → ⊥
¬≡suc zero p = znots p
¬≡suc (suc n) p = ¬≡suc n (injSuc p)
