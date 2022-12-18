{-# OPTIONS --cubical --guarded #-}

open import Cubical.Data.Sigma
open import Cubical.Data.List as List
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (act)
open import Cubical.HITs.PropositionalTruncation as PT
open import LaterPrims hiding (_∙_)
open import Basic

module BranchingStreams where


-- The type of guarded branching streams as a guarded recursive type.
record S (A : Type) : Type where
  inductive
  constructor _,_
  field
    head : A
    tails : ▹ List (S A)

open S

-- An equivalent definition as a fixpoint in the universe.
S' : Type → Type
S' A = fix (λ X → A × ▸ (λ α → List (X α)))

-- Its action of maps.
mapSF : {A B : Type}
  → ▹ ((A → B) → S A → S B)
  → (A → B) → S A → S B
mapSF mapS' f xs =
  f (xs .head) , λ α → List.map (mapS' α f) (xs .tails α)

mapS : {A B : Type} → (A → B) → S A → S B
mapS = fix mapSF

mapS-eq : {A B : Type} (f : A → B) (xs : S A)
  → mapS f xs ≡ (f (xs .head) , λ α → List.map (mapS f) (xs .tails α))
mapS-eq f xs = fix-eq mapSF <* f <* xs  

-- mapS preserves identities, proved via guarded recursion.
mapL-id : {A : Type}
  → (xs : List A) → List.map (λ x → x) xs ≡ xs
mapL-id [] = refl
mapL-id (x ∷ xs) i = x ∷ mapL-id xs i

mapS-idF : {A : Type}
  → ▹ ((xs : S A) → mapS (λ x → x) xs ≡ xs)
  → (xs : S A) → mapS (λ x → x) xs ≡ xs
mapS-idF ih xs =
  mapS-eq (λ x → x) xs
  ∙ (λ i → xs .head , λ α → List.map (λ ys → ih α ys i) (xs .tails α))
  ∙ (λ i → xs .head , λ α → mapL-id (xs .tails α) i)

mapS-id : {A : Type} (xs : S A) → mapS (λ x → x) xs ≡ xs
mapS-id = fix mapS-idF
