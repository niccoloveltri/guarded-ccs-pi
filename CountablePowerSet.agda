{-# OPTIONS --cubical #-}

module CountablePowerSet where

open import Cubical.Core.Everything
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.List as List
open import Cubical.Data.Sum as ⊎ hiding (inl; inr)
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.Functions.Logic as Logic
open import Cubical.HITs.PropositionalTruncation as PT 
open import Basic

-- An equivalent representation of the type ℕ → A, where head and the
-- tail are specified.
record Seq {l} (A : Set l) : Set l where
  constructor cons
  field
    hd : A
    tail : (ℕ → A)

apply : ∀ {l} {A : Set l} → Seq A → ℕ → A
apply (cons x y) zero = x
apply (cons x y) (suc n) = y n

seq : ∀ {l} {A : Set l} → (ℕ → A) → Seq A
seq f = cons (f zero) (λ n → f (suc n))

-- The countable powerset as a HIT.
data P∞ {l} (A : Set l) : Set l
_∪_ : ∀ {l} {A : Set l} → P∞ A → P∞ A → P∞ A

data P∞ {l} A where
  ø     : P∞ A
  η     : A → P∞ A
  sup   : (s : Seq (P∞ A)) → P∞ A
  comm  : ∀ x y → x ∪ y ≡ y ∪ x
  assoc : ∀ x y z → x ∪ (y ∪ z) ≡ (x ∪ y) ∪ z
  idem  : ∀ x → x ∪ x ≡ x
  unit  : ∀ x → x ∪ ø ≡ x
  bound : ∀ s n → apply s n ∪ (sup s) ≡ sup s
  dist  : ∀ s x → sup s ∪ x ≡ sup (seq \ n → apply s n ∪ x)
  trunc : isSet (P∞ A)

x ∪ y = sup (cons x (\ _ → y))

-- The induction principle of the countable powerset, where the
-- targeting type family P is propositional, i.e. P s is a
-- proposition, for all s : P∞ A.
module _ {A : Set} (P : P∞ A → hProp₀) (pø : ⟨ P ø ⟩) (pη : ∀ a → ⟨ P (η a) ⟩)
         (psup : ∀ s → (∀ n → ⟨ P (apply s n) ⟩) → ⟨ P (sup s) ⟩) where
 mutual
  IndP∞ : ∀ x → ⟨ P x ⟩
  IndP∞ ø = pø
  IndP∞ (η x) = pη x
  IndP∞ (sup s) = IndSeq∞ s
  IndP∞ (comm x x₁ i) = isProp→PathP' (λ x → snd (P x)) (comm x x₁) ih1 ih2 i
    where
      ih1 = IndP∞ x ∪P IndP∞ x₁
      ih2 = IndP∞ x₁ ∪P IndP∞ x
  IndP∞ (assoc x x₁ x₂ i) = isProp→PathP' (λ x → snd (P x)) (assoc x x₁ x₂) (IndP∞ x ∪P (IndP∞ x₁ ∪P IndP∞ x₂))
                                                                           ((IndP∞ x ∪P IndP∞ x₁) ∪P IndP∞ x₂) i
  IndP∞ (idem x i) = isProp→PathP' (λ x → snd (P x)) (idem x) (IndP∞ x ∪P IndP∞ x) (IndP∞ x) i
  IndP∞ (unit x i) = isProp→PathP' (λ x → snd (P x)) (unit x) (IndP∞ x ∪P pø) (IndP∞ x) i
  IndP∞ (bound s@(cons hd tail) n@zero i)
        = isProp→PathP' (λ x → snd (P x)) (bound s n) (IndP∞ hd ∪P IndSeq∞ s) (IndSeq∞ s) i
  IndP∞ (bound s@(cons hd tail) n@(suc n') i)
        = isProp→PathP' (λ x → snd (P x)) (bound s n) (IndP∞ (tail n') ∪P IndSeq∞ s) (IndSeq∞ s) i
  IndP∞ (dist s x i)
        = isProp→PathP' (λ x → snd (P x)) (dist s x)
             (IndSeq∞ s ∪P IndP∞ x)
             (consP (IndP∞ (s .Seq.hd) ∪P IndP∞ x) (\ n → IndP∞ (s .Seq.tail n) ∪P IndP∞ x))
             i
  IndP∞ (trunc x y p q i j) =
    isOfHLevel→isOfHLevelDep 2 (λ x → isProp→isSet (snd (P x)))
                             (IndP∞ x) (IndP∞ y)
                             (cong IndP∞ p) (cong IndP∞ q)
                             (trunc x y p q)
                             i j


  IndSeq∞ : ∀ s → ⟨ P (sup s) ⟩
  IndSeq∞ (cons hd tail) = psup (cons hd tail) (split-nat (IndP∞ hd) (λ n → IndP∞ (tail n)))

  consP : ∀ {s} → ⟨ P (s .Seq.hd) ⟩ → (∀ n → ⟨ P (s .Seq.tail n) ⟩) → ⟨ P (sup s) ⟩
  consP {cons hd tail} h t = psup (cons hd tail) (split-nat h (λ n → t n))

  _∪P_ : ∀ {x} xp {y} yp → ⟨ P (x ∪ y) ⟩
  _∪P_ {x} xp {y} yp = psup (cons x (λ _ → y)) (split-nat xp (λ _ → yp))

-- The order on countable powerset induced by the ∪ operation.
_≤_ : ∀ {ℓ} {A : Set ℓ} → P∞ A → P∞ A → Set _
x ≤ y = (x ∪ y) ≡ y

-- ≤ is transitive and antisymmetric
trans≤ : ∀ {ℓ} {A : Set ℓ} {x y z : P∞ A} → x ≤ y → y ≤ z → x ≤ z
trans≤ {x = x}{y}{z} p q =
  cong (λ z' → x ∪ z') (sym q) ∙ assoc x y z ∙ cong (_∪ z) p ∙ q

antisym≤ : ∀ {ℓ} {A : Set ℓ} {x y : P∞ A} → x ≤ y → y ≤ x → x ≡ y
antisym≤ p q = sym q ∙ comm _ _ ∙ p

-- The sup operation builds least upper bounds wrt ≤.
least-bound≤ : ∀ {ℓ} {A : Set ℓ} (s : Seq (P∞ A)) → (x : P∞ A)
              → (∀ n → apply s n ≤ x) → sup s ≤ x
least-bound≤ s x s≤x =
  dist s x
 ∙ cong sup (\ i → cons (s≤x zero i) (\ n → s≤x (suc n) i))
 ∙ idem x

-- Membership in a countable powerset, x ∈ s.
cons-hProp : hProp₀ → (∀ n → hProp₀) → hProp₀
cons-hProp p q = ∥ ⟨ p ⟩ ⊎ (Σ[ n ∈ ℕ ] ⟨ q n ⟩) ∥₁ , isPropPropTrunc

_∈S_ : ∀ {A : Set} x (s : Seq (P∞ A)) → hProp₀
_∈_ : {A : Set} → A → P∞ A → hProp₀

x ∈S cons hd tail = cons-hProp (x ∈ hd) (\ n → x ∈ tail n)

x ∈ ø = Logic.⊥
x ∈ η y = x ≡ₚ y
x ∈ sup (cons hd tail) = cons-hProp (x ∈ hd) (\ n → x ∈ tail n)
x ∈ comm xs ys i      = ⇔toPath {P = cons-hProp (x ∈ xs) (λ _ → x ∈ ys)}
                          {cons-hProp (x ∈ ys) (λ _ → x ∈ xs)}
                          (PT.rec squash₁ (\ { (_⊎_.inl x) → inr (0 , x)
                                                  ; (_⊎_.inr (_ , x)) → inl x}))
                          (PT.rec squash₁ (\ { (_⊎_.inl x) → inr (0 , x)
                                                   ; (_⊎_.inr (_ , x)) → inl x}))
                          i
x ∈ assoc xs ys zs i = ⇔toPath {P = cons-hProp (x ∈ xs) (λ _ → cons-hProp (x ∈ ys) λ _ → x ∈ zs)}
                         {cons-hProp (cons-hProp (x ∈ xs) (λ _ → x ∈ ys)) λ _ → x ∈ zs}
                         (PT.rec squash₁ \ { (_⊎_.inl x)  → inl (inl x)
                                                ;  (_⊎_.inr (n , y)) →
                             PT.rec squash₁ (\ { (_⊎_.inl x) → inl (inr (n , x))
                                                    ; (_⊎_.inr x) → inr x }) y })
                         (PT.rec squash₁ \ { (_⊎_.inl x) →
                            PT.rec squash₁ (\ { (_⊎_.inl x) → inl x
                                                   ; (_⊎_.inr (n , x)) → inr (n , inl x) }) x
                                                ; (_⊎_.inr (n , x)) → inr (n , inr (n , x)) }) i
x ∈ idem xs i = ⇔toPath {P = cons-hProp (x ∈ xs) (\ _ → x ∈ xs)}
                 {x ∈ xs}
                 (PT.rec ((x ∈ xs) .snd) (\ { (_⊎_.inl x) → x ; (_⊎_.inr x) → x .snd })) (\ p → inl p)
                 i
x ∈ unit xs i = ⇔toPath {P = cons-hProp (x ∈ xs) (\ _ → Logic.⊥)}
                 {x ∈ xs} ((PT.rec ((x ∈ xs) .snd) (\ { (_⊎_.inl x) → x ; (_⊎_.inr (fst₁ , ())) }))) inl i
x ∈ bound s n@zero i
  = ⇔toPath {P = cons-hProp (x ∈ s .Seq.hd) \ _ → x ∈S s} {x ∈S s}
            (PT.rec squash₁ (\ { (_⊎_.inl x) → inl x
                                    ; (_⊎_.inr (n , x)) → x}))
            (PT.rec squash₁ (\ { (_⊎_.inl x) → inl x
                                    ; (_⊎_.inr x) → inr (0 , inr x) }))
            i
x ∈ bound s n@(suc n') i = ⇔toPath {P = cons-hProp (x ∈ s .Seq.tail n') \ _ → x ∈S s} {x ∈S s}
            (PT.rec squash₁ (\ { (_⊎_.inl x) → inr (_ , x)
                                    ; (_⊎_.inr (n , x)) → x}))
            ((PT.rec squash₁ (\ { (_⊎_.inl x) → inr (0 , inl x)
                                     ; (_⊎_.inr x) → inr (0 , inr x) })))
            i
x ∈ dist s xs i = ⇔toPath {P = cons-hProp (x ∈S s) λ _ → x ∈ xs}
                    {cons-hProp (cons-hProp (x ∈ s .Seq.hd) \ _ → x ∈ xs) \ n → cons-hProp (x ∈ s .Seq.tail n) \ _ → x ∈ xs}
                      (PT.rec squash₁
                       (\ { (_⊎_.inl x) →
                            PT.rec squash₁ (\ { (_⊎_.inl x) → inl (inl x)
                                                   ; (_⊎_.inr (n , x)) → inr (n , inl x)})
                                                x
                          ; (_⊎_.inr (n , x)) → inl (inr (n , x))}))
                      (PT.rec squash₁
                       (\ { (_⊎_.inl x) →
                            PT.rec squash₁ (\ { (_⊎_.inl x) → inl (inl x)
                                                   ; (_⊎_.inr (n , x)) → inr (n , x) }) x
                          ; (_⊎_.inr (n , x)) →
                            PT.rec squash₁ (\ { (_⊎_.inl x) → inl (inr (n , x))
                                                   ; (_⊎_.inr x) → inr x}) x }))
                      i
x ∈ trunc xs ys p q i j = isSetHProp (x ∈ xs) (x ∈ ys) (cong (x ∈_) p) (cong (x ∈_) q) i j

-- Membership and union.
∪-in-L : ∀ {A : Set} {P : P∞ A} {P' s} → ⟨ s ∈ P ⟩ → ⟨ s ∈ (P ∪ P') ⟩
∪-in-L = inl

∪-out : ∀ {A : Set} {P : P∞ A} {P' s} → ⟨ s ∈ (P ∪ P') ⟩ → ∥ ⟨ s ∈ P ⟩ ⊎ ⟨ s ∈ P' ⟩ ∥₁
∪-out = PT.map (⊎.map (λ x → x) snd)

∪-in-R : ∀ {A : Set} {P : P∞ A} {P' s} → ⟨ s ∈ P' ⟩ → ⟨ s ∈ (P ∪ P') ⟩
∪-in-R s = inr (0 , s)

-- The subset relation ⊂, which is logically equivalent to ≤.
_⊂_ : {A : Set} → P∞ A → P∞ A → Set
xs ⊂ ys = ∀ x → ⟨ x ∈ xs ⟩ → ⟨ x ∈ ys ⟩

⊂-to-≤-η : {A : Set} (a : A) (x : P∞ A) → ⟨ a ∈ x ⟩ → η a ≤ x
⊂-to-≤-η a =
  IndP∞ (λ _ → _ , (hLevelPi 1 (λ _ → trunc _ _)))
        Empty.rec
        (λ a' → PT.rec (trunc _ _) (λ p → cong (λ x → η x ∪ η a') p  ∙ idem (η a')))
        (λ s ih → PT.rec (trunc _ _) (λ { (_⊎_.inl p) → trans≤ (ih zero p) (bound s zero)
                                              ; (_⊎_.inr (n , p)) → trans≤ (ih (suc n) p) (bound s (suc n)) }))

⊂-to-≤ : {A : Set} → (x y : P∞ A) → y ⊂ x → y ≤ x
⊂-to-≤ x =
  IndP∞ (λ _ → _ , (hLevelPi 1 (λ _ → trunc _ _)))
        (λ _ → comm ø x ∙ unit x)
        (λ a p → ⊂-to-≤-η a x (p a ∣ refl ∣₁))
          (λ s ih p → least-bound≤ s x (λ { zero → ih zero (λ a q → p a ∣ _⊎_.inl q ∣₁) ;
                                           (suc n) → ih (suc n) (λ a q → p a ∣ _⊎_.inr (n , q) ∣₁) }))

-- Extensional equality of subsets: they are equal if they contain the
-- same elements. This is equivalent to path equality.
_≅_ : {A : Set} → P∞ A → P∞ A → Set
xs ≅ ys = Σ (xs ⊂ ys) \ _ → (ys ⊂ xs)

P∞-ext : {A : Set} {x y : P∞ A} → x ≅ y → x ≡ y
P∞-ext (p , q) = antisym≤ (⊂-to-≤ _ _ p) (⊂-to-≤ _ _ q)

-- Action of P∞ on functions, defining a functor on P∞.
mapP∞ : ∀ {A B : Set} → (A → B) → P∞ A → P∞ B
mapSP∞ : ∀ {A B : Set} → (A → B) → Seq (P∞ A) → Seq (P∞ B)

mapSP∞ f (cons hd tail) = cons (mapP∞ f hd) (\ n → mapP∞ f (tail n))
mapP∞ f ø = ø
mapP∞ f (η x) = η (f x)
mapP∞ f (sup (cons hd tail)) = sup (cons (mapP∞ f hd) (\ n → mapP∞ f (tail n)))
mapP∞ f (comm x y i)      = comm (mapP∞ f x) (mapP∞ f y) i
mapP∞ f (assoc p p₁ p₂ i) = assoc (mapP∞ f p) (mapP∞ f p₁) (mapP∞ f p₂) i
mapP∞ f (idem p i) = idem (mapP∞ f p) i
mapP∞ f (unit p i) = unit (mapP∞ f p) i
mapP∞ f (bound (cons hd tail) zero    i) = bound (cons (mapP∞ f hd) (\ n → mapP∞ f (tail n))) zero i
mapP∞ f (bound (cons hd tail) (suc n) i) = bound (cons (mapP∞ f hd) (\ n → mapP∞ f (tail n))) (suc n) i
mapP∞ f (dist (cons hd tail) p i) = dist (cons (mapP∞ f hd) (\ n → mapP∞ f (tail n))) (mapP∞ f p) i
mapP∞ f (trunc p q x y i j) = trunc _ _ (cong (mapP∞ f) x) (cong (mapP∞ f) y) i j

mapmapP∞ : ∀ {A B C : Set} (f : B → C) (g : A → B) → (x : P∞ A) → mapP∞ f (mapP∞ g x) ≡ mapP∞ (\ x → f (g x)) x
mapmapSP∞ : ∀ {A : Set}{B : Set}{C : Set}
             → (f : B → C) (g : A → B) (x : Seq (P∞ A)) → mapSP∞ f (mapSP∞ g x) ≡ mapSP∞ (\ v → f (g v)) x
mapmapSP∞ f g (cons hd tail) = cong₂ cons (mapmapP∞ f g hd) (funExt \ n → mapmapP∞ f g (tail n))
mapmapP∞ f g ø = refl
mapmapP∞ f g (η x) = refl
mapmapP∞ f g (sup s) = cong sup (cong₂ cons (mapmapP∞ f g (Seq.hd s)) (funExt \ n → mapmapP∞ f g (Seq.tail s n)))
mapmapP∞ f g (comm x x₁ i) j = comm (mapmapP∞ f g x j) (mapmapP∞ f g x₁ j) i
mapmapP∞ f g (assoc x x₁ x₂ i) j = assoc (mapmapP∞ f g x j) (mapmapP∞ f g x₁ j) (mapmapP∞ f g x₂ j) i
mapmapP∞ f g (idem x i) j = idem (mapmapP∞ f g x j) i
mapmapP∞ f g (unit x i) j = unit (mapmapP∞ f g x j) i
mapmapP∞ f g (bound s zero i) j = bound (mapmapSP∞ f g s j) zero i
mapmapP∞ f g (bound s (suc n) i) j = bound (mapmapSP∞ f g s j) (suc n) i
mapmapP∞ f g (dist s x i) j = dist (mapmapSP∞ f g s j) (mapmapP∞ f g x j) i
mapmapP∞ f g (trunc m0 m1 x y i i') j = trunc (mapmapP∞ f g m0 j) (mapmapP∞ f g m1 j)
                                              (cong (\ x → mapmapP∞ f g x j) x) (cong (\ x → mapmapP∞ f g x j) y) i i'

mapidP∞ : ∀ {A : Set} → (x : P∞ A) → mapP∞ (λ y → y) x ≡ x
mapidSP∞ : ∀ {A : Set} → (x : Seq (P∞ A)) → mapSP∞ (λ y → y) x ≡ x
mapidSP∞ (cons hd tail) = cong₂ cons (mapidP∞ hd) (funExt \ n → mapidP∞ (tail n))
mapidP∞ ø = refl
mapidP∞ (η x) = refl
mapidP∞ (sup s) = cong sup (cong₂ cons (mapidP∞ (Seq.hd s)) (funExt \ n → mapidP∞ (Seq.tail s n)))
mapidP∞ (comm x x₁ i) j = comm (mapidP∞ x j) (mapidP∞ x₁ j) i
mapidP∞ (assoc x x₁ x₂ i) j = assoc (mapidP∞ x j) (mapidP∞ x₁ j) (mapidP∞ x₂ j) i
mapidP∞ (idem x i) j = idem (mapidP∞ x j) i
mapidP∞ (unit x i) j = unit (mapidP∞ x j) i
mapidP∞ (bound s zero i) j = bound (mapidSP∞ s j) zero i
mapidP∞ (bound s (suc n) i) j = bound (mapidSP∞ s j) (suc n) i
mapidP∞ (dist s x i) j = dist (mapidSP∞ s j) (mapidP∞ x j) i
mapidP∞ (trunc m0 m1 x y i i') j = trunc (mapidP∞ m0 j) (mapidP∞ m1 j)
                                              (cong (\ x → mapidP∞ x j) x) (cong (\ x → mapidP∞ x j) y) i i'

-- Monadic bind, so that P∞ is a monad.
bindSeq : ∀ {l l'} {A : Set l}{B : Set l'}
  → Seq (P∞ A) → (A → P∞ B) → Seq (P∞ B)
bind : ∀ {l l'} {A : Set l}{B : Set l'} → P∞ A → (A → P∞ B) → P∞ B

bindSeq (cons hd tail) f = cons (bind hd f) (\ n → bind (tail n) f)

bind ø f                   = ø
bind (η x) f               = f x
bind (sup s) f             = sup (bindSeq s f)
bind (comm x x₁ i) f       = comm (bind x f) (bind x₁ f) i
bind (assoc x x₁ x₂ i) f   = assoc (bind x f) (bind x₁ f) (bind x₂ f) i
bind (idem x i) f          = idem (bind x f) i
bind (unit x i) f          = unit (bind x f) i
bind (bound s zero i) f    = bound (bindSeq s f) zero i
bind (bound s (suc n) i) f = bound (bindSeq s f) (suc n) i
bind (dist s x i) f        = dist (bindSeq s f) (bind x f) i
bind (trunc x y p q i j) f = trunc (bind x f) (bind y f) (cong (λ z → bind z f) p) (cong (λ z → bind z f) q) i j

map-bind : ∀ {l} {A : Set l}{B : Set}{C : Set}
             → (m : P∞ A) → (k : A → P∞ B) → (f : B → C) → mapP∞ f (bind m k) ≡ bind m (\ v → mapP∞ f (k v))
map-bindS : ∀ {l} {A : Set l}{B : Set}{C : Set}
             → (m : Seq (P∞ A)) → (k : A → P∞ B) → (f : B → C) → mapSP∞ f (bindSeq m k) ≡ bindSeq m (\ v → mapP∞ f (k v))
map-bindS (cons hd tail) k f = cong₂ cons (map-bind hd k f) (funExt \ n → map-bind (tail n) k f)
map-bind ø k f = refl
map-bind (η x) k f = refl
map-bind (sup s) k f = cong sup (cong₂ cons (map-bind (Seq.hd s) k f) (funExt \ n → map-bind (Seq.tail s n) k f))
map-bind (comm m m₁ i) k f j = comm (map-bind m k f j) (map-bind m₁ k f j) i
map-bind (assoc m m₁ m₂ i) k f j = assoc (map-bind m k f j) (map-bind m₁ k f j) (map-bind m₂ k f j) i
map-bind (idem m i) k f j = idem (map-bind m k f j) i
map-bind (unit m i) k f j = unit (map-bind m k f j) i
map-bind (bound s zero i) k f j = bound (map-bindS s k f j) zero i
map-bind (bound s (suc n) i) k f j = bound (map-bindS s k f j) (suc n) i
map-bind (dist s m i) k f j = dist (map-bindS s k f j) (map-bind m k f j) i
map-bind (trunc m0 m1 x y i i') k f j = trunc (map-bind m0 k f j) (map-bind m1 k f j)
                                              (cong (\ x → map-bind x k f j) x) (cong (\ x → map-bind x k f j) y) i i'

bind-map  : ∀ {A : Set}{B : Set}{C : Set}
              → (m : P∞ A) → (k : B → P∞ C) → (f : A → B) → (bind (mapP∞ f m) k) ≡ bind m (\ v → k (f v))
bind-mapS : ∀ {A : Set}{B : Set}{C : Set}
             → (m : Seq (P∞ A)) → (k : B → P∞ C) → (f : A → B) → bindSeq (mapSP∞ f m) k ≡ bindSeq m (\ v → k (f v))
bind-mapS (cons hd tail) k f = cong₂ cons (bind-map hd k f) (funExt \ n → bind-map (tail n) k f)
bind-map ø k f = refl
bind-map (η x) k f = refl
bind-map (sup s) k f = cong sup (cong₂ cons (bind-map (Seq.hd s) k f) (funExt \ n → bind-map (Seq.tail s n) k f))
bind-map (comm m m₁ i) k f j = comm (bind-map m k f j) (bind-map m₁ k f j) i
bind-map (assoc m m₁ m₂ i) k f j = assoc (bind-map m k f j) (bind-map m₁ k f j) (bind-map m₂ k f j) i
bind-map (idem m i) k f j = idem (bind-map m k f j) i
bind-map (unit m i) k f j = unit (bind-map m k f j) i
bind-map (bound s zero i) k f j = bound (bind-mapS s k f j) zero i
bind-map (bound s (suc n) i) k f j = bound (bind-mapS s k f j) (suc n) i
bind-map (dist s m i) k f j = dist (bind-mapS s k f j) (bind-map m k f j) i
bind-map (trunc m0 m1 x y i i') k f j = trunc (bind-map m0 k f j) (bind-map m1 k f j)
                                              (cong (\ x → bind-map x k f j) x) (cong (\ x → bind-map x k f j) y) i i'

cong-bind : ∀ {A B : Set} (x : P∞ A) {f g : A → P∞ B} → (∀ a → ⟨ a ∈ x ⟩ → f a ≡ g a) → bind x f ≡ bind x g
cong-bind x {f}{g} =
  IndP∞ (λ x → ((∀ a → ⟨ a ∈ x ⟩ → f a ≡ g a) → bind x f ≡ bind x g) , hLevelPi 1 (λ _ → trunc _ _))
        (λ _ → refl)
        (λ a m → m a ∣ refl ∣₁)
        (λ s ih m → cong sup (cong₂ cons (ih 0 (λ a m' → m a (inl m'))) (funExt (λ n → ih (suc n) (λ a m' → m a (inr (n , m')))))))
        x

bind-η : ∀ {A : Set} (x : P∞ A) → bind x η ≡ x
bind-η =
  IndP∞ (λ x → _ , trunc _ _)
        refl
        (λ _ → refl)
        (λ s ih → cong sup (cong₂ cons (ih 0) (funExt (λ n → ih (suc n)))))

mapP∞-is-bind : {A B : Set} {f : A → B} (x : P∞ A) → mapP∞ f x ≡ bind x (λ a → η (f a))
mapP∞-is-bind =
  IndP∞ (λ x → _ , trunc _ _)
        refl
        (λ _ → refl)
        (λ s ih → cong sup (cong₂ cons (ih 0) (funExt (λ n → ih (suc n)))))

bind-bind : {A B C : Set} (m : P∞ A) (f : A → P∞ B) (g : B → P∞ C)
  → bind (bind m f) g ≡ bind m (λ x → bind (f x) g)
bind-bind m f g =
  IndP∞ (\ m → (bind (bind m f) g ≡ bind m (λ x → bind (f x) g)) , trunc _ _)
        refl
        (\ _ → refl)
        (\ s ih → cong sup (cong₂ cons (ih 0) (funExt \ n → ih (suc n))))
        m

-- Relationship of bind with the operations of P∞.
bind-sup : {A B : Set} (f : ℕ → A → P∞ B) (x : P∞ A)  →
  bind x (λ a → sup (seq (λ n → f n a))) ≡ sup (seq λ n → bind x (f n))
bind-sup f =
  IndP∞ (λ _ → _ , trunc _ _)
    (sym (idem _))
    (λ _ → refl)
    (λ s ih → cong sup (cong₂ cons (ih 0) (funExt \ n → ih (suc n))) ∙ P∞-ext
      ((\ x → PT.rec squash₁ \ { (_⊎_.inl x) → PT.rec squash₁ (\ { (_⊎_.inl x) → inl (inl x)
                                                                   ; (_⊎_.inr x) → inr (x .fst , inl (x .snd)) }) x
                                ; (_⊎_.inr (n , x)) → PT.rec squash₁ (\ { (_⊎_.inl x) → inl (inr (n , x))
                                                                         ; (_⊎_.inr (m , x)) → inr (m , inr (n , x)) }) x })
      , (\ x → PT.rec squash₁ \ { (_⊎_.inl x) → PT.rec squash₁ (\ { (_⊎_.inl x) →  inl (inl x)
                                                                    ; (_⊎_.inr (n , x)) → inr (n , inl x) }) x
                                 ; (_⊎_.inr (n , x)) → PT.rec squash₁ (\ { (_⊎_.inl x) → inl (inr (_ , x))
                                                                          ; (_⊎_.inr (m , x)) → inr (_ , inr (_ , x)) }) x })
      ))

bind-∪ : {A B : Set} (f g : A → P∞ B) (x : P∞ A)  →
  bind x (λ a → f a ∪ g a) ≡ bind x f ∪ bind x g
bind-∪ f g = bind-sup (λ { zero → f ; (suc n) → g})

bind-ø : {A B : Set} (x : P∞ A) → bind {B = B} x (λ _ → ø) ≡ ø
bind-ø =
  IndP∞ (λ _ → _ , trunc _ _)
    refl
    (λ _ → refl)
    (λ s ih → cong sup (cong₂ cons (ih 0) (λ i n → ih (suc n) i)) ∙ idem _)

bind-comm : {A B C : Set} (f : A → B → P∞ C) (x : P∞ A) (y : P∞ B)
  → bind x (λ a → bind y (f a)) ≡ bind y (λ b → bind x (λ a → f a b))
bind-comm f x =
  IndP∞ (λ _ → _ , trunc _ _)
    (bind-ø x)
    (λ _ → refl)
    (λ s ih → bind-sup (λ n a → bind (apply s n) (f a)) x ∙ cong sup (cong₂ cons (ih 0) (λ i n → ih (suc n) i)))

-- Lemmata about the relationship between ∈ and mapP∞.
mapP∞-in : {A B : Set} (f : A → B) (a : A) (x : P∞ A)
  → ⟨ a ∈ x ⟩ → ⟨ f a ∈ mapP∞ f x ⟩
mapP∞-in f a =
  IndP∞ (λ x → _ , hLevelPi 1 (λ _ → snd (f a ∈ mapP∞ f x)))
        (λ x → x)
        (λ a → PT.map (cong f))
        (λ s ih → PT.map λ { (_⊎_.inl p) → _⊎_.inl (ih zero p)
                                 ; (_⊎_.inr (n , p)) → _⊎_.inr (n , (ih (suc n) p)) })

mapP∞-out : {A B : Set} (f : A → B) (b : B) (x : P∞ A)
  → ⟨ b ∈ mapP∞ f x ⟩ → ∥ Σ A (λ a → ⟨ a ∈ x ⟩ × (b ≡ f a)) ∥₁
mapP∞-out f b =
  IndP∞ (λ x → _ , hLevelPi 1 (λ _ → squash₁))
        (λ ())
        (λ a → PT.map (λ p → (a , (∣ refl ∣₁ , p))))
        (λ s ih → PT.rec squash₁ (λ { (_⊎_.inl p) → PT.map (λ { (a , q , r) → a , inl q , r }) (ih zero p)
                                        ; (_⊎_.inr (n , p)) → PT.map (λ { (a , q , r) → a , (inr (n , q)) , r }) (ih (suc n) p) }))

lemma-4·1-part1 = mapP∞-in
lemma-4·1-part2 = mapP∞-out

∈mapP∞-eq' : {A B : Set} (f : A → B) (b : B) (x : P∞ A)
  → b ∈ mapP∞ f x ≡ (∥ Σ A (λ a → ⟨ a ∈ x ⟩ × (b ≡ f a)) ∥₁ , isPropPropTrunc)
∈mapP∞-eq' f b x =
  ⇔toPath (lemma-4·1-part2 f b x)
           (PT.rec (snd (b ∈ mapP∞ f x)) (λ {(a , m , eq) → subst (λ z → ⟨ z ∈ mapP∞ f x ⟩) (sym eq) (lemma-4·1-part1 f a x m) }))

∈mapP∞-eq : {A B : Set} (f : A → B) (b : B) (x : P∞ A)
  → ⟨ b ∈ mapP∞ f x ⟩ ≡ ∥ Σ A (λ a → ⟨ a ∈ x ⟩ × (b ≡ f a)) ∥₁
∈mapP∞-eq f b x = cong fst (∈mapP∞-eq' f b x)

-- Lemmata about the relationship between ∈ and bind.

bind-out : {A B : Set} (f : A → P∞ B) (b : B) (x : P∞ A)
  → ⟨ b ∈ bind x f ⟩ → ∥ Σ A (λ a → ⟨ a ∈ x ⟩ × ⟨ b ∈ f a ⟩) ∥₁
bind-out f b =
  IndP∞ (λ x → _ , hLevelPi 1 (λ _ → squash₁))
    (λ ())
    (λ a m → ∣ a , ∣ refl ∣₁ , m ∣₁)
    (λ s ih → PT.rec squash₁
      (λ { (_⊎_.inl p) → PT.map (λ { (a , q , r) → a , inl q , r }) (ih zero p)
         ; (_⊎_.inr (n , p)) → PT.map (λ { (a , q , r) → a , (inr (n , q)) , r }) (ih (suc n) p) }))

bind-in : {A B : Set} (f : A → P∞ B) (b : B) (x : P∞ A)
    → Σ A (λ a → ⟨ a ∈ x ⟩ × ⟨ b ∈ f a ⟩) → ⟨ b ∈ bind x f ⟩
bind-in f b =
  IndP∞ (λ x → _ , hLevelPi 1 (λ _ → snd (b ∈ bind x f)))
    (λ { (a , () , m)})
    (λ { a (a' , eq , m) → PT.rec (snd (b ∈ f a)) (λ eq → subst (λ x → ⟨ b ∈ f x ⟩) eq m) eq })
    (λ {s ih (a , p , m) → PT.map (λ { (_⊎_.inl p) → _⊎_.inl (ih zero (a , p , m))
                                           ; (_⊎_.inr (n , p)) → _⊎_.inr (n , ih (suc n) (a , p , m) ) })
                                        p })

-- List can be embedded in countable subsets.
fromList : ∀ {A : Set} → List A → P∞ A
fromList [] = ø
fromList (x ∷ xs) = η x ∪ fromList xs

fromList-mapL : ∀ {A B : Set} (f : A → B) xs
  → fromList (List.map f xs) ≡ mapP∞ f (fromList xs)
fromList-mapL f [] = refl
fromList-mapL f (x ∷ xs) = cong₂ _∪_ refl (fromList-mapL f xs)

-- A countable subset is finitely presented if it's finite, in the
-- sense that it comes from the embedding of some list.
-- NB: It used ≡'
FinitelyPresented : ∀ {A : Set} → P∞ A → Set
FinitelyPresented s = ∃[ xs ∈ _ ] fromList xs ≡ s

abstract
  map-fn : {A B : Set} {f : A → B} {x : P∞ A}
    → FinitelyPresented x → FinitelyPresented (mapP∞ f x)
  map-fn = PT.map (λ { (xs , p) →  List.map _ xs , fromList-mapL _ xs ∙ cong (mapP∞ _) p })




-- sup-step : {A : Set} (s : Seq (P∞ A)) → apply s 0 ∪ sup (seq (Seq.tail s)) ≡ sup s
-- sup-step s = P∞-ext ((\ x → PT.rec squash₁ (elim-⊎ (\ a → inl a)
--                     (\ { (n , p) → PT.rec squash₁ (elim-⊎ (\ a → inr (0 , a)) \ { (n , b) → inr (suc n , b) }) p
--                         })) )
--   , \ x → PT.rec squash₁ (elim-⊎ inl (\ { (0 , p) → inr (0 , inl p); (suc n , p) → inr (0 , inr (n , p)) })))


-- {A = A} {B = B} = \ p f → go f p
--  module Bind where
--   module M (f : A → P∞ B) where
--    mutual
--     goS : Seq (P∞ A) → Seq (P∞ B)
--     goS (cons hd tail) = cons (go hd) (\ n → go (tail n))
--     go : P∞ A → P∞ B
--     go ø                    = ø
--     go (η x)                = f x
--     go (sup s)              = sup (goS s)
--     go (comm x x₁ i)        = comm (go x) (go x₁) i
--     go (assoc x x₁ x₂ i)    = assoc (go x) (go x₁) (go x₂) i
--     go (idem x i)           = idem (go x) i
--     go (unit x i)           = unit (go x) i
--     go (bound s zero i)     = bound (goS s) zero i
--     go (bound s (suc n) i)  = bound (goS s) (suc n) i
--     go (dist s x i)         = dist (goS s) (go x) i
--     go (trunc x y p q i j)  = trunc (go x) (go y) (cong go p) (cong go q) i j
--   open M public
