{-# OPTIONS --cubical #-}

open import AbsNames

-- Syntax of early π-calculus

module pi-calculus.Syntax (ns : Names) where

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


-- -- The type of actions. 
data Act (n : ℕ) : (m : ℕ) → Set where
  out : (ch : Name n) → Name n → Act n n
  inp : (ch : Name n) → Act n (suc n)
  τ  : Act n n

infixr 12 !_
infix 11 _∣∣_

-- π-calculus syntax.
data Pi (n : ℕ) : Set where
  end : Pi n
  _·_ : ∀ {m} → (a : Act n m) → (P : Pi m) → Pi n
  _⊕_ _∣∣_ : (P : Pi n) → (Q : Pi n) → Pi n
  ν : (P : Pi (suc n)) → Pi n
  guard : Name n → Name n → Pi n → Pi n
  !_ : (P : Pi n) → Pi n

-- Action of CCS on renamings.
mapPi : ∀ {m n} → (Name m → Name n) → Pi m → Pi n
mapPi f end = end
mapPi f (out ch v · P) = out (f ch) (f v) · mapPi f P
mapPi f (inp ch · P) = inp (f ch) · mapPi (lift f) P
mapPi f (τ · P) = τ · mapPi f P
mapPi f (P ⊕ Q) = mapPi f P ⊕ mapPi f Q
mapPi f (P ∣∣ Q) = mapPi f P ∣∣ mapPi f Q
mapPi f (ν P) = ν (mapPi (lift f) P)
mapPi f (guard x y P) = guard (f x) (f y) (mapPi f P)
mapPi f (! P) = ! (mapPi f P)

mapPi-id : ∀ {n} (P : Pi n) → mapPi (λ x → x) P ≡ P
mapPi-id end = refl
mapPi-id (out ch x · P) = cong′ (out ch x ·_) (mapPi-id P)
mapPi-id (inp ch · P) = cong′ (inp ch ·_) ((λ i → mapPi (λ v → lift-id v i) P) ∙ mapPi-id P)
mapPi-id (τ · P) = cong′ (τ ·_) (mapPi-id P)
mapPi-id (P ⊕ P₁) = cong₂ _⊕_ (mapPi-id P) (mapPi-id P₁)
mapPi-id (P ∣∣ P₁) = cong₂ _∣∣_ (mapPi-id P) (mapPi-id P₁)
mapPi-id (ν P) = cong ν ((λ i → mapPi (λ v → lift-id v i) P) ∙ mapPi-id P)
mapPi-id (guard x x₁ P) = cong (guard x x₁) (mapPi-id P)
mapPi-id (! P) = cong !_ (mapPi-id P)

mapmapPi : ∀ {n m o} (f : Name n → Name m) (g : Name o → Name n)
  → ∀ P → mapPi f (mapPi g P) ≡ mapPi (\ x → f (g x)) P
mapmapPi f g end = refl
mapmapPi f g (out ch x · P) = cong (out _ _ ·_) (mapmapPi f g P)
mapmapPi f g (inp ch · P) =
  cong (inp (f (g ch)) ·_) (mapmapPi (lift f) (lift g) P
  ∙ (cong mapPi (funExt (liftlift f g)) <* P))
mapmapPi f g (τ · P) = cong (τ ·_) (mapmapPi f g P)
mapmapPi f g (P ⊕ P₁) = cong₂ _⊕_ (mapmapPi f g P) (mapmapPi f g P₁)
mapmapPi f g (P ∣∣ P₁) = cong₂ _∣∣_ (mapmapPi f g P) (mapmapPi f g P₁)
mapmapPi f g (ν P) =
  cong ν (mapmapPi (lift f) (lift g) P
  ∙ (cong mapPi (funExt (liftlift f g)) <* P))
mapmapPi f g (guard x x₁ P) = cong (guard _ _) (mapmapPi f g P)
mapmapPi f g (! P) = cong !_ (mapmapPi f g P)

-- Structural congruence of terms.
infix 10 _≈_
data _≈_ {n : ℕ} : (P Q : Pi n) → Set where
  refl≈ : ∀ {P} → P ≈ P
  sym≈ : ∀ {P Q} → P ≈ Q → Q ≈ P
  _∙≈_ : ∀ {P Q R} → P ≈ Q → Q ≈ R → P ≈ R
  cong· : ∀ {m P Q} {a : Act n m} → P ≈ Q → a · P ≈ a · Q
  cong⊕ : ∀ {P P' Q Q'} → P ≈ P' → Q ≈ Q' → P ⊕ Q ≈ P' ⊕ Q'
  cong∣∣ : ∀ {P P' Q Q'} → P ≈ P' → Q ≈ Q' → P ∣∣ Q ≈ P' ∣∣ Q'
  congν : ∀ {P Q} → P ≈ Q → ν P ≈ ν Q
  congguard : ∀ {x y P Q} → P ≈ Q → guard x y P ≈ guard x y Q
  cong! : ∀ {P Q} → P ≈ Q → ! P ≈ ! Q
  unit⊕ : ∀ {P} → P ⊕ end ≈ P
  comm⊕ : ∀ {P Q} → P ⊕ Q ≈ Q ⊕ P
  assoc⊕ : ∀ {P Q R} → (P ⊕ Q) ⊕ R ≈ P ⊕ (Q ⊕ R)
  unit∣∣ : ∀ {P} → P ∣∣ end ≈ P
  comm∣∣ : ∀ {P Q} → P ∣∣ Q ≈ Q ∣∣ P
  assoc∣∣ : ∀ {P Q R} → (P ∣∣ Q) ∣∣ R ≈ P ∣∣ (Q ∣∣ R)
  repl : ∀ {P} → ! P ≈ P ∣∣ ! P
  guardrefl : ∀ {x P} → guard x x P ≈ P
  ν∣∣ : ∀ {P Q} → ν (P ∣∣ mapPi ι Q) ≈ ν P ∣∣ Q
  swapν : ∀ {P} → ν (ν P) ≈ ν (ν (mapPi swap P))
  νend : ν end ≈ end

≡→≈ : ∀ {n} {P Q : Pi n} → P ≡ Q → P ≈ Q
≡→≈ {P = P} eq = subst (λ Q → P ≈ Q) eq refl≈

-- Structural congruences is closed under renaming.
map≈ : ∀ {n m} {P Q : Pi n} (f : Name n → Name m) → P ≈ Q → mapPi f P ≈ mapPi f Q
map≈ f refl≈ = refl≈
map≈ f (sym≈ tr) = sym≈ (map≈ f tr)
map≈ f (tr ∙≈ tr₁) = map≈ f tr ∙≈ map≈ f tr₁
map≈ f (cong· {a = out ch x} tr) = cong· (map≈ f tr)
map≈ f (cong· {a = inp ch} tr) = cong· (map≈ (lift f) tr)
map≈ f (cong· {a = τ} tr) = cong· (map≈ f tr)
map≈ f (cong⊕ tr tr₁) = cong⊕ (map≈ f tr) (map≈ f tr₁)
map≈ f (cong∣∣ tr tr₁) = cong∣∣ (map≈ f tr) (map≈ f tr₁)
map≈ f (congν tr) = congν (map≈ (lift f) tr)
map≈ f (congguard tr) = congguard (map≈ f tr)
map≈ f (cong! tr) = cong! (map≈ f tr)
map≈ f unit⊕ = unit⊕
map≈ f comm⊕ = comm⊕
map≈ f assoc⊕ = assoc⊕
map≈ f unit∣∣ =  unit∣∣
map≈ f comm∣∣ = comm∣∣
map≈ f assoc∣∣ = assoc∣∣
map≈ f repl = repl
map≈ f guardrefl = guardrefl
map≈ f (ν∣∣ {Q = Q}) =
  transport (cong _≈_ (cong ν (cong₂ _∣∣_ refl (mapmapPi _ _ Q ∙ (cong mapPi (funExt (\ x → sym (lift-ι f x))) <* Q) ∙ sym (mapmapPi _ _ Q)))) <* _) ν∣∣
map≈ f (swapν {P = P}) =
  swapν ∙≈ congν (congν (≡→≈ (mapmapPi _ _ _ ∙ sym (mapmapPi _ _ _ ∙ cong (λ g → mapPi g P) (funExt (swap-lift f))))))
map≈ f νend = νend

-- Labels of π-calculus transitions
data Label (n : ℕ) : ℕ → Set where
  out : Name n → Name n → Label n n
  bout : Name n → Label n (suc n)
  inp : Name n → Name n → Label n n
  binp : Name n → Label n (suc n)
  τ : Label n n

labelInj : ∀ {n m} → Label n m → Inj n m
labelInj (out ch z) = idInj
labelInj (bout ch) = ι , ι-inj
labelInj (binp ch) = ι , ι-inj
labelInj (inp ch v) = idInj
labelInj τ = idInj

labelN : ∀{n m} → Label n m → ℕ → ℕ
labelN (out x x₁) k = k
labelN (bout x) k = suc k
labelN (binp x) k = suc k
labelN (inp x x₁) k = k
labelN τ k = k

disj : ∀{n m} → Label n m → Set
disj τ = Unit
disj _ = Empty.⊥

inp≢τ : ∀ {n} {ch v : Name n} → inp ch v ≡ τ → Empty.⊥
inp≢τ eq = transport (\ i → disj (eq (~ i))) _

mapLabel : ∀{n m k} → (Name n → Name m) → (a : Label n k) → Label m (labelN a m)
mapLabel f (out ch z) = out (f ch) (f z)
mapLabel f (bout ch) = bout (f ch)
mapLabel f (binp ch) = binp (f ch)
mapLabel f (inp ch v) = inp (f ch) (f v)
mapLabel f τ = τ

mapLabelι : ∀{n m} → (a : Label n m) → Label (suc n) (suc m)
mapLabelι (out ch z) = out (ι ch) (ι z)
mapLabelι (bout ch) = bout (ι ch)
mapLabelι (binp ch) = binp (ι ch)
mapLabelι (inp ch v) = inp (ι ch) (ι v)
mapLabelι τ = τ

labelRen : ∀{n m} (a : Label n m) (k : ℕ) → (Name n → Name k) → Name m → Name (labelN a k)
labelRen (out x x₁) k f v = f v
labelRen (bout x) k f v = lift f v
labelRen (binp x) k f v = lift f v
labelRen (inp x x₁) k f v = f v
labelRen τ k f v = f v

labelRen-inj : ∀{n m} (a : Label n m) (k : ℕ) (f : Inj n k)
  → ∀ x y → labelRen a k (fst f) x ≡ labelRen a k (fst f) y → x ≡ y
labelRen-inj (out x₁ x₂) k f = f .snd
labelRen-inj (bout x₁) k f = lift-inj f
labelRen-inj (binp x₁) k f = lift-inj f
labelRen-inj (inp x₁ x₂) k f = f .snd
labelRen-inj τ k f = f .snd

labellabelN : ∀ {l m' n} (g : Name l → Name n) (w : Label _ m') m
  → labelN (mapLabel g w) m ≡ labelN w m
labellabelN g (out x x₁) _ = refl
labellabelN g (bout x) _ = refl
labellabelN g (binp x) _ = refl
labellabelN g (inp _ x) _ = refl
labellabelN g τ _ = refl

mapmapLabel : ∀
             {l} {m} {n} {m'}
             (f : Name n → Name m) (g : Name l → Name n) (w : Label l m') →
             PathP (\ i → Label m (labellabelN  g w m i)) (mapLabel f (mapLabel g w))
                             (mapLabel (λ x₁ → f (g x₁)) w)
mapmapLabel f g (out x x₁) = refl
mapmapLabel f g (bout x) = refl
mapmapLabel f g (binp x) = refl
mapmapLabel f g (inp x x₁) = refl
mapmapLabel f g τ = refl

labellabelRen : ∀{l} {m} {n} {m'}
  → (f : Name n → Name m) (g : Name l → Name n) (w : Label l m') (x : Name m')
  → PathP (\ i → Name (labellabelN g w m i))
          (labelRen (mapLabel g w) m f (labelRen w n g x))
          (labelRen w _ (\ x → f (g x)) x)
labellabelRen f g (out x₁ x₂) x = refl
labellabelRen f g (bout x₁) x = liftlift f g x
labellabelRen f g (binp x₁) x = liftlift f g x
labellabelRen f g (inp x₁ x₂) x = refl
labellabelRen f g τ x = refl

labelRenInj : ∀ {n m m'}
  → (f : Name n → Name m) (x : Label n m') {v : Name n}
  → labelRen x m (f) (fst (labelInj x) v) ≡ fst (labelInj (mapLabel (f) x)) (f v)
labelRenInj f (out x x₁) {v} = refl
labelRenInj f (bout x) {v} = lift-ι (f) v
labelRenInj f (binp x) {v} = lift-ι (f) v
labelRenInj f (inp x x₁) {v} = refl
labelRenInj f τ {v} = refl

swap? : ∀ {n m} → Label n m → Pi (suc m) → Pi (suc m)
swap? (out ch z) P = P
swap? (bout ch) P = mapPi swap P
swap? (inp ch z) P = P
swap? (binp ch) P = mapPi swap P
swap? τ P = P

-- Early operational semantics.
infix 10 _[_]↦_
data _[_]↦_ : {n m : ℕ} (P : Pi n) (σ : Label n m) (Q : Pi m) → Set where
  out : ∀ {n P} (ch : Name n) v → out ch v · P [ out ch v ]↦ P
  inp : ∀ {n P} (ch : Name n) v → inp ch · P [ inp ch v ]↦ mapPi (for-fresh v) P
  binp : ∀ {n P} (ch : Name n) → inp ch · P [ binp ch ]↦ P
  τ : ∀ {n} {P : Pi n} → τ · P [ τ ]↦ P
  sumtr : ∀ {n m P Q P'} {a : Label n m} → P [ a ]↦ P' → P ⊕ Q [ a ]↦ P'
  partr : ∀ {n m P Q P'} {a : Label n m} → P [ a ]↦ P'
    → P ∣∣ Q [ a ]↦ P' ∣∣ mapPi (labelInj a .fst) Q
  com : ∀ {n P Q P' Q'} {ch v : Name n} → P [ out ch v ]↦ P' → Q [ inp ch v ]↦ Q'
    → P ∣∣ Q [ τ ]↦ P' ∣∣ Q'
  close : ∀ {n P Q P' Q'} {ch : Name n} → P [ bout ch ]↦ P' → Q [ binp ch ]↦ Q'
    → P ∣∣ Q [ τ ]↦ ν (P' ∣∣ Q')
  res : ∀ {n m P P'} {a : Label n m} → P [ mapLabelι a ]↦ P' → ν P [ a ]↦ ν (swap? a P')
  opn : ∀ {n P P'} {ch : Name n} → P [ out (ι ch) (fresh n) ]↦ P' → ν P [ bout ch ]↦ P'
  conv : ∀ {n m} {P P' Q Q'} {a : Label n m} → P [ a ]↦ Q → P ≈ P' → Q ≈ Q' → P' [ a ]↦ Q'

-- Reduction is closed under renaming.
map↦ : ∀ {n m m'} {P} {a : Label n m} {Q} (f : Name n → Name m') → P [ a ]↦ Q → mapPi f P [ mapLabel f a ]↦ mapPi (labelRen a _  f) Q
map↦ f (out ch v) = out (f ch) (f v)
map↦ f (inp {P = P} ch v) =
  transport (cong ((inp (f ch) · mapPi (lift f) P) [ inp (f ch) (f v) ]↦_)
                  (mapmapPi _ _ P
                  ∙ (cong mapPi (funExt \ v → sym (for-fresh-lift' _ _ f _ v)) <* P)
                  ∙ sym (mapmapPi _ _ P)))
            (_[_]↦_.inp (f ch) (f v))
map↦ f (binp ch) = binp (f ch)
map↦ f τ = τ
map↦ f (sumtr tr) = sumtr (map↦ f tr)
map↦ f (partr {P = P} {Q = Q} {a = a} tr) =
  transport (cong (mapPi f P ∣∣ mapPi f Q [ mapLabel f a ]↦_)
                  (cong₂ _∣∣_ refl
                         (mapmapPi _ _ Q
                         ∙ (cong mapPi (funExt (\ v → sym (labelRenInj f a {v}))) <* Q)
                         ∙ sym (mapmapPi _ _ Q))))
            (partr (map↦ f tr))
map↦ f (com tr tr₁) = com (map↦ f tr) (map↦ f tr₁)
map↦ f (close tr tr₁) = close (map↦ f tr) (map↦ f tr₁)
map↦ {a = out x x₁} f (res {P = P} {a = .(out x x₁)} tr) =
  res (transport (cong (_[_]↦_ _) (cong₂ Label.out (lift-ι _ _) (lift-ι _ _)) <* _)
                 (map↦ (lift f) tr))
map↦ {a = bout x₁} f (res {P = P} {P' = P'} {a = .(bout x₁)} tr) =
  transport (cong₂ (_[_]↦_ _) refl
                   (cong ν
                         (mapmapPi _ _ P'
                          ∙ (cong mapPi (funExt \ x → sym (swap-lift _ x)) <* P')
                          ∙ sym (mapmapPi _ _ P'))))
            (res (transport (cong (_[_]↦_ _) (cong bout (lift-ι f x₁)) <* _) (map↦ (lift f) tr)))
map↦ {a = binp x₁} f (res {P = P} {P' = P'} {a = .(binp x₁)} tr) =
  transport (cong₂ (_[_]↦_ _) refl
                   (cong ν
                         (mapmapPi _ _ P'
                          ∙ (cong mapPi (funExt \ x → sym (swap-lift _ x)) <* P')
                          ∙ sym (mapmapPi _ _ P'))))
            (res (transport (cong (_[_]↦_ _) (cong binp (lift-ι f x₁)) <* _) (map↦ (lift f) tr)))
map↦ {a = inp x x₁} f (res {P = P} {a = .(inp x x₁)} tr) =
  res (transport (cong (_[_]↦_ _) (cong₂ Label.inp (lift-ι _ _) (lift-ι _ _)) <* _)
                 (map↦ (lift f) tr))
map↦ {a = τ} f (res {P = P} {a = .τ} tr) = res (map↦ (lift f) tr)
map↦ f (opn tr) =
  opn (transport (cong₂ _[_]↦_ refl (cong₂ Label.out (lift-ι f _) (lift-fresh f)) <* _)
                 (map↦ (lift f) tr))
map↦ {a = a} f (conv tr x x₁) = conv (map↦ f tr) (map≈ f x) (map≈ (labelRen a _ f) x₁)
