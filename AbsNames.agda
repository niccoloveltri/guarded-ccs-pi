{-# OPTIONS --cubical #-}

module AbsNames where

open import Cubical.Core.Everything
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat
open import Cubical.Data.List hiding (snoc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Foundations.Everything hiding (assoc;lift)
open import Cubical.HITs.PropositionalTruncation as PT 
open import Cubical.Relation.Nullary
open import Basic
open import CountablePowerSet

-- We take an abstract notion of name.
-- We assume given an enumerable infinite collection of names (the
-- "enum" field), so that "Name n" contains the first n names.
-- This could be easily intantiated to have Fin as the carrier.

record Names : Set₁ where
  field
    Name : ℕ → Set
    decName : ∀ {n} (x y : Name n) → Dec (x ≡ y)
    fresh : (n : ℕ) → Name (suc n)
    down : ∀ {n} (k : Name (suc n)) → (k ≡ fresh n → ⊥) → Name n
    down-inj : ∀ {n} (k k' : Name (suc n))
      → (p : k ≡ fresh n → ⊥) (p' : (k' ≡ fresh n → ⊥))
      → down k p ≡ down k' p' → k ≡ k'
    ι : ∀ {n} → Name n → Name (suc n)
    ι-inj : ∀ {n} x y → ι {n} x ≡ ι y → x ≡ y
    enum : ∀ {n} → P∞ (Name n)
    fresh-ι : ∀ {n} {v : Name n} → ι v ≡ fresh n → ⊥
    down-ι : ∀ {n} {v : Name n} (¬p : ι v ≡ fresh n → ⊥) → down (ι v) ¬p ≡ v
    ι-down : ∀ {n} {v : Name (suc n)} (¬p : v ≡ fresh _ → ⊥) → ι (down v ¬p) ≡ v
    enum-eq : ∀ {n} (x : P∞ (Name n)) → enum {n} ≡ x ∪ enum {n}
    enum-fin : ∀ {n} → FinitelyPresented (enum {n})

  abstract
    dec∈ : ∀ {m} → (z : Name m) → (x : P∞ (Name m)) → FinitelyPresented x → Dec ⟨ z ∈ x ⟩
    dec∈ z x =
      PT.rec (isPropDec ((z ∈ x) .snd))
             (λ { (xs , p) → J (λ y eq → Dec (typ (z ∈ y))) (aux xs) p })
      where
        aux : ∀ xs → Dec ⟨ z ∈ fromList xs ⟩
        aux [] = no (\ ())
        aux (x ∷ xs) with decName z x | aux xs
        ... | yes p | _ = yes ∣ inl ∣ p ∣₁ ∣₁ 
        ... | no ¬p | yes r = yes ∣ inr (0 , r) ∣₁
        ... | no ¬p | no ¬r =
          no (PT.rec (\ ()) \ { (_⊎_.inl eq) → PT.rec (λ ()) ¬p eq; (_⊎_.inr (_ , m)) → ¬r m })


-- Operations on names

module OpNames (ns : Names) where
  open Names ns

-- Lifting a renaming acting on n to a renaming acting on n + 1.
  lift : ∀ {n m} → (Name n → Name m) → (Name (suc n) → Name (suc m))
  lift f v with decName v (fresh _)
  ... | yes _ = fresh _
  ... | no  ¬r = ι (f (down v ¬r))

-- Lifting a renaming on the embedding of a name v is the same as
-- embedding the renaming of v
  lift-ι : ∀ {n m} (f : Name n → Name m) (v : Name n) → lift f (ι v) ≡ ι (f v)
  lift-ι f v with decName (ι v) (fresh _)
  lift-ι f v | yes p = Empty.rec (fresh-ι p)
  lift-ι f v | no ¬p = cong ι (cong f (down-ι ¬p))

-- Lifting a renaming of a fresh name is just the fresh name.
  lift-fresh : ∀ {n m} (f : Name n → Name m) → lift f (fresh n) ≡ fresh m
  lift-fresh {n} f with decName (fresh n) (fresh n)
  lift-fresh {n} f | yes p = refl
  lift-fresh {n} f | no ¬p = Empty.rec (¬p refl)
  
  lift-is-ι : ∀ {n m} (f : Name n → Name m) (v : Name (suc n)) y → lift f v ≡ ι y → Σ (Name n) λ v' → f v' ≡ y
  lift-is-ι f v y eq with decName v (fresh _)
  lift-is-ι f v y eq | yes p = Empty.rec (fresh-ι (sym eq))
  lift-is-ι f v y eq | no ¬p = down v ¬p , ι-inj _ _ eq
  
  for-fresh : ∀ {n} → Name n → Name (suc n) → Name n
  for-fresh z y with decName y (fresh _)
  for-fresh z y | yes p = z
  for-fresh z y | no ¬p = down y ¬p

-- Injective renamings.
  InjRen : ℕ → ℕ → Set
  InjRen n m = Σ (Name n → Name m) \ f → ∀ x y → f x ≡ f y → x ≡ y

  Inj = InjRen


-- Many provable properties of renamings and their operations.
  idInj : ∀ {m} → Inj m m
  idInj = (λ x → x) , (λ x x₁ x₂ → x₂)
  
  _for-fresh_ = for-fresh
    
  image : ∀ {n m} (f : Name n → Name m) → P∞ (Name m)
  image f = mapP∞ f enum
  
  abstract  
    image-fn : ∀ {n m} (f : Name n → Name m) → FinitelyPresented (image f)
    image-fn f = map-fn {x = enum} enum-fin
  
    neg' : ∀ {m} → Name m → (x : P∞ (Name m)) → FinitelyPresented x → P∞ (Name m)
    neg' z x fn with dec∈ z x fn
    ... | yes _ = ø
    ... | no _ = η z

-- neg x is the complement of x
    neg : ∀ {m} → (x : P∞ (Name m)) → FinitelyPresented x → P∞ (Name m)
    neg x fn = bind enum \ z → neg' z x fn
  
    enum-in : ∀ {m} → (v : Name m) → ⟨ v ∈ enum ⟩
    enum-in v = subst (\ x → ⟨ v ∈ x ⟩) (sym (enum-eq (η v))) (∪-in-L {P = η v} {enum} (∣ refl ∣₁))
  
  
    neg-out : ∀ {m} → (z : Name m) → (x : P∞ (Name m)) (fn : FinitelyPresented x) → ⟨ z ∈ neg x fn ⟩ → ⟨ z ∈ x ⟩ → ⊥
    neg-out z x fn m m' = bind-out _ _  enum (m) >>⊥ aux
      where
        aux : Σ (Name _) (λ a → ⟨ a ∈ enum ⟩ × ⟨ z ∈ neg' a x fn ⟩) → ⊥
        aux (y , my , m) with dec∈ y x fn
        ... | yes eq = m
        ... | no ¬eq = m >>⊥ \ eq → ¬eq (subst (\ z → ⟨ z ∈ x ⟩) eq m')
  
    neg'-in : ∀ {m} → (z : Name m) → (x : P∞ (Name m)) (fn : _) → (⟨ z ∈ x ⟩ → ⊥) → neg' z x fn ≡ η z
    neg'-in z x fn ¬p with dec∈ z x fn
    ... | yes p = Empty.rec (¬p p)
    ... | no _ = refl
  
    neg-in : ∀ {m} → (z : Name m) → (x : P∞ (Name m)) (fn : _) → (⟨ z ∈ x ⟩ → ⊥) → ⟨ z ∈ neg x fn ⟩
    neg-in z x fn ¬p = bind-in _ _ enum (_ , enum-in z , subst (\ s → ⟨ z ∈ s ⟩) (sym (neg'-in z x fn ¬p)) ∣ refl ∣₁)
  
    neg-image-out : ∀ {n m v} → (z : Name m) → (f : Name n → Name m) → ⟨ z ∈ neg (image f) (image-fn f) ⟩ → z ≡ f v → ⊥
    neg-image-out z f m eq = neg-out z (image f) (image-fn f) m (subst (λ z → ⟨ z ∈ image f ⟩) (sym eq) (lemma-4·1-part1 _ _ enum (enum-in _)))
  
    neg-image-in : ∀ {n m} → (z : Name m) → (f : Name n → Name m) → (∀ v → z ≡ f v → ⊥) → ⟨ z ∈ neg (image f) (image-fn _) ⟩
    neg-image-in z f ¬p = neg-in z (image f) (image-fn f) (\ p → lemma-4·1-part2 _ _ enum p >>⊥ \ { (w , m , eq) → ¬p w eq } )
  
    neg-nat : ∀ {n m} (f : Inj n m) x fn → mapP∞ (fst f) (neg x fn) ⊂ neg (mapP∞ (fst f) x) (map-fn fn)
    neg-nat f x fn y m = neg-in y (mapP∞ (fst f) x) (map-fn fn) (\ m' → lemma-4·1-part2 _ _ (neg x fn) m >>⊥ \ { (w , m , eq) → lemma-4·1-part2 _ _ x m' >>⊥ \ { (w' , m' , eq') →
            neg-out _ x fn m (subst (\ w → ⟨ w ∈ x ⟩) (snd f _ _ (sym eq' ∙ eq)) m') } })
  
  
    neg-image-∘ : ∀ {n m o} (f : Inj m o) (g : Name n → Name m) → neg (image (λ x → fst f (g x))) (image-fn _) ≡ neg (image (fst f)) (image-fn _) ∪ mapP∞ (fst f) (neg (image (g)) (image-fn _))
    neg-image-∘ f g = P∞-ext (aux
                             , \ x m → PT.rec ((x ∈ neg (image (λ x → fst f (g x))) (image-fn _)) .snd)
                            (\ { (_⊎_.inl x) → neg-image-in _ (λ x₁ → fst f (g x₁)) (\ v eq → neg-image-out _ (fst f) x eq)
                               ; (_⊎_.inr (_ , m)) → transport (cong ⟨_⟩ (cong (x ∈_) (cong₂ neg (mapmapP∞ _ _ enum)
                                                                     (isOfHLevel→isOfHLevelDep 1 {B = FinitelyPresented} (λ _ → squash₁)
                                                                        _ _ (mapmapP∞ _ _ enum)))))
                                                               (neg-nat f (image (g)) (image-fn _) _ m) } ) m)
     where
      aux : neg (image (λ x → fst f (g x))) (image-fn _) ⊂ (neg (image (fst f)) (image-fn _) ∪ mapP∞ (fst f) (neg (image (g)) (image-fn _)))
      aux x m with dec∈ x (image (fst f)) (image-fn _)
      aux x m | yes p = ∣ inr (0 ,  PT.rec ((x ∈ mapP∞ (fst f) (neg (image (g)) (image-fn _))) .snd) (λ { (v , mv , eq) → subst (λ x → ⟨ x ∈ mapP∞ (fst f) (neg (image (g)) (image-fn _)) ⟩) (sym eq)
          (lemma-4·1-part1 _ _ (neg (image (g)) (image-fn _)) (neg-in v (image (g)) (image-fn _) (\ mv' →
            lemma-4·1-part2 _ _ enum mv' >>⊥ \ { (w , mw , eq') → neg-image-out _ _ m ((eq ∙ cong (fst f) eq'))  }  ))) }) (lemma-4·1-part2 _ _ enum p)  ) ∣₁
      aux x m | no ¬p = ∣ inl (neg-in x (mapP∞ (fst f) enum) (image-fn _) ¬p) ∣₁

    neg-image-id : ∀ {m} → neg (image (\ (x : Name m) → x)) (image-fn _) ≡ ø
    neg-image-id = P∞-ext ((\ x m → neg-out _ (image (\ x → x)) (image-fn _) m (lemma-4·1-part1 (λ x₁ → x₁) x enum (enum-in x))) , (\ _ ()))
  
    neg-image-lift : ∀ {n m} (f : Name n → Name m) → neg (image (lift f)) (image-fn _) ≡ mapP∞ ι (neg (image f) (image-fn _))
    neg-image-lift f = P∞-ext (aux , aux')
      where
        aux : neg (image (lift f)) (image-fn _) ⊂ mapP∞ ι (neg (image f) (image-fn _))
        aux x p with decName x (fresh _)
        aux x p | yes q = Empty.rec (neg-image-out x (lift f) p (q ∙ sym (lift-fresh f)))
        aux x p | no ¬q =
          subst (λ z → ⟨ z ∈ mapP∞ ι (neg (image f) (image-fn _)) ⟩)
                (ι-down ¬q)
                (lemma-4·1-part1 ι (down x ¬q) (neg (image f) (image-fn _)) (neg-image-in _ f (λ v r → neg-image-out x (lift f) p (sym (ι-down ¬q) ∙ cong ι r ∙ sym (lift-ι f v)))))
  
        aux' : mapP∞ ι (neg (image f) (image-fn _)) ⊂ neg (image (lift f)) (image-fn _)
        aux' x p = neg-image-in _ _ (λ v q → lemma-4·1-part2 ι x (neg (image f) (image-fn _)) p >>⊥ λ {(y , r , eq) → neg-image-out y f r (sym (lift-is-ι f v y (sym q ∙ eq) .snd)) })
  
    snoc : ∀ {n m} (f : Name n → Name m) (z : Name m) → Name (suc n) → Name m
    snoc f z v with decName v (fresh _)
    ... | yes _ = z
    ... | no ¬r = f (down v ¬r)
  
    snoc-ι : ∀ {n m} (f : Name n → Name m) (z : Name m) (v :  Name n) → snoc f z (ι v) ≡ f v
    snoc-ι f z v with decName (ι v) (fresh _)
    ... | yes r = Empty.rec (fresh-ι r)
    ... | no ¬r = cong f (down-ι ¬r)
  
    snoc-fresh : ∀ {n m} (f : Name n → Name m) (z : Name m) → snoc f z (fresh _) ≡ z
    snoc-fresh {n} f z with decName (fresh n) (fresh _)
    ... | yes r = refl
    ... | no ¬r = Empty.rec (¬r refl)
  
    snoc-for-fresh : ∀ {n} (v : Name n) → ∀ x → for-fresh v x ≡ snoc (\ z → z) v x
    snoc-for-fresh v x with decName x (fresh _)
    ... | yes _ = refl
    ... | no _ = refl
  
    snoc-inj : ∀ {n m} (f : Inj n m) (z : Name m) (mz : ⟨ z ∈ neg (image (fst f)) (image-fn _) ⟩) (v v' : Name (suc n)) → snoc (fst f) z v ≡ snoc (fst f) z v' → v ≡ v'
    snoc-inj f z mz v v' with decName v (fresh _) | decName v' (fresh _)
    snoc-inj f z mz v v' | yes p | yes p₁ = \ _ → p ∙ sym p₁
    snoc-inj f z mz v v' | yes p | no ¬p = \ eq → Empty.rec (neg-image-out z (fst f) mz eq)
    snoc-inj f z mz v v' | no ¬p | yes p = \ eq → Empty.rec (neg-image-out z (fst f) mz (sym eq))
    snoc-inj f z mz v v' | no ¬p | no ¬p₁ = \ eq → down-inj v v' ¬p ¬p₁ (snd f _ _ eq)
  
    snoc-lift : ∀ {n m o} (f : Name m → Name o)(g : Name n → Name m) z x →  snoc f z (lift g x) ≡ snoc (\ y → f (g y)) z x
    snoc-lift f g z x with decName x (fresh _)
    snoc-lift f g z x | yes p = snoc-fresh f z
    snoc-lift f g z x | no ¬p = snoc-ι f z (g (down x ¬p))
  
    snoc-∘ : ∀ {n m o} (f : Name m → Name o) (g : Name n → Name m) a v → f (snoc g a v) ≡ snoc (λ x → f (g x)) (f a) v
    snoc-∘ f g a v with decName v (fresh _)
    ... | yes p = refl
    ... | no ¬p = refl
  
    neg-image-ι : ∀ {n} → neg (image {n} ι) (image-fn _) ≡ η (fresh n)
    neg-image-ι {n} = P∞-ext (aux
      , (\ x eq → neg-in x (image ι) (image-fn _) (\ m → eq >>⊥ \ eq → lemma-4·1-part2 ι _ enum m >>⊥ \ {(a , ma , eq') → fresh-ι (sym eq' ∙ eq) })))
     where
       aux : neg (image ι) (image-fn _) ⊂ η (fresh n)
       aux x m with dec∈ x (image ι) (image-fn _) | decName x (fresh _)
       aux x m | yes p | _ = Empty.rec (lemma-4·1-part2 ι _ enum p >>⊥ \ { (_ , _ , eq) → neg-image-out _ ι m eq })
       aux x m | no ¬p | yes p = ∣ p ∣₁
       aux x m | no ¬p | no ¬p₁ = Empty.rec (¬p (subst (\ x → ⟨ x ∈ image ι ⟩) (ι-down ¬p₁)
           (lemma-4·1-part1 _ _ enum (enum-in (down x ¬p₁)))))
  
    neg-∪ : ∀ {n} {x : P∞ (Name n)}{fn} → x ∪ neg x fn ≡ enum
    neg-∪ {n} {x} {fn} = P∞-ext ((\ v m → enum-in v) , aux)
      where
        aux : enum ⊂ (x ∪ neg x fn)
        aux v m with dec∈ v x fn
        aux v m | yes p = ∪-in-L {P = x} {P' = neg x fn} p
        aux v m | no ¬p = ∪-in-R {P = x} {P' = neg x fn} (neg-in v x fn ¬p)
  
  swap : ∀ {n} → Name (suc (suc n)) → Name (suc (suc n))
  swap = snoc (snoc (\ x → ι (ι x)) (fresh _)) (ι (fresh _))
  
  abstract
    swap-inj : ∀ {n} (v v' : Name (suc (suc n))) → swap v ≡ swap v' → v ≡ v'
    swap-inj v v' p with decName v (fresh _) | decName v' (fresh _)
    swap-inj v v' p | yes p₁ | yes p₂ = p₁ ∙ sym p₂
    swap-inj v v' p | yes p₁ | no ¬p with decName (down v' ¬p) (fresh _)
    swap-inj v v' p | yes p₁ | no ¬p | yes p₂ = Empty.rec (fresh-ι p)
    swap-inj v v' p | yes p₁ | no ¬p | no ¬p₁ = Empty.rec (fresh-ι (ι-inj _ _ (sym p)))
    swap-inj v v' p | no ¬p | yes p₁ with decName (down v ¬p) (fresh _)
    swap-inj v v' p | no ¬p | yes p₁ | yes p₂ = Empty.rec (fresh-ι (sym p))
    swap-inj v v' p | no ¬p | yes p₁ | no ¬p₁ = Empty.rec (fresh-ι (ι-inj _ _ p))
    swap-inj v v' p | no ¬p | no ¬p₁ with decName (down v ¬p) (fresh _) | decName (down v' ¬p₁) (fresh _)
    swap-inj v v' p | no ¬p | no ¬p₁ | yes p₁ | yes p₂ = down-inj _ _ ¬p ¬p₁ (p₁ ∙ sym p₂)
    swap-inj v v' p | no ¬p | no ¬p₁ | yes p₁ | no ¬p₂ = Empty.rec (fresh-ι (sym p))
    swap-inj v v' p | no ¬p | no ¬p₁ | no ¬p₂ | yes p₁ = Empty.rec (fresh-ι p)
    swap-inj v v' p | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ = down-inj _ _ ¬p ¬p₁ (down-inj _ _ ¬p₂ ¬p₃ (ι-inj _ _ (ι-inj _ _ p)))
  
    swap-inv : ∀ {m} x → swap {m} (swap x) ≡ x
    swap-inv x with decName x (fresh _)
    ... | yes p = snoc-ι _ _ _ ∙ snoc-fresh _ _ ∙ sym p
    ... | no ¬p with decName (down x ¬p) (fresh _)
    ... | yes r = snoc-fresh _ _ ∙ sym (cong ι r) ∙ ι-down ¬p
    ... | no ¬r = snoc-ι _ _ _ ∙ snoc-ι _ _ _ ∙ cong ι (ι-down ¬r) ∙ ι-down ¬p
  
    neg-image-swap : ∀ {m} → neg (image (swap {m})) (image-fn _) ≡ ø
    neg-image-swap = P∞-ext ((\ x m → neg-out _ (image swap) (image-fn _) m (subst (λ x → ⟨ x ∈ image swap ⟩) (swap-inv x)
      (lemma-4·1-part1 swap (swap x) enum (enum-in (swap x))))) , (\ _ ()))
  
    snoc-lift-ι : ∀ {n m} (f : Name n → Name m) (z : Name m) (v :  Name (suc (suc n))) →
      snoc (lift f) (ι z) v ≡ lift (snoc f z) (swap v)
    snoc-lift-ι f z v with decName v (fresh _)
    snoc-lift-ι {n} f z v | yes p with decName (ι (fresh n)) (fresh _)
    snoc-lift-ι f z v | yes p | yes p₁ = Empty.rec (fresh-ι p₁)
    snoc-lift-ι f z v | yes p | no ¬p with decName (down (ι (fresh _)) ¬p) (fresh _)
    snoc-lift-ι {_} f z v | yes p | no ¬p | yes p₁ = refl
    snoc-lift-ι {_} f z v | yes p | no ¬p | no ¬p₁ = Empty.rec (¬p₁ (down-ι ¬p))
    snoc-lift-ι f z v | no ¬p with decName (down v ¬p) (fresh _)
    snoc-lift-ι {n} f z v | no ¬p | yes p with decName (fresh (suc n)) (fresh (suc n))
    snoc-lift-ι {n} f z v | no ¬p | yes p | yes p₁ = refl
    snoc-lift-ι {n} f z v | no ¬p | yes p | no ¬p₁ = Empty.rec (¬p₁ refl)
    snoc-lift-ι f z v | no ¬p | no ¬p₁ with decName (ι (ι (down (down v ¬p) ¬p₁))) (fresh _)
    snoc-lift-ι f z v | no ¬p | no ¬p₁ | yes p = Empty.rec (¬p (sym (cong ι (ι-down ¬p₁) ∙ ι-down ¬p) ∙ p))
    snoc-lift-ι f z v | no ¬p | no ¬p₁ | no ¬p₂ with decName (down (ι (ι (down (down v ¬p) ¬p₁))) ¬p₂) (fresh _)
    snoc-lift-ι f z v | no ¬p | no ¬p₁ | no ¬p₂ | yes p = Empty.rec (fresh-ι (sym (down-ι ¬p₂) ∙ p))
    snoc-lift-ι f z v | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ =
      cong ι (cong f (cong₂ down (sym (down-ι ¬p₂ ∙ ι-down ¬p₁)) (isProp→PathP' {B = \ x → x ≡ fresh _ → ⊥} (\ x → propPi (\ _ → isProp⊥)) _ _ _)))
  
  swap-ιι : ∀ {n} (v : Name n) → swap (ι (ι v)) ≡ ι (ι v)
  swap-ιι v = snoc-ι _ _ (ι v) ∙ snoc-ι _ _ v
  
  swapswap : ∀ {n} (v : Name (suc (suc n))) → swap (swap v) ≡ v
  swapswap v with decName v (fresh _)
  ... | yes p = cong swap (cong swap p ∙ snoc-fresh _ _) ∙ snoc-ι _ _ _ ∙ snoc-fresh _ _ ∙ sym p
  ... | no ¬p with decName (down v ¬p) (fresh _)
  ... | yes r = cong swap (cong swap (sym (ι-down ¬p)) ∙ snoc-ι _ _ _ ∙ cong (snoc _ _) r ∙ snoc-fresh _ _) ∙ snoc-fresh _ _ ∙ cong ι (sym r) ∙ ι-down ¬p
  ... | no ¬r = cong swap (cong swap (sym (ι-down ¬p)) ∙ snoc-ι _ _ _ ∙ cong (snoc _ _) (sym (ι-down ¬r)) ∙ snoc-ι _ _ _) ∙ swap-ιι _ ∙ cong ι (ι-down ¬r) ∙ ι-down ¬p
  
  
  lift-inj : ∀ {n m} → (f : Inj n m) → ∀ x y → lift (fst f) x ≡ lift (fst f) y → x ≡ y
  lift-inj f x y eq with decName x (fresh _) | decName y (fresh _)
  lift-inj f x y eq | yes p | yes p₁ = p ∙ sym p₁
  lift-inj f x y eq | yes p | no ¬p = Empty.rec (fresh-ι (sym eq))
  lift-inj f x y eq | no ¬p | yes p = Empty.rec (fresh-ι eq)
  lift-inj f x y eq | no ¬p | no ¬p₁ = down-inj _ _ _ _ (f .snd _ _ (ι-inj _ _ eq))
  
  liftlift : ∀ {l m n} (f : Name m → Name n) (g : Name l → Name m) (v : Name (suc l)) → lift f (lift g v) ≡ lift (\ x → f (g x)) v
  liftlift f g v with decName v (fresh _)
  liftlift {m = m} f g v | yes p with decName (fresh m) (fresh m)
  liftlift {m = m} f g v | yes p | yes p₁ = refl
  liftlift {m = m} f g v | yes p | no ¬p = Empty.rec (¬p refl)
  liftlift f g v | no ¬p with decName (ι (g (down v ¬p))) (fresh _)
  liftlift f g v | no ¬p | yes p = Empty.rec (fresh-ι p)
  liftlift f g v | no ¬p | no ¬p₁ = cong ι (cong f (down-ι ¬p₁))
  
  for-fresh-lift' : ∀ n m (f : Name n → Name m) z x → f (for-fresh z x) ≡ (for-fresh (f z) (lift (f) x))
  for-fresh-lift' n m f z x with decName x (fresh n)
  for-fresh-lift' n m f z x | yes p with decName (fresh m) (fresh m)
  for-fresh-lift' n m f z x | yes p | yes p₁ = refl
  for-fresh-lift' n m f z x | yes p | no ¬p = Empty.rec (¬p refl)
  for-fresh-lift' n m f z x | no ¬p with decName (ι (f (down x ¬p))) (fresh m)
  for-fresh-lift' n m f z x | no ¬p | yes p = Empty.rec (fresh-ι p)
  for-fresh-lift' n m f z x | no ¬p | no ¬p₁ = sym (down-ι ¬p₁)
  
  for-fresh-lift : ∀ n m (f : Inj n m) z x → fst f (for-fresh z x) ≡ (for-fresh (fst f z) (lift (fst f) x))
  for-fresh-lift n m (f , _) z x = for-fresh-lift' n m f z x
  
  lift-id : ∀ {n} v → lift {n} (\ x → x) v ≡ v
  lift-id v with decName v (fresh _)
  ... | yes p = sym p
  ... | no ¬p = ι-down ¬p
  
  abstract
    swap-lift : ∀ {n m} (f : Name n → Name m) (v : Name (suc (suc n))) → lift (lift f) (swap v) ≡ swap (lift (lift f) v)
    swap-lift f v with decName v (fresh _)
    swap-lift {n}{m} f v | yes p with decName (fresh (suc m)) (fresh (suc m)) | decName (ι (fresh n)) (fresh _)
    swap-lift {n} {m} f v | yes p | yes p₁ | yes p₂ = Empty.rec (fresh-ι p₂)
    swap-lift {n} {m} f v | yes p | yes p₁ | no ¬p = cong ι (cong (lift f) (down-ι ¬p) ∙ lift-fresh _)
    swap-lift {n} {m} f v | yes p | no ¬p | r = Empty.rec (¬p refl)
    swap-lift f v | no ¬p with decName (down v ¬p) (fresh _)
    swap-lift {n} f v | no ¬p | yes p with decName (fresh (suc n)) (fresh (suc n))
    swap-lift {n}{m} f v | no ¬p | yes p | yes p₁ with decName (ι (fresh m)) (fresh (suc m))
    swap-lift {n} {m} f v | no ¬p | yes p | yes p₁ | yes p₂ = Empty.rec (fresh-ι p₂)
    swap-lift {n} {m} f v | no ¬p | yes p | yes p₁ | no ¬p₁ with decName (down (ι (fresh m)) ¬p₁) (fresh m)
    swap-lift {n} {m} f v | no ¬p | yes p | yes p₁ | no ¬p₁ | yes p₂ = refl
    swap-lift {n} {m} f v | no ¬p | yes p | yes p₁ | no ¬p₁ | no ¬p₂ = Empty.rec (¬p₂ (down-ι ¬p₁))
    swap-lift {n} f v | no ¬p | yes p | no ¬p₁ = Empty.rec (¬p₁ refl)
    swap-lift f v | no ¬p | no ¬p₁ with decName (ι (ι (down (down v ¬p) ¬p₁))) (fresh _)
    swap-lift f v | no ¬p | no ¬p₁ | yes p = Empty.rec (fresh-ι p)
    swap-lift f v | no ¬p | no ¬p₁ | no ¬p₂ with decName (down (ι (ι (down (down v ¬p) ¬p₁))) ¬p₂) (fresh _)
    swap-lift f v | no ¬p | no ¬p₁ | no ¬p₂ | yes p = Empty.rec (fresh-ι (sym (down-ι ¬p₂) ∙ p))
    swap-lift f v | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ with decName (ι (ι (f (down (down v ¬p) ¬p₁)))) (fresh _)
    swap-lift f v | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ | yes p = Empty.rec (fresh-ι p)
    swap-lift f v | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ | no ¬p₄ with decName (down (ι (ι (f (down (down v ¬p) ¬p₁)))) ¬p₄) (fresh _)
    swap-lift f v | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ | no ¬p₄ | yes p = Empty.rec (fresh-ι (sym (down-ι ¬p₄) ∙ p))
    swap-lift f v | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ | no ¬p₄ | no ¬p₅ =
      cong ι (cong ι (cong f (cong₂ down (down-ι ¬p₂ ∙ ι-down ¬p₁) (isProp→PathP' {B = \ x → x ≡ fresh _ → ⊥} (\ x → propPi (\ _ → isProp⊥)) _ _ _))
                     ∙ sym (down-ι fresh-ι)
                     ∙ cong₂ down (sym (down-ι ¬p₄)) (isProp→PathP' {B = \ x → x ≡ fresh _ → ⊥} (\ x → propPi (\ _ → isProp⊥)) _ _ _)))
  
  abstract
    swap-lift-ι : ∀ {n} (v : Name (suc n)) → swap (lift ι v) ≡ ι v
    swap-lift-ι v with decName v (fresh _)
    swap-lift-ι {n} v | yes p with decName (fresh (suc n)) (fresh _)
    swap-lift-ι {n} v | yes p | yes p₁ = cong ι (sym p)
    swap-lift-ι {n} v | yes p | no ¬p = Empty.rec (¬p refl)
    swap-lift-ι v | no ¬p with decName (ι (ι (down v ¬p))) (fresh _)
    swap-lift-ι v | no ¬p | yes p = Empty.rec (fresh-ι p)
    swap-lift-ι v | no ¬p | no ¬p₁ with decName (down (ι (ι (down v ¬p))) ¬p₁) (fresh _)
    swap-lift-ι v | no ¬p | no ¬p₁ | yes p = Empty.rec (fresh-ι (sym (down-ι ¬p₁) ∙ p))
    swap-lift-ι v | no ¬p | no ¬p₁ | no ¬p₂ = cong ι (ι-down ¬p₂ ∙ down-ι ¬p₁ ∙ ι-down ¬p)
  
    swap-ι-lift : ∀ {n} (v : Name (suc n)) → swap (ι v) ≡ lift ι v
    swap-ι-lift v with decName v (fresh _)
    swap-ι-lift v | yes p with decName (ι v) (fresh _)
    swap-ι-lift v | yes p | yes p₁ = Empty.rec (fresh-ι p₁)
    swap-ι-lift v | yes p | no ¬p with decName (down (ι v) ¬p) (fresh _)
    swap-ι-lift v | yes p | no ¬p | yes p₁ = refl
    swap-ι-lift v | yes p | no ¬p | no ¬p₁ = Empty.rec (¬p₁ (down-ι ¬p ∙ p))
    swap-ι-lift v | no ¬p with decName (ι v) (fresh _)
    swap-ι-lift v | no ¬p | yes p =  Empty.rec (fresh-ι p)
    swap-ι-lift v | no ¬p | no ¬p₁ with decName (down (ι v) ¬p₁) (fresh _)
    swap-ι-lift v | no ¬p | no ¬p₁ | yes p = Empty.rec (¬p (sym (down-ι ¬p₁) ∙ p))
    swap-ι-lift v | no ¬p | no ¬p₁ | no ¬p₂ =
      cong ι (cong ι (cong₂ down (down-ι ¬p₁) (isProp→PathP' {B = \ x → x ≡ fresh _ → ⊥} (\ x → propPi (\ _ → isProp⊥)) _ _ _)))
  
    snoc-ι-fresh : ∀ {n} (v : Name (suc n)) → snoc ι (fresh n) v ≡ v
    snoc-ι-fresh v with decName v (fresh _)
    snoc-ι-fresh v | yes p = sym p
    snoc-ι-fresh v | no ¬p = ι-down ¬p
  
    lift-snoc : ∀ {n m} (f : Name n → Name m) (x : Name (suc n)) → lift f x ≡ snoc (\ x → ι (f x)) (fresh _) x
    lift-snoc f x with decName x (fresh _)
    ... | yes _ = refl
    ... | no  _ = refl
  
    f-snoc : ∀ {n m o} (f : Name m → Name o) {g : Name n → Name m} {v : _} (x : Name (suc n)) → f (snoc g v x) ≡ snoc (\ x → f (g x)) (f v) x
    f-snoc f x with decName x (fresh _)
    ... | yes _ = refl
    ... | no _ = refl
  
  lift-vs-swap : ∀ {n} → (x : Name (suc (suc (suc n)))) → lift swap (swap (lift swap x)) ≡ swap (lift swap (swap x))
  lift-vs-swap x = cong (lift swap) (cong swap (lift-snoc _ _)) ∙ lift-snoc _ _
                 ∙ f-snoc (snoc _ _) _ ∙ f-snoc (snoc _ _) _ ∙ cong (\ f → f x)
                   (cong₂ snoc (funExt \ x → snoc-ι _ _ _ ∙ f-snoc (snoc _ _) _ ∙ f-snoc (snoc _ _) _
                        ∙ cong (λ f → f x) (cong₂ snoc
                        (funExt \ y → f-snoc (snoc _ _) _ ∙ cong (λ f → f y)
                          (cong₂ snoc
                            (funExt \ z → snoc-ι _ _ _ ∙ snoc-ι _ _ _ ∙ cong ι (swap-ιι z))
                            (snoc-fresh _ _ ∙ snoc-fresh _ _)))
                        (snoc-ι _ _ _ ∙ snoc-ι _ _ _ ∙ cong ι (snoc-ι _ _ _ ∙ snoc-fresh _ _ ))))
                   (snoc-fresh _ _ ∙ snoc-ι _ _ _ ∙ cong ι (snoc-fresh _ _ ∙ refl)))
                 ∙ sym (cong swap (lift-snoc _ _) ∙ f-snoc (snoc _ _) _ ∙ f-snoc (snoc _ _) _ ∙ cong (\ f → f x) (cong₂ snoc
                   (funExt \ y → f-snoc (snoc _ _) _ ∙ cong (\ f → f y) (cong₂ snoc
                     (funExt \ z → snoc-ι _ _ _ ∙ snoc-ι _ _ _ ∙ f-snoc (snoc _ _) _ ∙ snoc-ι _ _ _ ∙ f-snoc (snoc _ _) _ ∙ cong (\ f → f z) (cong₂ snoc
                       (funExt \ w → snoc-ι _ _ _ ∙ refl)
                       (snoc-fresh _ _)))
                     (snoc-fresh _ _ ∙ snoc-fresh _ _ ∙ refl)))
                   (snoc-ι _ _ _ ∙ snoc-ι _ _ _ ∙ f-snoc (snoc _ _) _ ∙ snoc-fresh _ _ ∙ snoc-ι _ _ _ ∙ refl)))
  
  
