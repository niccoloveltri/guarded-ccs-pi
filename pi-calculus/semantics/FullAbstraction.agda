
{-# OPTIONS --cubical --guarded #-}

open import Cubical.Data.Sum hiding (inl; inr) 
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (lift;act)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Logic
open import Cubical.Relation.Nullary
open import CountablePowerSet
open import Cubical.Functions.FunExtEquiv
open import Basic
open import AbsNames
open import LaterPrims hiding (_∙_)

module pi-calculus.semantics.FullAbstraction (ns : Names) where

open Names ns
open OpNames ns
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma
open import pi-calculus.Syntax ns
open import pi-calculus.Algebra ns
open import pi-calculus.semantics.Algebra ns
open import pi-calculus.semantics.Coalgebra ns
open import pi-calculus.semantics.Model ns
open import pi-calculus.Bisim ns


-- Full abstraction: early congruence of two Pi-terms p and q is
-- equivalent to the path equality of their interpretation in PiMod via
-- the map evalGM.

module Bisim-≡ where

  open CoalgebraPi'
  module BR2 = BisimRel stepRel
  open BR2
  open BR2.Bisim
  open BR2.BisimF
  open BR2.SimF
  open Eval'

  bisim-≡ : ∀ n → (p q : Pi n) → Bisim n p q → eval n p ≡ eval n q
  bisim-≡ = fix lem
    where
      lem : ▹ (∀ n → (p q : Pi n) → Bisim n p q → eval n p ≡ eval n q) → ∀ n (p q : Pi n) → Bisim n p q → eval n p ≡ eval n q
      lem ih n x y x∼y
        = cong (λ f → f n x) (fix-eq eval-fun)
        ∙ cong (Fold) ((P∞-ext ( Lem.lem' x y h1  ,  Lem.lem' y x h2  )))
        ∙ cong (λ f → f n y) (sym (fix-eq (eval-fun)))
        where
          h1 : SimF (λ α n₁ x' y' → eval n₁ x' ≡ eval n₁ y') n x y
          sim h1 a p' m = PT.map (\ { (q' , m' , bsim) → q' , (m' , (\ α → ih α _ _ _ (bsim α))) }) (x∼y .uncon .fwd .sim a p' m)

          h2 : SimF (λ α n₁ x' y' → eval n₁ x' ≡ eval n₁ y') n y x
          sim h2 a p' m = PT.map (\ { (q' , m' , bsim) → q' , (m' , (\ α → ih α _ _ _ (bsim α))) }) (x∼y .uncon .bwd .sim a p' m)

          module Lem (x y : Pi n)
                     (h : SimF (\ α n x' y' → eval n x' ≡ eval n y') n x y) where

            lem' : mapF (\ m _ x → next (eval m x)) (step x) ⊂ mapF (\ m _ x → next (eval m x)) (step y)
            lem' sp m = PT.rec (snd (sp ∈ mapF (λ m _ x → next (eval m x)) (step y)))  help  r
              where
                r = mapP∞-out (λ { q → mapStep (\ m i x α → eval m x) q }) sp (step x) m
                help : Σ (Step Pi n)
                         (λ a → ⟨ a ∈ step x ⟩ × (sp ≡ mapStep (λ m₁ i x₁ α → eval m₁ x₁) a)) →
                       fst (sp ∈ mapF (λ m₁ _ x _ → eval m₁ x) (step y))
                help ((a , x') , m' , eq) = PT.rec (snd (sp ∈ mapF (λ m₁ _ x _ → eval m₁ x) (step y)))
                                                     (\ { (y' , m'' , eq') →
                                                     PT.rec (snd (sp ∈ mapF (λ m₁ _ x _ → eval m₁ x) (step y)))
                                                (\ { (q , q' , _ , qc , r , q'c , m'') →

                                                  let ∈stepy = mapP∞-in {B = Step (\ n → ▹ (Proc n)) n} (mapStep (\ m' i t α → eval m' (t)))
                                                                                  (a , _) (step q) m'' in
                                                         transport (cong (λ x → ⟨ x ∈ mapF ((\ m _ x α → eval m x)) (step y) ⟩)
                                                                     ((λ i → (a , λ α → eq' α (~ i))) ∙ sym eq))
                                                                     (transport (cong ⟨_⟩ (cong₂ _∈_ (cong′ (a ,_) (later-ext (λ α → sym (eval-≈ q'c) ∙ cong′ (eval _) (λ i → r (~ i) α))))
                                                                     (cong Unfold (sym (fix-eq eval-fun <* _ <* q) ∙ sym (eval-≈ qc) ∙ (fix-eq eval-fun <* _ <* y)))))  ∈stepy )
                                                }) m''

                                                     })
                                                     (h .sim a (next x') ∣ x , _ , _ , refl≈ , refl , (refl≈ , m') ∣₁)

  ≡-bisim : ∀ n → (p q : Pi n) → eval n p ≡ eval n q → Bisim n p q
  ≡-bisim = fix \ r n p q eq → con (conB (lem r n p q eq) (lem r n q p (sym eq)))
    where
      module BR' = BisimRel stepRel'
      open BR'.SimF
      lem-old : ▹ (∀ n (p q : Pi n) → eval n p ≡ eval n q → Bisim n p q) → ∀ n (p q : Pi n) → eval n p ≡ eval n q → BR'.SimF (\ α _ p q → eval _ p ≡ eval _ q) n p q
      lem-old ih n p q e .sim {m} a _ (p' , r , ap'∈stepp) =
        subst (λ z → ∥ Σ (▹ Pi m) (λ q' → stepRel' q a q' × (▸ (λ α → eval m (z α) ≡ eval m (q' α)))) ∥₁)
          r
          (PT.map lem' (mapP∞-out (mapStep \ _ _ x α → eval _ (x)) (a , (λ α → eval _ (p'))) (step q) a⟦p'⟧∈stepq))
        where
          a⟦p'⟧∈stepp = mapP∞-in {B = Step (\ n → ▹ Proc n) n} (mapStep \ _ _ x α → eval _ (x)) (a , p') (step p)
                                                     ap'∈stepp
          a⟦p'⟧∈stepq = transport (cong {x = mapF (\ _ _ x _ → eval _ x) (step p)} {mapF (\ _ _ x _ → eval _ x) (step q)}
                                                                (λ x → ⟨ (a , \ _ → eval _ p') ∈ x ⟩)
                                                                (sym (cong (λ x → Unfold (x n p)) (fix-eq (eval-fun)))
                                                                ∙ cong (Unfold) e
                                                                ∙ cong (λ x → Unfold (x n q)) (fix-eq (eval-fun))))
                                                           a⟦p'⟧∈stepp
          lem' : Σ (Step Pi n)
                      (λ a₁ →
                         ⟨ a₁ ∈ step q ⟩ ×
                         ((a , (λ α → eval m (p'))) ≡
                          mapStep {Y = (\ n → ▹ Proc n)} (λ z _ x α → eval z x) a₁)) →
                      Σ (▹ Pi m)
                      (λ q' → (Σ _ \ Q' → (next Q' ≡ q') × ⟨ (a , Q') ∈ step q ⟩) × (▸ (λ α → eval _ p' ≡ eval _ (q' α))))
          lem' ((a' , q') , aq'∈stepq , e') =
                 J {_} {Σ ℕ λ m' → Label n m'}
                   (λ m'a eq →
                      (q' : Pi (m'a .fst)) (aq'∈stepq : ⟨ (m'a .snd , q') ∈ step q ⟩)
                      (e'
                       : ▸ \ α → PathP (\ i → Proc (eq i .fst)) (eval _ p') (eval _ (q'))) →
                      Σ (▹ Pi m)
                      (λ q'' →
                         (Σ _ \ Q' → (next Q' ≡ q'') × ⟨ (a , Q') ∈ step q ⟩) × (▸ (λ α → eval _ (p') ≡ eval _ (q'' α)))))
                   (\ q' aq'∈stepq e' → next q' , (_ , refl , aq'∈stepq) , e')
                   (cong (\ ap → _ , theLabel ap) e') q' aq'∈stepq (\ α i → e' i .theX α)
      lem : ▹ (∀ n (p q : Pi n) → eval n p ≡ eval n q → Bisim n p q) → ∀ n (p q : Pi n) → eval n p ≡ eval n q → SimF (\ α → Bisim) n p q
      lem ih n p q e .sim {m} a p' = 
        PT.rec squash₁ \ { (Q , Q' , Q'' , Qc , r' , Q'c ,  ap'∈stepp) →
                                     lem-old ih n Q q (sym (eval-≈ Qc) ∙ e) .sim _ (λ _ → Q'') (Q'' , refl , ap'∈stepp) >>PT
                                       \ { (q' , (q'' , r'' , m) , e') →
                                         ∣ q' , ∣ q , (_ , (_ , (refl≈ , (sym r'' , (refl≈ , m))))) ∣₁
                                         , (\ α → ih α _ (p' α) (q' α) ((λ i → eval _ (r' i α)) ∙ eval-≈ Q'c ∙ e' α)) ∣₁  }
                                           }

open BisimRel piRel
open Bisim-≡
open PiMod

EarlyCong : ∀ {n} → Pi n → Pi n → Set
EarlyCong P Q = ∀ m (σ : Name _ → Name m) → Bisim m (mapPi σ P) (mapPi σ Q)

fullAbstract : ∀ {n} (P Q : Pi n) → EarlyCong P Q ≡ (evalGM P ≡ evalGM Q)
fullAbstract {n} P Q =
  (∀ m ρ → Bisim m (mapPi ρ P) (mapPi ρ Q))
    ≡⟨ (Π= \ m → Π= \ σ → cong (BisimRel.Bisim) (ifunExt (\ _ → ifunExt \ _ → funExt \ _ → funExt \ _ → funExt \ _ →
           cong fst (⇔toPath {P = _ , squash₁} {Q = _ , squash₁} (opsem→∈step2 _ _ _) (∈step→opsem2 _ _ _)))) <* _ <* _ <* _) ⟩
  (∀ m ρ → BR2.Bisim m (mapPi ρ P) (mapPi ρ Q))
    ≡⟨ (Π= \ m → Π= \ σ → cong fst (⇔toPath {P = _ , BR2.isPropBisim} {Q = _ , isSetProc _ _ _} (bisim-≡ m (mapPi σ P) (mapPi σ Q)) (≡-bisim m (mapPi σ P) (mapPi σ Q)))) ⟩
  (∀ m ρ → Eval'.eval m (mapPi ρ P) ≡ Eval'.eval m (mapPi ρ Q))
    ≡⟨ (Π= \ m → Π= \ σ → cong₂ _≡_ (sym (Eval'.eval-eq' (mapPi σ P))) (sym (Eval'.eval-eq' (mapPi σ Q)))) ⟩
  (∀ m ρ → Eval.eval m (mapPi ρ P) ≡ Eval.eval m (mapPi ρ Q))
    ≡⟨ (Π= \ m → Π= \ σ → cong₂ _≡_ (evalGM-eq P σ) (evalGM-eq Q σ)) ⟩
  (∀ m ρ → evalGM P .elem m ρ ≡ evalGM Q .elem m ρ)
    ≡⟨ (Π= \ m → funExtPath) ⟩
  (∀ m → evalGM P .elem m ≡ evalGM Q .elem m)
    ≡⟨ funExtPath ⟩
  (evalGM P .elem ≡ evalGM Q .elem)
    ≡⟨ cong fst (⇔toPath {P = _ , hLevelPi 2 (\ m → hLevelPi 2 \ σ → isSetProc m) _ _} {Q = _ , isSetPiMod _ _ _} PiMod-ext (cong elem)) ⟩
  (evalGM P ≡ evalGM Q)
    ∎
