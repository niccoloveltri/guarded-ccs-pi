
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
open import Basic
open import AbsNames
open import LaterPrims hiding (_∙_)

module ccs.semantics.FullAbstraction (ns : Names) where

open Names ns
open OpNames ns
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma
open import ccs.Syntax ns
open import ccs.Algebra ns
open import ccs.semantics.Algebra ns
open import ccs.semantics.Coalgebra ns
open import ccs.Bisim ns


-- Full abstraction: bisimilarity of two CCS-terms p and q is
-- equivalent to the path equality of their interpretation in Proc via
-- the map eval.


-- First, bisimilarity is equivalent to path equality.
module Bisim-≡ where

  open CoalgebraCCS'
  module BR = BisimRel stepRel
  open BR
  open BR.Bisim
  open BR.BisimF
  open BR.SimF
  open Eval'

  bisim-≡ : ∀ n → (p q : CCS n) → Bisim n p q → eval n p ≡ eval n q
  bisim-≡ = fix lem
    where
      lem : ▹ (∀ n → (p q : CCS n) → Bisim n p q → eval n p ≡ eval n q) → ∀ n (p q : CCS n) → Bisim n p q → eval n p ≡ eval n q
      lem ih n x y x∼y
        = cong (λ f → f n x) (fix-eq eval-fun)
        ∙ cong (Fold) (P∞-ext {Step (λ m → ▸ (λ α → Proc m)) n} (Lem.lem' x y h1  ,  Lem.lem' y x h2))
        ∙ cong (λ f → f n y) (sym (fix-eq (eval-fun)))
        where
          h1 : SimF (λ α n₁ x' y' → eval n₁ x' ≡ eval n₁ y') n x y
          sim h1 a p' m = PT.map (\ { (q' , m' , bsim) → q' , (m' , (\ α → ih α _ _ _ (bsim α))) }) (x∼y .uncon .fwd .sim a p' m)

          h2 : SimF (λ α n₁ x' y' → eval n₁ x' ≡ eval n₁ y') n y x
          sim h2 a p' m = PT.map (\ { (q' , m' , bsim) → q' , (m' , (\ α → ih α _ _ _ (bsim α))) }) (x∼y .uncon .bwd .sim a p' m)

          module Lem (x y : CCS n)
                     (h : SimF (\ α n x' y' → eval n x' ≡ eval n y') n x y) where

            lem' : mapP∞ {B = Step (λ m → ▸ (λ α → Proc m)) n} (λ x → (x .theLabel , λ α → eval n (x .theX)) ) (step x) ⊂ mapP∞ (λ x → (x .theLabel , λ α → eval n (x .theX))) (step y)
            lem' sp m = PT.rec (snd (sp ∈ mapP∞ (λ x → (x .theLabel , λ α → eval n (x .theX))) (step y)))  help  r
              where
                r = mapP∞-out (λ { q → q .theLabel , λ α → eval n (q .theX) }) sp (step x) m
                help : Σ (Step CCS n)
                         (λ a → ⟨ a ∈ step x ⟩ × (sp ≡ (a .theLabel , λ α → eval n (a .theX)))) →
                       fst (sp ∈ mapP∞ (λ x → (x .theLabel , λ α → eval n (x .theX))) (step y))
                help ((a , x') , m' , eq) = PT.rec (snd (sp ∈ mapP∞ (λ x → (x .theLabel , λ α → eval n (x .theX))) (step y)))
                                                     (\ { (y' , m'' , eq') →
                                                     PT.rec (snd (sp ∈ mapP∞ (λ x → (x .theLabel , λ α → eval n (x .theX))) (step y)))
                                                (\ { (q , q' , _ , qc , r' , q'c , m'') →

                                                  let ∈stepy = mapP∞-in {B = Step (\ n → ▹ (Proc n)) n} (λ x → x .theLabel , λ α → eval n (x .theX))
                                                                                  (a , _) (step q) m'' in
                                                         transport (cong (λ x → ⟨ x ∈ mapP∞ (λ x → (x .theLabel , λ α → eval n (x .theX))) (step y) ⟩)
                                                                     (cong′ (a ,_) (later-ext \ α → sym (eq' α)) ∙ sym eq))
                                                                     (subst (λ x → ⟨ (a , (λ α → eval n (x α))) ∈ mapP∞ (λ z → z .theLabel , (λ α → eval n (z .theX))) (step y) ⟩)
                                                                            (sym r')
                                                                            (transport (cong ⟨_⟩ (cong₂ _∈_ (cong′ (a ,_) (later-ext \ α → sym (eval-≈ (q'c))))
                                                                              (λ i → Unfold ((sym (fix-eq eval-fun <* _ <* q) ∙ sym (eval-≈ qc) ∙ (fix-eq eval-fun <* _ <* y)) i))))  ∈stepy ))
                                                }) m''

                                                     })
                                                     (h .sim a (next x') ∣ x , _ , _ , refl≈ , refl , (refl≈ , m') ∣₁)




  ≡-bisim : ∀ n → (p q : CCS n) → eval n p ≡ eval n q → Bisim n p q
  ≡-bisim = fix \ r n p q eq → con (conB (lem r n p q eq) (lem r n q p (sym eq)))
    where
      module BR' = BisimRel stepRel'
      open BR'.SimF
      lem-old : ▹ (∀ n (p q : CCS n) → eval n p ≡ eval n q → Bisim n p q) → ∀ n (p q : CCS n) → eval n p ≡ eval n q → BR'.SimF (\ α _ p q → eval _ p ≡ eval _ q) n p q
      lem-old ih n p q e .sim a _ (p' , r , ap'∈stepp) =
        subst (λ x →  ∥ Σ (▹ CCS n) (λ q' → Σ (CCS n) (λ Q' → (next Q' ≡ q') × typ ((a , Q') ∈ step q)) × (▸ (λ α → eval n (x α) ≡ eval n (q' α)))) ∥₁)
              r
              (PT.map lem' 
                      (mapP∞-out (λ x → x .theLabel , λ _ → eval _ (x .theX)) (a , (λ α → eval _ (p'))) (step q) a⟦p'⟧∈stepq))
        where
          a⟦p'⟧∈stepp = mapP∞-in {B = Step (\ n → ▹ Proc n) n} (λ x → x .theLabel , λ _ → eval n (x .theX)) (a , p') (step p)
                                                     ap'∈stepp
          a⟦p'⟧∈stepq = transport (cong′
                                                                (λ x → ⟨ (a , \ _ → eval _ p') ∈ x ⟩)
                                                                (sym (cong (λ x → Unfold (x n p)) (fix-eq (eval-fun)))
                                                                ∙ (λ i → Unfold (e i))
                                                                ∙ cong (λ x → Unfold (x n q)) (fix-eq (eval-fun))))
                                                           a⟦p'⟧∈stepp
          lem' : Σ (Step CCS n)
                      (λ a₁ →
                         ⟨ a₁ ∈ step q ⟩ ×
                         ((a , (λ α → eval n (p'))) ≡
                          (a₁ .theLabel , λ α → eval _ (a₁ .theX)))) →
                      Σ (▹ CCS n)
                      (λ q' → (Σ _ \ Q' → (next Q' ≡ q') × ⟨ (a , Q') ∈ step q ⟩) × (▸ (λ α → eval _ p' ≡ eval _ (q' α))))
          lem' ((a' , q') , aq'∈stepq , e') =
                 J {_} {Act n}
                   (λ a eq →
                      (q' : CCS n) (aq'∈stepq : ⟨ (a' , q') ∈ step q ⟩)
                      (e' : ▸ \ α → eval _ p' ≡ eval _ q') →
                      Σ (▹ CCS n) (λ q'' → (Σ _ \ Q' → (next Q' ≡ q'') × ⟨ (a , Q') ∈ step q ⟩) × (▸ (λ α → eval _ (p') ≡ eval _ (q'' α)))))
                   (\ q' aq'∈stepq e' → next q' , (_ , refl , aq'∈stepq) , e')
                   (sym (cong′ theLabel e'))
                   q' aq'∈stepq
                   (λ α i → cong′ theX e' i α)
                   
      lem : ▹ (∀ n (p q : CCS n) → eval n p ≡ eval n q → Bisim n p q) → ∀ n (p q : CCS n) → eval n p ≡ eval n q → SimF (\ α → Bisim) n p q
      lem ih n p q e .sim a p' = PT.rec squash₁ \ { (Q , Q' , Q'' , Qc , r , Q'c ,  ap'∈stepp) →
                                     lem-old ih n Q q (sym (eval-≈ Qc) ∙ e) .sim a (λ _ → Q'') (Q'' , refl , ap'∈stepp) >>PT
                                       \ { (q' , (q'' , r' , m) , e') →
                                         subst (λ x →  ∥ Σ (▹ CCS n) (λ q''' → stepRel q a q''' × (▸ (λ α → Bisim n (x α) (q''' α)))) ∥₁)
                                               (sym r)
                                               ∣ q' , ∣ q , _ , _ , refl≈ , sym r' , refl≈ , m ∣₁ ,
                                                     (λ α → ih α _ (next Q' α) (q' α) (eval-≈ Q'c ∙ e' α)) ∣₁ }
                                         }

open BisimRel piRel
open Bisim-≡

-- Full abstraction
fullAbstract : ∀ {n} (P Q : CCS n) → Bisim n P Q ≡ (evalX ProcCCS-alg P ≡ evalX ProcCCS-alg Q)
fullAbstract {n} P Q =
  Bisim n P Q
    ≡⟨ cong (λ f → f n P Q) (cong (BisimRel.Bisim) 
        (ifunExt \ _ → funExt (λ _ → funExt λ _ → funExt λ _ →
          cong fst (⇔toPath {P = _ , squash₁} {Q = _ , squash₁} (opsem→∈step2 _ _ _) (∈step→opsem2 _ _ _))))) ⟩
  BR.Bisim n P Q
    ≡⟨ cong′ fst (⇔toPath {P = _ , BR.isPropBisim}{Q = _ , isSetProc _ _ _}
             (λ b → (sym (evalG-eq P) ∙ Eval'.eval-eq' P) ∙ bisim-≡ n P Q b ∙ sym (Eval'.eval-eq' Q) ∙ evalG-eq Q)
             (λ eq → ≡-bisim n P Q (sym (Eval'.eval-eq' P) ∙ evalG-eq P ∙ eq ∙ sym (evalG-eq Q) ∙ Eval'.eval-eq' Q))) ⟩
  (evalX ProcCCS-alg P ≡ evalX ProcCCS-alg Q)
    ∎
