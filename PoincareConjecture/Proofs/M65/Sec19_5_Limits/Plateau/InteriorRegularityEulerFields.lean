import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerVariation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerEulerFields

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped Topology ContDiff SchwartzMap

namespace PoincareConjecture.M65Euler

def variationValue {N : ℕ} (X : LoopPlane → EuclideanSpace ℝ (Fin N))
    (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (φ : 𝓢(LoopPlane, ℝ)) (t : ℝ) (z : LoopPlane) : EuclideanSpace ℝ (Fin N) :=
  X z + t • (φ z • V (X z))

def variationField {N : ℕ} (X : LoopPlane → EuclideanSpace ℝ (Fin N))
    (A : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N))
    (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (φ : 𝓢(LoopPlane, ℝ)) (t : ℝ) (i : Fin 2) (z : LoopPlane) :
    EuclideanSpace ℝ (Fin N) :=
  A i z + t • (φ z • fderiv ℝ V (X z) (A i z) +
    fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) • V (X z))

def weak_variation_on_ball {N : ℕ} {S : Set LoopPlane}
    (X : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin N) => y) S)
    (hS : IsOpen S) (x : LoopPlane) {R : ℝ} (hR : 0 ≤ R)
    (hRS : closedBall x R ⊆ S)
    (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hV : ContDiff ℝ 1 V) (C : NNReal) (hC : ∀ y, ‖fderiv ℝ V y‖ ≤ (C : ℝ))
    (φ : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ ball x R)
    (t : ℝ) : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin N) => y) (ball x R) :=
  compact_variation (restrict_map X (ball_subset_closedBall.trans hRS))
    (compose_on_ball X hS x hR hRS V hV C hC) φ hc hs t

theorem exists_variation_capture {N : ℕ} {S : Set LoopPlane}
    (X : LoopPlane → EuclideanSpace ℝ (Fin N))
    (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hV : Continuous V) (φ : 𝓢(LoopPlane, ℝ)) (hc : HasCompactSupport φ)
    (a : EuclideanSpace ℝ (Fin N)) {ε : ℝ} (hε : 0 < ε)
    (hX : MapsTo X S (ball a (ε / 2))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      MapsTo (variationValue X V φ t) S (ball a ε) := by
  obtain ⟨K, hK⟩ := hc.exists_bound_of_continuous φ.continuous
  obtain ⟨L, hL⟩ := (isCompact_closedBall a (ε / 2)).exists_bound_of_continuousOn hV.continuousOn
  let B := max K 0 * max L 0
  have hB : 0 ≤ B := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  obtain ⟨δ, hδ, hδB⟩ := exists_pos_mul_lt (half_pos hε) B
  refine ⟨δ, hδ, ?_⟩
  intro t ht z hz
  have hXz := hX hz
  have hφ : ‖φ z‖ ≤ max K 0 := (hK z).trans (le_max_left _ _)
  have hVz : ‖V (X z)‖ ≤ max L 0 :=
    (hL (X z) (ball_subset_closedBall hXz)).trans (le_max_left _ _)
  have hpert : ‖t • (φ z • V (X z))‖ ≤ B * |t| := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |t| * (max K 0 * max L 0) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hφ hVz (norm_nonneg _) (le_max_right _ _))
          (abs_nonneg _)
      _ = _ := mul_comm _ _
  have hpε : ‖t • (φ z • V (X z))‖ < ε / 2 :=
    hpert.trans_lt ((mul_le_mul_of_nonneg_left ht.le hB).trans_lt hδB)
  have hd : dist (variationValue X V φ t z) (X z) = ‖t • (φ z • V (X z))‖ := by
    simp only [dist_eq_norm, variationValue, add_sub_cancel_left]
  have htri := dist_triangle (variationValue X V φ t z) (X z) a
  rw [hd] at htri
  change dist (variationValue X V φ t z) a < ε
  have hxε : dist (X z) a < ε / 2 := hXz
  linarith

end PoincareConjecture.M65Euler
