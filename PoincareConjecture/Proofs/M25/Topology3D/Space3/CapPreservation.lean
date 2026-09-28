import PoincareConjecture.Proofs.M25.Topology3D.Space3.CapContractionFlow
import Mathlib.Analysis.SpecialFunctions.Log.Basic











set_option autoImplicit false

open Set Metric
open scoped InnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (χ : ℝ → ℝ) (hχ : ∀ z, χ z ∈ Icc 0 1)
variable (hzero : ∀ z, z ≤ 1 / 2 → χ z = 0) (u : E) (hu : ‖u‖ = 1)
variable (f : E → E) {K L : ℝ≥0} (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
variable (hag : EqOn f (capContractionField χ u) (closedBall 0 1))

include hχ hzero hu hag



theorem capFlow_mapsTo_cap (a : ℝ) (ha : 0 ≤ a) (hone : ∀ z ∈ Icc a 1, χ z = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    MapsTo (fun x => boundedFlow f hK hL x t)
      {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ} {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ} := by
  intro x hx
  have hxball : x ∈ closedBall (0 : E) 1 := mem_closedBall_zero_iff.mpr hx.1.le
  let c := boundedFlow f hK hL x
  have hball (s : ℝ) (hs : 0 ≤ s) : ‖c s‖ ≤ 1 :=
    mem_closedBall_zero_iff.mp
      (capFlow_mapsTo_closedBall χ hχ hzero u hu f hK hL hag s hs hxball)
  have hz (s : ℝ) (hs : 0 ≤ s) : ⟪u, c s⟫_ℝ ∈ Icc a 1 := by
    constructor
    · have hm := capFlow_height_mono χ hχ hzero u hu f hK hL hag x hxball
        (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs) hs
      simp only [boundedFlow_zero] at hm
      exact hx.2.trans hm
    · have hi := real_inner_le_norm u (c s)
      rw [hu, one_mul] at hi
      exact hi.trans (hball s hs)
  have hd (s : ℝ) : HasDerivAt (fun v => ‖c v‖ ^ 2) (2 * ⟪c s, f (c s)⟫_ℝ) s :=
    (boundedFlow_hasDerivAt f hK hL x s).norm_sq
  have hmono : MonotoneOn (fun s => ‖c s‖ ^ 2) (Icc 0 t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t)
      (fun s _ => (hd s).continuousAt.continuousWithinAt)
      (fun s _ => (hd s).hasDerivWithinAt)
    intro s hs
    have hs0 : 0 ≤ s := (interior_subset hs).1
    have hbs := hball s hs0
    have hzs := hz s hs0
    rw [hag (mem_closedBall_zero_iff.mpr hbs), capContractionField_radial,
      capContractionCoefficient, hone _ hzs]
    have hn : 0 ≤ 1 - ‖c s‖ ^ 2 := by nlinarith [norm_nonneg (c s)]
    have hp := mul_nonneg (ha.trans hzs.1) hn
    nlinarith only [hp]
  have hsq := hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simp only [c, boundedFlow_zero, hx.1, one_pow] at hsq
  refine ⟨?_, (hz t ht).1⟩
  have hn := hball t ht
  change ‖c t‖ = 1
  change 1 ≤ ‖c t‖ ^ 2 at hsq
  nlinarith [norm_nonneg (c t)]



theorem capFlow_eventually_mapsTo_ball (eps : ℝ) (heps : 0 < eps) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      MapsTo (fun x => boundedFlow f hK hL x t) (closedBall 0 1) (ball u eps) := by
  obtain ⟨T, hT⟩ := exists_gt (max 0 (-Real.log (eps ^ 2 / 8)))
  have hT0 : 0 ≤ T := (le_max_left _ _).trans hT.le
  refine ⟨T, hT0, ?_⟩
  intro t ht x hx
  have ht0 : 0 ≤ t := hT0.trans ht
  have hexp : Real.exp (-t) < eps ^ 2 / 8 := by
    apply (Real.lt_log_iff_exp_lt (by positivity : 0 < eps ^ 2 / 8)).mp
    have hh := (le_max_right 0 (-Real.log (eps ^ 2 / 8))).trans_lt hT
    linarith
  have hdist := capFlow_distance_sq_le χ hχ hzero u hu f hK hL hag x hx t ht0
  have hxnorm : ‖x - u‖ ≤ 2 := by
    have hh := norm_sub_le x u
    rw [hu] at hh
    linarith [mem_closedBall_zero_iff.mp hx]
  have hsquare : ‖x - u‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (x - u)]
  have hsmall := mul_le_mul_of_nonneg_left hsquare (Real.exp_pos (-t)).le
  rw [mem_ball, dist_eq_norm]
  nlinarith [norm_nonneg (boundedFlow f hK hL x t - u)]

end PoincareConjecture.M25.Topology3D
