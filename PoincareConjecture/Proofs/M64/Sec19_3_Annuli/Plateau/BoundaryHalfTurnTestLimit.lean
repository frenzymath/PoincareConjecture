import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnTests
import Mathlib.MeasureTheory.Integral.DominatedConvergence







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "K" => m64AnnulusDomain
local notation "S" => interior m64AnnulusDomain
local notation "a" => curvePeriod / 2
local notation "ei" i => EuclideanSpace.single (i : Fin 2) (1 : ℝ)




theorem m64HalfTurnBlend_integral_tendsto
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {mu : Measure X} {q : X → LoopPlane}
    (hq : Measurable q) (hK : ∀ᵐ x ∂mu, q x ∈ K)
    (hcut : ∀ᵐ x ∂mu, q x 0 ≠ a) {F : X → E} (hF : Integrable F mu)
    {f g : LoopPlane → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    Tendsto (fun j => ∫ x, m64HalfTurnBlend j f g (q x) • F x ∂mu) atTop
      (𝓝 (∫ x, m64HalfTurnPiece f g (q x) • F x ∂mu)) := by
  obtain ⟨C, -, hC⟩ := m64HalfTurnBlend_bound hf.continuous hg.continuous
  apply tendsto_integral_of_dominated_convergence (fun x => C * ‖F x‖)
  · intro j
    have hm := (m64HalfTurnBlend_contDiff hf hg j).continuous.measurable.comp hq
    exact hm.aestronglyMeasurable.smul hF.aestronglyMeasurable
  · exact hF.norm.const_mul C
  · intro j
    filter_upwards [hK] with x hx
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC j (q x) hx) (norm_nonneg _)
  · filter_upwards [hcut] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [m64HalfTurnBlend_eventually hf hg hx 0] with j hj
    rw [hj.1]




theorem m64HalfTurnBlend_derivative_integral_tendsto
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {mu : Measure X} {q : X → LoopPlane}
    (hq : Measurable q) (hK : ∀ᵐ x ∂mu, q x ∈ K)
    (hcut : ∀ᵐ x ∂mu, q x 0 ≠ a) {F : X → E} (hF : Integrable F mu)
    {f g : LoopPlane → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (i : Fin 2)
    (hmatch : i = 1 ∨
      ∀ s ∈ Icc (0 : ℝ) 1, f (annulusPoint a s) = g (annulusPoint a s)) :
    Tendsto (fun j => ∫ x, fderiv ℝ (m64HalfTurnBlend j f g) (q x) (ei i) • F x ∂mu) atTop
      (𝓝 (∫ x, m64HalfTurnPiece (fun p => fderiv ℝ f p (ei i))
        (fun p => fderiv ℝ g p (ei i)) (q x) • F x ∂mu)) := by
  obtain ⟨C, -, hC⟩ := m64HalfTurnBlend_derivative_bound hf hg i hmatch
  apply tendsto_integral_of_dominated_convergence (fun x => C * ‖F x‖)
  · intro j
    have hc : Continuous (fun p => fderiv ℝ (m64HalfTurnBlend j f g) p (ei i)) :=
      ((m64HalfTurnBlend_contDiff hf hg j).continuous_fderiv (by simp)).clm_apply
        continuous_const
    exact (hc.measurable.comp hq).aestronglyMeasurable.smul hF.aestronglyMeasurable
  · exact hF.norm.const_mul C
  · intro j
    filter_upwards [hK] with x hx
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC j (q x) hx) (norm_nonneg _)
  · filter_upwards [hcut] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [m64HalfTurnBlend_eventually hf hg hx i] with j hj
    rw [hj.2]




theorem m64HalfTurn_rectangle_ae :
    (∀ᵐ p ∂volume.restrict S, p ∈ K) ∧
      ∀ᵐ p ∂volume.restrict S, p 0 ≠ a := by
  constructor
  · exact (ae_restrict_mem isOpen_interior.measurableSet).mono fun _ hp => interior_subset hp
  · apply ae_restrict_of_ae
    apply ae_iff.mpr
    simpa only [not_not] using m64_cut_line_null a




theorem m64HalfTurn_boundary_ae {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) curvePeriod), annulusPoint x s ∈ K) ∧
      ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) curvePeriod), annulusPoint x s 0 ≠ a := by
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact ⟨hx.1, hx.2, hs⟩
  · apply ae_restrict_of_ae
    apply ae_iff.mpr
    simp only [annulusPoint, Matrix.cons_val_zero, not_not]
    exact measure_singleton a

end PoincareConjecture
