import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.TangentialTests
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.TestFunction.Smooth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace Poincare.Analysis.Sobolev.BoundaryTangential

open Weak NirenbergStandardTest NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem exists_norm_bound {F : Type*} [NormedAddCommGroup F]
    {a : E → F} (ha : Continuous a) (hc : HasCompactSupport a) :
    ∃ C ≥ 0, ∀ x, ‖a x‖ ≤ C := by
  obtain ⟨C, hC⟩ := ha.norm.bddAbove_range_of_hasCompactSupport hc.norm
  exact ⟨max C 0, le_max_right _ _, fun x => (hC ⟨x, rfl⟩).trans (le_max_left _ _)⟩

private theorem tendsto_bounded_mul {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {a : X → ℝ} {C : ℝ} (hC : ∀ x, ‖a x‖ ≤ C)
    {v : ℕ → X → ℝ} (hv : Tendsto (fun j => eLpNorm (v j) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (fun x => a x * v j x) 2 μ) atTop (𝓝 0) := by
  have hb (j : ℕ) : eLpNorm (fun x => a x * v j x) 2 μ ≤
      ENNReal.ofReal C * eLpNorm (v j) 2 μ := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul _ 2
    exact Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _
    (fun _ => bot_le) hb
  simpa using ENNReal.Tendsto.const_mul hv (Or.inr ENNReal.ofReal_ne_top)

omit [NeZero d] in
private theorem tendsto_restrict_inter {O W : Set E} {v : ℕ → E → ℝ}
    (hv : Tendsto (fun j => eLpNorm (v j) 2 (volume.restrict O)) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (v j) 2 (volume.restrict (W ∩ O))) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hv (fun _ => bot_le)
  intro j
  exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume inter_subset_right)

omit [NeZero d] in

theorem memW01p_mul_smooth_inter
    {O W : Set E} (hO : IsOpen O) (hW : IsOpen W) {u χ : E → ℝ}
    (hu : MemW01p 2 u O)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ W) :
    MemW01p 2 (fun x => χ x * u x) (W ∩ O) := by
  rcases hu with ⟨_, w, φ, hφ, hφc, hφs, hv, hd⟩
  obtain ⟨C₀, hC₀, hCχ⟩ := exists_norm_bound hχ.continuous hc
  obtain ⟨C₁, hC₁, hCDχ⟩ := exists_norm_bound
    (hχ.continuous_fderiv (by simp)) (hc.fderiv ℝ)
  let w' := w.mulSmoothBoundedP (by norm_num : (1 : ℝ≥0∞) ≤ 2) hO hχ hC₀ hC₁
    (by simpa only [Real.norm_eq_abs] using hCχ) hCDχ
  let w'' := w'.restrict (hW.inter hO) inter_subset_right
  refine ⟨w''.memW1p, w'', fun j x => χ x * φ j x, fun j => hχ.mul (hφ j),
    fun j => (hφc j).mul_left, ?_, ?_, ?_⟩
  · intro j x hx
    exact ⟨hs (tsupport_mul_subset_left hx), hφs j (tsupport_mul_subset_right hx)⟩
  · apply tendsto_restrict_inter
    have hlim := tendsto_bounded_mul hCχ hv
    convert hlim using 1
    ext j
    congr 1
    funext x
    ring
  · intro i
    apply tendsto_restrict_inter
    let a : E → ℝ := fun x => fderiv ℝ χ x (EuclideanSpace.single i 1)
    have hCa (x : E) : ‖a x‖ ≤ C₁ := by
      have hop : ‖a x‖ ≤ ‖fderiv ℝ χ x‖ := by
        simpa [a] using (fderiv ℝ χ x).le_opNorm (EuclideanSpace.single i (1 : ℝ))
      exact hop.trans (hCDχ x)
    have ha : Continuous a := (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hlim₁ := tendsto_bounded_mul hCχ (hd i)
    have hlim₀ := tendsto_bounded_mul hCa hv
    have hb (j : ℕ) : eLpNorm
        (fun x => fderiv ℝ (fun y => χ y * φ j y) x (EuclideanSpace.single i 1) -
          w''.weakGrad x i) 2 (volume.restrict O) ≤
        eLpNorm (fun x => χ x *
          (fderiv ℝ (φ j) x (EuclideanSpace.single i 1) - w.weakGrad x i)) 2 (volume.restrict O) +
        eLpNorm (fun x => a x * (φ j x - u x)) 2 (volume.restrict O) := by
      have heq : (fun x => fderiv ℝ (fun y => χ y * φ j y) x (EuclideanSpace.single i 1) -
          w''.weakGrad x i) = fun x =>
          χ x * (fderiv ℝ (φ j) x (EuclideanSpace.single i 1) - w.weakGrad x i) +
            a x * (φ j x - u x) := by
        funext x
        have hmul : fderiv ℝ (fun y => χ y * φ j y) x =
            χ x • fderiv ℝ (φ j) x + φ j x • fderiv ℝ χ x := by
          convert! fderiv_mul (hχ.differentiable (by simp) x)
            ((hφ j).differentiable (by simp) x) using 1
        rw [hmul]
        simp [w'', w', MemW1pWitness.restrict, MemW1pWitness.mulSmoothBoundedP, a]
        ring
      rw [heq]
      apply eLpNorm_add_le _ _ (by norm_num)
      · exact hχ.continuous.aestronglyMeasurable.mul
          ((((hφ j).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.sub
            (w.weakGrad_component_memLp i).aestronglyMeasurable)
      · exact ha.aestronglyMeasurable.mul
          ((hφ j).continuous.aestronglyMeasurable.sub w.memLp.aestronglyMeasurable)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _
      (fun _ => bot_le) hb
    simpa using hlim₁.add hlim₀

omit [NeZero d] in

theorem memW01p_inter_of_tsupport_subset
    {O W : Set E} (hO : IsOpen O) (hW : IsOpen W) {u : E → ℝ}
    (hu : MemW01p 2 u O) (hc : HasCompactSupport u) (hs : tsupport u ⊆ W) :
    MemW01p 2 u (W ∩ O) := by
  obtain ⟨χ, hχ, hχc, _, hχone, hχs⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff hc.isCompact hW hs
  have hm := memW01p_mul_smooth_inter hO hW hu hχ hχc hχs
  convert hm using 1
  funext x
  by_cases hx : x ∈ tsupport u
  · rw [hχone x hx, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem memW01p_standardNirenbergTest_inter
    {W : Set E} (hW : IsOpen W) {u η : E → ℝ}
    (hu : MemW01p 2 u (halfSpace d))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (k : Fin d) (hk : k ≠ 0) (h : ℝ)
    (hthick : Metric.cthickening |h| (tsupport η) ⊆ W) :
    MemW01p 2 (standardNirenbergTest k h η u) (W ∩ halfSpace d) := by
  apply memW01p_inter_of_tsupport_subset isOpen_halfSpace hW
    (memW01p_standardNirenbergTest hu hη hc k hk h)
    (standardNirenbergTest_hasCompactSupport k h hc u)
  exact (NirenbergTestFunction.tsupport_nirenbergTestFunction_subset η u k h).trans hthick

end Poincare.Analysis.Sobolev.BoundaryTangential
