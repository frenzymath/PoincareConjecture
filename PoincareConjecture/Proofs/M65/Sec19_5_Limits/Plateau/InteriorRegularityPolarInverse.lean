import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityPolarMeasure
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic












set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M65Interior



def polarCoordinates (x z : LoopPlane) : ℝ × ℝ :=
  polarCoord (Proofs.M58.loopPlaneEquivProd (z - x))



theorem polarCoordinates_measurable (x : LoopPlane) :
    Measurable (polarCoordinates x) := by
  have h : Measurable (fun z : LoopPlane =>
      Proofs.M58.loopPlaneEquivProd (z - x)) :=
    Proofs.M58.loopPlaneEquivProd.measurable.comp (continuous_id.sub continuous_const).measurable
  exact ((Real.continuous_sqrt.measurable.comp
    ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2))).prodMk
    (Complex.measurable_arg.comp Complex.equivRealProdCLM.symm.continuous.measurable)).comp h



theorem polarCoordinates_radius (x z : LoopPlane) :
    (polarCoordinates x z).1 = ‖z - x‖ := by
  change Real.sqrt ((z - x) 0 ^ 2 + (z - x) 1 ^ 2) = ‖z - x‖
  have h := EuclideanSpace.real_norm_sq_eq (z - x)
  rw [Fin.sum_univ_two] at h
  rw [← h, Real.sqrt_sq (norm_nonneg _)]



theorem polarCoordinates_angle (x z : LoopPlane) :
    (polarCoordinates x z).2 ∈ Icc (-Real.pi) Real.pi :=
  ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩



theorem polarCoordinates_polarPlane (x : LoopPlane) {p : ℝ × ℝ}
    (hp : p ∈ polarCoord.target) : polarCoordinates x (polarPlane x p) = p := by
  unfold polarCoordinates polarPlane
  rw [add_sub_cancel_left, ← Proofs.M58.loopPlaneEquivProd_symm_polar,
    MeasurableEquiv.apply_symm_apply]
  exact polarCoord.right_inv hp



theorem polarCoordinates_measurePreserving (x : LoopPlane) :
    MeasurePreserving (polarCoordinates x) volume polarMeasure := by
  refine ⟨polarCoordinates_measurable x, ?_⟩
  have ht : ∀ᵐ p ∂polarMeasure, p ∈ polarCoord.target :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem polarCoord.open_target.measurableSet)
  have heq : (polarCoordinates x ∘ polarPlane x) =ᵐ[polarMeasure] id := by
    filter_upwards [ht] with p hp
    exact polarCoordinates_polarPlane x hp
  rw [← (polarPlane_measurePreserving x).map_eq,
    Measure.map_map (polarCoordinates_measurable x) (polarPlane_measurePreserving x).measurable,
    Measure.map_congr heq, Measure.map_id]




theorem polarCoordinates_preimage_rectangle (x : LoopPlane) (r : ℝ) :
    polarCoordinates x ⁻¹' (Icc (0 : ℝ) r ×ˢ Icc (-Real.pi) Real.pi) =
      closedBall x r := by
  ext z
  simp only [mem_preimage, mem_prod, mem_Icc, polarCoordinates_radius,
    norm_nonneg, true_and, mem_closedBall, dist_eq_norm]
  exact and_iff_left (polarCoordinates_angle x z)



theorem polarCoordinates_disk_measurePreserving (x : LoopPlane) (r : ℝ) :
    MeasurePreserving (polarCoordinates x) (volume.restrict (closedBall x r))
      (polarMeasure.restrict (Icc (0 : ℝ) r ×ˢ Icc (-Real.pi) Real.pi)) := by
  simpa only [polarCoordinates_preimage_rectangle] using
    (polarCoordinates_measurePreserving x).restrict_preimage
      (s := Icc (0 : ℝ) r ×ˢ Icc (-Real.pi) Real.pi)
      (measurableSet_Icc.prod measurableSet_Icc)



theorem polar_rectangle_measure_le (r : ℝ) :
    polarMeasure.restrict (Icc (0 : ℝ) r ×ˢ Icc (-Real.pi) Real.pi) ≤
      ENNReal.ofReal r • volume.restrict (Icc (0 : ℝ) r ×ˢ Icc (-Real.pi) Real.pi) := by
  let S : Set (ℝ × ℝ) := Icc 0 r ×ˢ Icc (-Real.pi) Real.pi
  have hS : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  change polarMeasure.restrict S ≤ _
  rw [polarMeasure, restrict_withDensity hS]
  calc
    _ ≤ ((volume.restrict polarCoord.target).restrict S).withDensity
        (fun _ => ENNReal.ofReal r) := by
      apply withDensity_mono
      filter_upwards [ae_restrict_mem hS] with p hp
      exact ENNReal.ofReal_le_ofReal hp.1.2
    _ = ENNReal.ofReal r • (volume.restrict polarCoord.target).restrict S :=
      withDensity_const _
    _ ≤ _ := smul_le_smul_left _ (Measure.restrict_mono_measure Measure.restrict_le_self S)



theorem memLp_polarCoordinates {E : Type*} [NormedAddCommGroup E]
    {f : ℝ × ℝ → E} {p : ℝ≥0∞} {r : ℝ}
    (hf : MemLp f p (volume.restrict (Icc (0 : ℝ) r ×ˢ Icc (-Real.pi) Real.pi)))
    (x : LoopPlane) :
    MemLp (fun z => f (polarCoordinates x z)) p (volume.restrict (closedBall x r)) := by
  have h := hf.of_measure_le_smul ENNReal.ofReal_ne_top (polar_rectangle_measure_le r)
  exact h.comp_measurePreserving (polarCoordinates_disk_measurePreserving x r)

end PoincareConjecture.M65Interior
