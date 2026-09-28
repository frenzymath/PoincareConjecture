import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_HorizontalDisk
import PoincareConjecture.Proofs.M14.Sec6_2_EulerContinuity
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Matrix.Bounds
import PoincareConjecture.Proofs.M04.TensorNorm











set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}



theorem horizontalScalarDifferential_continuous_total
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    Continuous (fun z : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal =>
      M14HorizontalScalarDifferential G z.proj z.2.val) := by
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hI : ContMDiff ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (spacetimeModel n).tangent ∞
      (fun z : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal =>
        TotalSpace.mk' (SpacetimeModelVector n)
          (E := (TangentSpace (spacetimeModel n) : G.Point → Type _)) z.proj z.2.val) :=
    G.spacetime.horizontal_inclusion_smooth
  have h := (contMDiff_snd_tangentBundle_modelSpace ℝ (𝓘(ℝ, ℝ))).comp
    ((H.scalar_smooth.contMDiff_tangentMap (m := ∞) (by simp)).comp hI)
  exact h.continuous




theorem compact_cage_analytic_bounds
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {K : Set G.Point} (hK : IsCompact K) :
    ∃ CR Cgrad : ℝ, 0 ≤ CR ∧ 0 ≤ Cgrad ∧
      (∀ q ∈ K, ∀ v w : G.Horizontal q, |horizontalRicci G.leafwise q v w| ≤
        CR * Real.sqrt (G.spacetime.horizontalMetric.inner q v v) *
          Real.sqrt (G.spacetime.horizontalMetric.inner q w w)) ∧
      ∀ q ∈ K, ∀ v : G.Horizontal q,
        |M14HorizontalScalarDifferential G q v.val| ≤
          Cgrad * Real.sqrt (G.spacetime.horizontalMetric.inner q v v) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : ∀ q, NormedAddCommGroup (G.Horizontal q) := fun q =>
    (metric.toCore q).toNormedAddCommGroupOfTopology
      (metric.continuousAt q) (metric.isVonNBounded q)
  let : ∀ q, InnerProductSpace ℝ (G.Horizontal q) := fun q =>
    .ofCoreOfTopology (metric.toCore q) (metric.continuousAt q) (metric.isVonNBounded q)
  let : RiemannianBundle G.Horizontal := ⟨metric⟩
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  obtain ⟨C0, hC0⟩ := hK.bddAbove_image H.norm_continuous.continuousOn
  let CR := (n : ℝ) * max C0 0
  have hCR : 0 ≤ CR := mul_nonneg (Nat.cast_nonneg n) (le_max_right _ _)
  have hRic (q : G.Point) (hq : q ∈ K) (v w : G.Horizontal q) :
      |horizontalRicci G.leafwise q v w| ≤
        CR * Real.sqrt (G.spacetime.horizontalMetric.inner q v v) *
          Real.sqrt (G.spacetime.horizontalMetric.inner q w w) := by
    let S := G.slices (G.spacetime.timeFunction q)
    let qs : S.Point := spacetimeSlicePoint G.slices q
    let D := G.leafwise.sliceConnection (G.spacetime.timeFunction q)
    let j := S.tangentEquiv qs
    have hnorm (a : G.Horizontal q) : S.metricOnPoints.tangentNorm qs (j.symm a) =
        Real.sqrt (G.spacetime.horizontalMetric.inner q a a) := by
      change Real.sqrt (S.metricOnPoints.inner qs (j.symm a) (j.symm a)) = _
      rw [S.metric_eq]
      change Real.sqrt (G.spacetime.horizontalMetric.inner q (j (j.symm a))
        (j (j.symm a))) = _
      exact congrArg (fun z : G.Horizontal q =>
        Real.sqrt (G.spacetime.horizontalMetric.inner q z z)) (j.apply_symm_apply a)
    have h := D.abs_ricci_le_curvatureDerivativeNorm_zero
      (H.slice_calculus (G.spacetime.timeFunction q)) qs (j.symm v) (j.symm w)
    rw [D.curvatureDerivativeNorm_zero, hnorm, hnorm] at h
    change |horizontalRicci G.leafwise q v w| ≤
      (n : ℝ) * horizontalCurvatureNorm G.leafwise q *
        Real.sqrt (G.spacetime.horizontalMetric.inner q v v) *
          Real.sqrt (G.spacetime.horizontalMetric.inner q w w) at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_left ((hC0 ⟨q, hq, rfl⟩).trans (le_max_left _ _))
      (Nat.cast_nonneg n)
  obtain ⟨C1, hC1⟩ := (isCompact_horizontalDisk G hK 1).bddAbove_image
    (horizontalScalarDifferential_continuous_total hM12).abs.continuousOn
  let Cgrad := max C1 0
  refine ⟨CR, Cgrad, hCR, le_max_right _ _, hRic, ?_⟩
  intro q hq v
  by_cases hv : v = 0
  · subst v
    simp only [ZeroMemClass.coe_zero, M14HorizontalScalarDifferential, map_zero,
      abs_zero, Real.sqrt_zero, mul_zero, le_refl]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : G.Horizontal q := ‖v‖⁻¹ • v
  have hw : G.spacetime.horizontalMetric.inner q w w = 1 := by
    change inner ℝ (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = 1
    rw [real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hbound : |M14HorizontalScalarDifferential G q w.val| ≤ Cgrad := by
    apply (hC1 ⟨TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q w,
      ⟨hq, hw.le⟩, rfl⟩).trans
    exact le_max_left _ _
  change |M14HorizontalScalarDifferential G q (‖v‖⁻¹ • v.val)| ≤ Cgrad at hbound
  rw [M14HorizontalScalarDifferential, map_smul, smul_eq_mul, abs_mul,
    abs_of_pos (inv_pos.mpr hvpos)] at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound hvpos.le
  rw [← mul_assoc, mul_inv_cancel₀ hvpos.ne', one_mul] at hmul
  have hnorm : ‖v‖ = Real.sqrt (G.spacetime.horizontalMetric.inner q v v) := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  simpa only [hnorm, mul_comm, M14HorizontalScalarDifferential] using hmul

end PoincareConjecture.Proofs.M46
