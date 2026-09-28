import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.SmoothInnerProduct
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false

open Bundle Bornology
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

noncomputable def capMetricInnerTangent (a : ℝ) (x : StandardCapSpace) :
    TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ := capMetricInner a x

theorem capMetricInner_isVonNBounded {a : ℝ} (ha : 0 ≤ a)
    (hapi : a ≤ Real.pi / 2) (x : StandardCapSpace) :
    IsVonNBounded ℝ {v : StandardCapSpace | capMetricInner a x v v < 1} := by
  let c := capAngularCoefficient a ‖x‖
  have hc : 0 < c := capAngularCoefficient_pos ha hapi (norm_nonneg x)
  apply (NormedSpace.isVonNBounded_ball ℝ StandardCapSpace (Real.sqrt (1 / c) + 1)).subset
  intro v hv
  have hnonneg := mul_nonneg (capRadialCoefficient_nonneg ha hapi (norm_nonneg x))
    (mul_self_nonneg (inner ℝ x v))
  have hbound : c * ‖v‖ ^ 2 < 1 := by
    change capMetricInner a x v v < 1 at hv
    rw [capMetricInner_apply, real_inner_self_eq_norm_sq] at hv
    linarith
  have hsq : ‖v‖ ^ 2 < 1 / c := (lt_div_iff₀ hc).mpr (by linarith)
  have hroot := Real.sq_sqrt (show 0 ≤ 1 / c by positivity)
  have hrootnonneg := Real.sqrt_nonneg (1 / c)
  rw [Metric.mem_ball, dist_zero_right]
  nlinarith [norm_nonneg v]

theorem capMetricInner_contMDiff {a : ℝ} (ha : 0 < a) :
    ContMDiff (𝓡 3) ((𝓡 3).prod 𝓘(ℝ,
      StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ)
        x (E := fun x => TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ)
        (capMetricInnerTangent a x)) := by
  intro x
  refine Bundle.contMDiffAt_totalSpace.mpr ⟨contMDiffAt_id, ?_⟩
  have h := (contMDiff_iff_contDiff.mpr (capMetricInner_contDiff ha)).contMDiffAt (x := x)
  convert! h using 1
  ext y u v
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    TangentBundle.symmL_model_space, ContinuousLinearMap.comp_apply]
  have hy : y ∈ (trivializationAt (StandardCapSpace →L[ℝ] ℝ)
      (fun z => TangentSpace (𝓡 3) z →L[ℝ] ℝ) x).baseSet := by
    rw [hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet]
    exact ⟨Set.mem_univ y, Set.mem_univ y⟩
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hy]
  have ht : trivializationAt ℝ (Bundle.Trivial StandardCapSpace ℝ) x =
      Bundle.Trivial.trivialization StandardCapSpace ℝ :=
    Bundle.Trivial.eq_trivialization _ _ _
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, ht,
    Bundle.Trivial.continuousLinearMapAt_trivialization, TangentBundle.symmL_model_space,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, capMetricInnerTangent]
  rfl

noncomputable def capRiemannianMetric (a : ℝ) (ha : 0 < a) (hapi : a ≤ Real.pi / 2) :
    RiemannianMetric 3 StandardCapSpace where
  inner := capMetricInnerTangent a
  symm := capMetricInner_symm a
  pos := capMetricInner_pos ha.le hapi
  isVonNBounded := capMetricInner_isVonNBounded ha.le hapi
  contMDiff := capMetricInner_contMDiff ha

end PoincareConjecture.M34
