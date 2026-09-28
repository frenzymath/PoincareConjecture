import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.ChartEnergy
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variational

theorem positive_form_operator_isUnit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v : E, v ≠ 0 → 0 < B v v) :
    IsUnit (InnerProductSpace.continuousLinearMapOfBilin B) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  by_contra hne
  change InnerProductSpace.continuousLinearMapOfBilin B v = 0 at hv
  have hpos := hB v hne
  have hval := InnerProductSpace.continuousLinearMapOfBilin_apply B v v
  rw [hv, inner_zero_left] at hval
  exact (ne_of_gt hpos) hval.symm

theorem continuousOn_inverse_operator {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Set X} (A : X → E →L[ℝ] E) (hA : ContinuousOn A S)
    (hunit : ∀ x ∈ S, IsUnit (A x)) : ContinuousOn (fun x ↦ Ring.inverse (A x)) S := by
  intro x hx
  obtain ⟨u, hu⟩ := hunit x hx
  exact (hu ▸ NormedRing.inverse_continuousAt u).comp_continuousWithinAt (hA x hx)

theorem inverse_operator_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (hunit : IsUnit A) (v : E) : Ring.inverse A (A v) = v := by
  have h := congrArg (fun L : E →L[ℝ] E ↦ L v) (Ring.inverse_mul_cancel A hunit)
  exact h

theorem contDiffOn_inverse_operator {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Set X} (A : X → E →L[ℝ] E) (hA : ContDiffOn ℝ ∞ A S)
    (hunit : ∀ x ∈ S, IsUnit (A x)) : ContDiffOn ℝ ∞ (fun x ↦ Ring.inverse (A x)) S := by
  intro x hx
  obtain ⟨u, hu⟩ := hunit x hx
  exact (hu ▸ contDiffAt_ringInverse ℝ u).comp_contDiffWithinAt x (hA x hx)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem metricInChart_symm (g : RiemannianMetric n M) {x y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (v w : EuclideanSpace ℝ (Fin n)) : metricInChart g x y v w = metricInChart g x y w v := by
  rw [metricInChart_apply g hy, metricInChart_apply g hy]
  exact g.symm _ _ _

set_option synthInstance.maxHeartbeats 200000 in

theorem metricInChart_joint_contMDiffOn {J : Set ℝ} (F : RicciFlow n M J) (x : M) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun z : ℝ × M ↦ metricInChart (F.metric z.1) x z.2)
      (J ×ˢ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) := by
  let e := trivializationAt
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (fun z : M ↦ TangentSpace (𝓡 n) z →L[ℝ] TangentSpace (𝓡 n) z →L[ℝ] ℝ) x
  have he : MapsTo (fun z : ℝ × M ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      z.2 ((F.metric z.1).inner z.2))
      (J ×ˢ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) e.source := by
    intro z hz
    apply (Bundle.Trivialization.mem_source e).mpr
    change z.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∩
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).source ∩ univ)
    exact ⟨hz.2, hz.2, mem_univ _⟩
  have hsmooth := F.smooth.mono
    (prod_mono (Subset.rfl : J ⊆ J)
      (subset_univ (chartAt (EuclideanSpace ℝ (Fin n)) x).source))
  simpa only [metricInChart, e] using
    ((Bundle.Trivialization.contMDiffOn_iff (e := e) he).mp hsmooth).2

def chartActionDomain {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M) :
    Set (ℝ × EuclideanSpace ℝ (Fin n)) :=
  interior ((fun s : ℝ ↦ T - s ^ 2) ⁻¹' J) ×ˢ (extChartAt (𝓡 n) x).target

theorem chartActionDomain_open {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M) :
    IsOpen (chartActionDomain F T x) :=
  isOpen_interior.prod (isOpen_extChartAt_target (I := 𝓡 n) x)

noncomputable def chartActionMetric {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)
    (z : ℝ × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  metricInChart (F.metric (T - z.1 ^ 2)) x ((extChartAt (𝓡 n) x).symm z.2)

noncomputable def chartActionPotential {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)
    (z : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  2 * z.1 ^ 2 * (F.connection (T - z.1 ^ 2)).scalarCurvature ((extChartAt (𝓡 n) x).symm z.2)

theorem chartActionMetric_contDiffOn {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M) :
    ContDiffOn ℝ ∞ (chartActionMetric F T x) (chartActionDomain F T x) := by
  have htime : ContMDiffOn (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))) (𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) ↦ T - z.1 ^ 2) (chartActionDomain F T x) :=
    (contDiff_const.sub (contDiff_fst.pow 2)).contMDiff.contMDiffOn
  have hpoint : ContMDiffOn (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))) (𝓡 n) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) ↦ (extChartAt (𝓡 n) x).symm z.2)
      (chartActionDomain F T x) :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).comp
      contDiff_snd.contMDiff.contMDiffOn (fun _ hz ↦ hz.2)
  apply ContMDiffOn.contDiffOn
  apply (metricInChart_joint_contMDiffOn F x).comp (htime.prodMk hpoint)
  intro z hz
  refine ⟨?_, ?_⟩
  · have hztime : z.1 ∈ ((fun r : ℝ => T - r ^ 2) ⁻¹' J) := interior_subset hz.1
    exact hztime
  · simpa only [extChartAt_source] using (extChartAt (𝓡 n) x).map_target hz.2

theorem chartActionPotential_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ)
    (hpotential : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => 2 * z.1 ^ 2 *
        (F.connection (T - z.1 ^ 2)).scalarCurvature z.2)) (x : M) :
    ContDiffOn ℝ ∞ (chartActionPotential F T x) (chartActionDomain F T x) := by
  have hpoint : ContMDiffOn (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))) (𝓡 n) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (extChartAt (𝓡 n) x).symm z.2)
      (chartActionDomain F T x) :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).comp
      contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2)
  exact (hpotential.comp_contMDiffOn
    (contDiff_fst.contMDiff.contMDiffOn.prodMk hpoint)).contDiffOn

theorem chartActionMetric_pos {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)
    {z : ℝ × EuclideanSpace ℝ (Fin n)} (hz : z ∈ chartActionDomain F T x)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) : 0 < chartActionMetric F T x z v v := by
  apply metricInChart_pos _ _ v hv
  simpa only [extChartAt_source] using (extChartAt (𝓡 n) x).map_target hz.2

theorem chartActionMetric_symm {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)
    {z : ℝ × EuclideanSpace ℝ (Fin n)} (hz : z ∈ chartActionDomain F T x)
    (v w : EuclideanSpace ℝ (Fin n)) :
    chartActionMetric F T x z v w = chartActionMetric F T x z w v := by
  apply metricInChart_symm _ _ v w
  simpa only [extChartAt_source] using (extChartAt (𝓡 n) x).map_target hz.2

noncomputable def chartMetricOperator {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)
    (z : ℝ × EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  InnerProductSpace.continuousLinearMapOfBilin (chartActionMetric F T x z)

theorem chartMetricOperator_isUnit {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M)
    {z : ℝ × EuclideanSpace ℝ (Fin n)} (hz : z ∈ chartActionDomain F T x) :
    IsUnit (chartMetricOperator F T x z) :=
  positive_form_operator_isUnit _ (chartActionMetric_pos F T x hz)

theorem chartMetricOperator_contDiffOn {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M) :
    ContDiffOn ℝ ∞ (chartMetricOperator F T x) (chartActionDomain F T x) := by
  unfold chartMetricOperator InnerProductSpace.continuousLinearMapOfBilin
  exact contDiffOn_const.clm_comp (chartActionMetric_contDiffOn F T x)

theorem chartMetricInverse_contDiffOn {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ) (x : M) :
    ContDiffOn ℝ ∞ (fun z ↦ Ring.inverse (chartMetricOperator F T x z)) (chartActionDomain F T x) :=
  contDiffOn_inverse_operator _ (chartMetricOperator_contDiffOn F T x)
    (fun _ hz ↦ chartMetricOperator_isUnit F T x hz)

end PoincareConjecture.ReducedLengthMinimum.Variational
