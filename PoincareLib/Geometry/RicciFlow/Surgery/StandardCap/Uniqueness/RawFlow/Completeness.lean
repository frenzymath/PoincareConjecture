import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.RawFlow.MetricComparison
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.RawFlow.MetricSpace
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Mathlib.Completeness
import PoincareLib.Geometry.Riemannian.MetricComparison

/-!
# Completeness of every raw partial standard flow

Morgan-Tian, Lemma 12.6, printed p. 297: a uniform comparison with the
complete initial metric transfers Cauchy sequences and their limits. All
distances and completeness assertions use the selected Riemannian metric.
-/

set_option autoImplicit false

open Filter Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Lemma 12.6, p. 297: a global tangent-norm comparison controls the
extended path distance, including infinite distances between components. -/
theorem edist_le_mul_edist_of_tangentNorm_le
    (g h : RiemannianMetric n M) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm x v ≤ C * g.tangentNorm x v) (x y : M) :
    h.edist x y ≤ ENNReal.ofReal C * g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdiv : h.edist x y / ENNReal.ofReal C ≤ g.edist x y := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlength⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hb
    have hlength := pathELength_le_of_tangentNorm_le g h γ 0 1 C hC.le
      (fun u _ => hbound (γ u))
    have hdist : h.edist x y ≤ h.pathELength γ 0 1 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨h.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_le_pathELength hγsmooth hγ0 hγ1 zero_le_one
    apply (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hC).ne'
      ENNReal.ofReal_ne_top).mpr
    exact (hdist.trans hlength).trans
      ((mul_le_mul_right hγlength.le _).trans_eq (mul_comm _ _))
  simpa only [mul_comm] using (ENNReal.div_le_iff
    (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top).mp hdiv

/-- Lemma 12.6, p. 297: domination of a complete metric's tangent norms
transfers completeness. Both induced metrics have the manifold topology. -/
theorem metricComplete_of_tangentNorm_le [T3Space M]
    (g h : RiemannianMetric n M) (hg : MetricComplete g)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      g.tangentNorm x v ≤ C * h.tangentNorm x v) : MetricComplete h := by
  have hdist := edist_le_mul_edist_of_tangentNorm_le h g hC hbound
  rw [metricComplete_iff_toEMetricSpace] at hg ⊢
  refine EMetricSpace.completeSpace_of_topology_eq_edist_le (C := C)
    g.toEMetricSpace h.toEMetricSpace hg
    (g.toEMetricSpace_topology.trans h.toEMetricSpace_topology.symm) ?_
  intro x y
  simpa only [toEMetricSpace_edist] using hdist x y

end PoincareMT.RiemannianMetric

namespace PoincareMT.PartialStandardCapFlow

/-- Lemma 12.6, p. 297: each valid slice of an arbitrary partial standard
flow is complete, using only its raw curvature bound and the M04 comparison. -/
theorem complete (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {t : ℝ} (ht : t ∈ Set.Ico 0 G.lifetime) :
    MetricComplete (G.flow.metric t) := by
  obtain ⟨K, _, hcompare⟩ := G.exists_metric_comparison P ht.1 ht.2
  let A : ℝ := Real.exp (-6 * K * t)
  have hA : 0 < A := Real.exp_pos _
  apply RiemannianMetric.metricComplete_of_tangentNorm_le
    g₀.metric (G.flow.metric t) g₀.complete (inv_pos.mpr (Real.sqrt_pos.mpr hA))
  intro x v
  have hquad := (hcompare t ⟨ht.1, le_rfl⟩ x v).1
  have hsqrt := Real.sqrt_le_sqrt hquad
  rw [Real.sqrt_mul hA.le] at hsqrt
  change Real.sqrt A * g₀.metric.tangentNorm x v ≤
    (G.flow.metric t).tangentNorm x v at hsqrt
  exact (le_inv_mul_iff₀ (Real.sqrt_pos.mpr hA)).2 hsqrt

end PoincareMT.PartialStandardCapFlow
