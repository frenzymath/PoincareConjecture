import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Covering
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Bounds.Ricci
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence












noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedRicciFlowCompactnessHypotheses



theorem eventually_exists_uniform_finset_cover
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    {A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ᶠ k in atTop,
      ∃ S : Finset (H.sequence.carrier k).carrier,
        (↑S : Set (H.sequence.carrier k).carrier) ⊆ (H.sequence.flow k).zeroBall A ∧
        S.card ≤ N ∧
        (H.sequence.flow k).zeroBall A ⊆
          ⋃ x ∈ S, (H.sequence.carrier k).metricBall
            ((H.sequence.flow k).metricAt 0) x δ := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨1, Eventually.of_forall fun k => ?_⟩
    let C := H.sequence.carrier k
    let F := H.sequence.flow k
    let : TopologicalSpace C.carrier := C.topologicalSpace
    let : ChartedSpace (EuclideanSpace ℝ (Fin 0)) C.carrier := C.chartedSpace
    let : IsManifold (𝓡 0) ∞ C.carrier := C.isManifold
    let : Subsingleton C.carrier := C.subsingleton_zero
    refine ⟨{F.base}, ?_, by simp, ?_⟩
    · intro x hx
      have hxbase : x = F.base := by simpa only [Finset.mem_coe, Finset.mem_singleton] using hx
      subst x
      change (F.metricAt 0).edist F.base F.base < ENNReal.ofReal A
      simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
        ENNReal.ofReal_pos.mpr hA
    · intro x _
      refine mem_iUnion₂.mpr ⟨F.base, by simp, ?_⟩
      have hx : x = F.base := Subsingleton.elim _ _
      subst x
      change (F.metricAt 0).edist F.base F.base < ENNReal.ofReal δ
      simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
        ENNReal.ofReal_pos.mpr hδ
  by_cases hδA : δ ≤ A
  · obtain ⟨K, hK, hcurv⟩ := H.all_time_curvature_control_on_zero_ball (5 * A) (by positivity)
    refine ⟨⌈RiemannianMetric.modelVolume n K (3 * A) /
      RiemannianMetric.modelVolume n K (δ / 2)⌉₊, ?_⟩
    filter_upwards [hcurv, H.zero_time_ball_compact (5 * A) (by positivity)] with k hk hcompact
    let C := H.sequence.carrier k
    let F := H.sequence.flow k
    let : TopologicalSpace C.carrier := C.topologicalSpace
    let : MeasurableSpace C.carrier := C.measurableSpace
    let : BorelSpace C.carrier := C.borelSpace
    let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    let : T3Space C.carrier := C.t3Space
    let : T2Space C.carrier := C.t2Space
    let : SecondCountableTopology C.carrier := C.secondCountable
    have hRic : ∀ x ∈ (F.metricAt 0).ball F.base (5 * A),
        ∀ v : TangentSpace (𝓡 n) x,
          -(((n : ℝ) - 1) * K) * (F.metricAt 0).inner x v v ≤
            (F.flow.connection 0).ricci x v v := by
      intro x hx v
      have hsec := fun u w =>
        ((F.flow.connection 0).abs_sectionalCurvature_le_curvatureTensorNorm x u w).trans
          (hk 0 H.time_bounds x hx)
      simpa only [BasedFlow.metricAt, neg_mul] using
        (F.flow.connection 0).ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le
          x K hsec v
    obtain ⟨S, hS, hcard, _, hcover⟩ :=
      (F.metricAt 0).exists_finset_cover_of_precompact_ball F.base (by omega)
        hA hδ hδA hK hcompact (F.flow.connection 0) hRic
    exact ⟨S, hS, hcard, hcover⟩
  · refine ⟨1, Eventually.of_forall fun k => ?_⟩
    let C := H.sequence.carrier k
    let F := H.sequence.flow k
    let : TopologicalSpace C.carrier := C.topologicalSpace
    let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    refine ⟨{F.base}, ?_, by simp, ?_⟩
    · intro x hx
      have hxbase : x = F.base := by simpa only [Finset.mem_coe, Finset.mem_singleton] using hx
      subst x
      change (F.metricAt 0).edist F.base F.base < ENNReal.ofReal A
      simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
        ENNReal.ofReal_pos.mpr hA
    · intro x hx
      refine mem_iUnion₂.mpr ⟨F.base, by simp, ?_⟩
      exact hx.trans_le (ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_not_ge hδA)))

end PoincareConjecture.PointedRicciFlowCompactnessHypotheses
