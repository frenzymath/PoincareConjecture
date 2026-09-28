import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence.LengthBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Identities


set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem surface_ricci_nonneg (K : AncientKappaSolution 2 M) {t : ℝ} (ht : t ≤ 0)
    (x : M) (v : TangentSpace (𝓡 2) x) : 0 ≤ (K.flow.connection t).ricci x v v := by
  rw [(K.flow.connection t).ricci_eq_half_scalarCurvature_mul_inner]
  have hR := (K.flow.connection t).scalar_nonnegative_of_nonnegative_curvatureOperator x
    (K.nonnegative_curvature_operator t ht x)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨(K.flow.metric t).toRiemannianMetric⟩
  exact mul_nonneg (div_nonneg hR (by norm_num))
    (show 0 ≤ inner ℝ v v from real_inner_self_nonneg)


theorem surface_metric_monotone (K : AncientKappaSolution 2 M) {s t : ℝ}
    (hst : s ≤ t) (ht : t ≤ 0) (x : M) (v : TangentSpace (𝓡 2) x) :
    (K.flow.metric t).inner x v v ≤ (K.flow.metric s).inner x v v := by
  have hm : AntitoneOn (fun t => (K.flow.metric t).inner x v v) (Iic 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic 0)
      (fun t ht => (K.flow.equation t ht x v v).continuousWithinAt)
      (f' := fun t => -2 * (K.flow.connection t).ricci x v v)
    · intro t ht
      exact (K.flow.equation t (interior_subset ht) x v v).mono interior_subset
    · intro t ht
      have ht0 : t ∈ Iic (0 : ℝ) := interior_subset ht
      exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
        (K.surface_ricci_nonneg ht0 x v)
  exact hm (hst.trans ht) ht hst

end PoincareConjecture.AncientKappaSolution
