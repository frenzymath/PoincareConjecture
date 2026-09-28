import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Services
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Derivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.TimeTranslation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.ScalarDerivatives

theorem ancient_ball_mono (S : ScalarDerivativeServices.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution 3 M) {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 0)
    (p : M) (r : ℝ) :
    (K.flow.metric s).ball p r ⊆ (K.flow.metric t).ball p r := by
  have hmetric (x : M) (v : TangentSpace (𝓡 3) x) :
      (K.flow.metric t).inner x v v ≤ (K.flow.metric s).inner x v v := by
    have hm : AntitoneOn (fun a => (K.flow.metric a).inner x v v) (Iic 0) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic 0)
        (fun a ha => (K.flow.equation a ha x v v).continuousWithinAt)
        (f' := fun a => -2 * (K.flow.connection a).ricci x v v)
      · intro a ha
        exact (K.flow.equation a (interior_subset ha) x v v).mono interior_subset
      · intro a ha
        exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
          ((K.flow.connection a).ricci_bounds_of_nonnegative_curvatureOperator
            (S.tensor_calculus 3 M _ _) x
            (K.nonnegative_curvature_operator a
              (show a ∈ Iic (0 : ℝ) from interior_subset ha) x) v).1
    exact hm (hst.trans ht) ht hst
  have hdist := RiemannianMetric.edist_le_mul_of_inner_mfderiv_le
    (K.flow.metric s) (K.flow.metric t) (F := id) contMDiff_id
    (C := 1) zero_lt_one (fun x v => by simpa using hmetric x v)
  intro x hx
  exact lt_of_le_of_lt (by simpa using hdist p x) hx

theorem uniform_terminal_curvatureDerivative_bound
    (S : ScalarDerivativeServices.{u}) (L : ℝ) (hL : 0 < L) (k : ℕ) :
    ∃ D : ℝ, 0 < D ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M],
        ∀ (K : AncientKappaSolution 3 M) (p : M),
          (∀ x ∈ (K.flow.metric 0).ball p 1,
            (K.flow.connection 0).scalarCurvature x ≤ L) →
          (K.flow.connection 0).curvatureDerivativeNorm k p ≤ D := by
  obtain ⟨D, hD, hShi⟩ :=
    local_curvatureDerivative_bound 3 k L L 1 hL hL (by norm_num)
  refine ⟨D, hD, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K p hscalar
  have hshift : (fun s : ℝ => s + (-1)) '' Icc 0 1 ⊆ Iic 0 := by
    rintro _ ⟨s, hs, rfl⟩
    change s + (-1) ≤ 0
    linarith [hs.2]
  have hnontrivial : (Icc (0 : ℝ) 1).Nontrivial :=
    ⟨0, by norm_num, 1, by norm_num, by norm_num⟩
  let F := K.flow.translate (-1) hshift ordConnected_Icc hnontrivial
  have hcompact : IsCompact (closure ((F.metric 0).ball p 1)) := by
    change IsCompact (closure ((K.flow.metric (0 + (-1))).ball p 1))
    exact (K.flow.metric (0 + (-1))).isCompact_closure_ball_of_metricComplete
      (K.complete _ (by norm_num)) p 1
  have hcurv : ∀ s ∈ Icc 0 1, ∀ x ∈ (F.metric 0).ball p 1,
      (F.connection s).curvatureTensorNorm x ≤ L := by
    intro s hs x hx
    have hxold : x ∈ (K.flow.metric (-1)).ball p 1 := by
      simpa only [F, RicciFlow.translate, zero_add] using hx
    have hxzero := ancient_ball_mono S K (by norm_num : (-1 : ℝ) ≤ 0) le_rfl p 1 hxold
    exact (S.past_norm_le_scalar M K (s + (-1)) 0
      (by linarith [hs.2]) le_rfl x).trans (hscalar x hxzero)
  have hp : p ∈ (F.metric 0).ball p (1 / 2) := by
    change (F.metric 0).edist p p < ENNReal.ofReal (1 / 2)
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
    positivity
  have hb := hShi M 1 (by norm_num) (by rw [div_self hL.ne']) F p hcompact hcurv
    1 (by norm_num) p hp
  change (K.flow.connection (1 + (-1))).curvatureDerivativeNorm k p ≤
    D / (1 : ℝ) ^ ((k : ℝ) / 2) at hb
  rw [show (1 : ℝ) + (-1) = 0 by norm_num, Real.one_rpow, div_one] at hb
  exact hb

end PoincareConjecture.ScalarDerivatives
