import PoincareConjecture.Proofs.M47.TerminalCurvatureFlowMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Diffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


def terminalCurvatureFlowDiffeomorph
    (Phi : ℝ → M → M) (hzero : ∀ x, Phi 0 x = x)
    (hadd : ∀ s t x, Phi (s + t) x = Phi s (Phi t x))
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (fun z : ℝ × M => Phi z.1 z.2))
    (t : ℝ) : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ M where
  toFun := Phi t
  invFun := Phi (-t)
  left_inv x := by rw [← hadd, neg_add_cancel, hzero]
  right_inv x := by rw [← hadd, add_neg_cancel, hzero]
  contMDiff_toFun := hs.comp (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun := hs.comp (contMDiff_const.prodMk contMDiff_id)



theorem terminalCurvature_flow_invariants
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {V : (x : M) → TangentSpace (𝓡 n) x} {Phi : ℝ → M → M}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V))
    (hparallel : ∀ y v, D.connection V y v = 0)
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (fun z : ℝ × M => Phi z.1 z.2))
    (hPhi : ∀ x, IsMIntegralCurve (fun t => Phi t x) V)
    (hzero : ∀ x, Phi 0 x = x)
    (hadd : ∀ s t x, Phi (s + t) x = Phi s (Phi t x)) (t : ℝ) :
    (∀ x, D.scalarCurvature (Phi t x) = D.scalarCurvature x) ∧
      (∀ x, D.curvatureTensorNorm (Phi t x) = D.curvatureTensorNorm x) ∧
      ∀ x y, g.edist (Phi t x) (Phi t y) = g.edist x y := by
  let e := terminalCurvatureFlowDiffeomorph Phi hzero hadd hs t
  have hmetric (x : M) (v w : TangentSpace (𝓡 n) x) :
      g.inner x v w = g.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w) :=
    (terminalCurvature_flow_preserves_metric hV hparallel hs hPhi hzero t x v w).symm
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact (D.scalarCurvature_eq_of_local_isometry D isOpen_univ e.contMDiff.contMDiffOn
      (fun x _ => hmetric x) (mem_univ x)).symm
  · intro x
    exact (D.curvatureTensorNorm_eq_of_local_isometry D isOpen_univ e.contMDiff.contMDiffOn
      (fun x _ => hmetric x) (mem_univ x)).symm
  · intro x y
    exact (RiemannianMetric.edist_diffeomorph g g e hmetric x y).symm



theorem terminalCurvature_flow_isometry [T3Space M] [PreconnectedSpace M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {V : (x : M) → TangentSpace (𝓡 n) x} {Phi : ℝ → M → M}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V))
    (hparallel : ∀ y v, D.connection V y v = 0)
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (fun z : ℝ × M => Phi z.1 z.2))
    (hPhi : ∀ x, IsMIntegralCurve (fun t => Phi t x) V)
    (hzero : ∀ x, Phi 0 x = x)
    (hadd : ∀ s t x, Phi (s + t) x = Phi s (Phi t x)) (t : ℝ) :
    letI := g.toMetricSpace
    Isometry (Phi t) := by
  let := g.toMetricSpace
  intro x y
  exact (terminalCurvature_flow_invariants D hV hparallel hs hPhi hzero hadd t).2.2 x y

end PoincareConjecture.M47
