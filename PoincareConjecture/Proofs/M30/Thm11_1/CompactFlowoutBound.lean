import PoincareConjecture.Proofs.M30.Thm11_1.TransverseFlowout
import PoincareConjecture.Proofs.M30.Thm11_1.FlowoutCompleteness
import PoincareConjecture.Proofs.M30.Thm11_1.CompleteLocalIsometry
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.RegularLevelScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold
open scoped Manifold ContDiff Bundle

universe u v w

namespace PoincareConjecture.M30

theorem scalar_bounded_of_compact_transverse_isometric_flowout
    {n : ℕ} {S : Type u} {Q : Type v} {M : Type w}
    [TopologicalSpace S] [TopologicalSpace Q] [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 n) ∞ S] [IsManifold (𝓡 (n + 1)) ∞ Q]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    [T3Space S] [CompactSpace S] [Nonempty S] [T3Space M] [PreconnectedSpace M]
    (gQ : RiemannianMetric (n + 1) Q) (gM : RiemannianMetric (n + 1) M)
    (D : LeviCivitaData gM) (hcomplete : MetricComplete gM)
    (pi : Q → M) (hpi : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ pi)
    (hpimetric : ∀ x, ∀ a b : TangentSpace (𝓡 (n + 1)) x,
      gM.inner (pi x) (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) pi x a)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) pi x b) = gQ.inner x a b)
    (j : S → Q) (hj : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ j)
    (hj_inj : ∀ q, Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1)) j q))
    (X : (x : Q) → TangentSpace (𝓡 (n + 1)) x) (Phi : ℝ → Q → Q)
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 (n + 1))) (𝓡 (n + 1)) ∞
      (Function.uncurry Phi))
    (hcurve : ∀ x, IsMIntegralCurve (I := 𝓡 (n + 1)) (fun t => Phi t x) X)
    (h0 : ∀ x, Phi 0 x = x)
    (hact : ∀ s t x, Phi (s + t) x = Phi s (Phi t x))
    (hmetric : ∀ (t : ℝ) (x : Q) (a b : TangentSpace (𝓡 (n + 1)) x),
      gQ.inner (Phi t x) (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (Phi t) x a)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (Phi t) x b) = gQ.inner x a b)
    (htrans : ∀ q, ¬ ∃ a : TangentSpace (𝓡 n) q,
      mfderiv (𝓡 n) (𝓡 (n + 1)) j q a = X (j q)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : M, |D.scalarCurvature x| ≤ B := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n) × ℝ) (S × ℝ) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin n)) S ℝ ℝ
  let := RiemannianMetric.lineProductChartedSpace (n := n) (M := S)
  let := RiemannianMetric.lineProductIsManifold (n := n) (M := S)
  let Xi : S × ℝ → Q := fun z => Phi z.2 (j z.1)
  have hXi : IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ Xi :=
    isLocalDiffeomorph_transverseFlowout hj hj_inj hs hcurve h0 hact htrans
  have hPhi (t : ℝ) : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (Phi t) :=
    hs.comp (contMDiff_const.prodMk contMDiff_id)
  let G := gQ.pullbackOfLocalDiffeomorph Xi hXi
  have hG : MetricComplete G :=
    metricComplete_flowout_pullback gQ Phi j hPhi hact hmetric hXi
  let E : S × ℝ → M := pi ∘ Xi
  have hE : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ E :=
    hpi.comp hXi.contMDiff
  have hEinner (z : S × ℝ) (a b : TangentSpace (𝓡 (n + 1)) z) :
      gM.inner (E z) (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) E z a)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) E z b) = G.inner z a b := by
    dsimp only [E, G]
    rw [RiemannianMetric.pullbackOfLocalDiffeomorph_inner,
      mfderiv_comp z (hpi.mdifferentiable (by simp) (Xi z))
        (hXi.contMDiff.mdifferentiable (by simp) z)]
    exact hpimetric (Xi z) _ _
  have hsurj : Function.Surjective E :=
    surjective_of_complete_pullback_eq G gM hG hcomplete E hE hEinner
  let DQ := gQ.leviCivitaData
  have hpiR (y : Q) : DQ.scalarCurvature y = D.scalarCurvature (pi y) :=
    DQ.scalarCurvature_eq_of_local_isometry D isOpen_univ hpi.contMDiffOn
      (fun y _ a b => (hpimetric y a b).symm) (mem_univ y)
  have hPhiR (t : ℝ) (y : Q) :
      DQ.scalarCurvature y = DQ.scalarCurvature (Phi t y) :=
    DQ.scalarCurvature_eq_of_local_isometry DQ isOpen_univ (hPhi t).contMDiffOn
      (fun y _ a b => (hmetric t y a b).symm) (mem_univ y)
  have hscalar (z : S × ℝ) :
      D.scalarCurvature (E z) = D.scalarCurvature (pi (j z.1)) :=
    (hpiR (Xi z)).symm.trans ((hPhiR z.2 (j z.1)).symm.trans (hpiR (j z.1)))
  have hcontinuous : Continuous (fun q : S => |D.scalarCurvature (pi (j q))|) :=
    (D.continuous_scalarCurvature.comp (hpi.continuous.comp hj.continuous)).abs
  obtain ⟨C, hC⟩ := isCompact_univ.bddAbove_image hcontinuous.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro x
  obtain ⟨z, rfl⟩ := hsurj x
  rw [hscalar]
  exact (hC ⟨z.1, mem_univ _, rfl⟩).trans (le_max_left C 1)

end PoincareConjecture.M30
