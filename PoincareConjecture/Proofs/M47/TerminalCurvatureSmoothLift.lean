import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Covering.LocalDiffeomorph
import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Topology.Homotopy.Lifting










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47



theorem terminalCurvature_exists_smooth_cover_lift
    {n k : ℕ} {M N A : Type*}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace A]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [ChartedSpace (EuclideanSpace ℝ (Fin k)) A]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N] [IsManifold (𝓡 k) ∞ A]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    {projection : N → M} (hcover : IsCoveringMap projection)
    (hlocal : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ projection)
    (f : A → M) (hf : ContMDiff (𝓡 k) (𝓡 n) ∞ f)
    (a0 : A) (p0 : N) (hp0 : projection p0 = f a0) :
    ∃ F : A → N, ContMDiff (𝓡 k) (𝓡 n) ∞ F ∧ F a0 = p0 ∧
      (∀ a, projection (F a) = f a) ∧
      ∀ a, (mfderiv (𝓡 n) (𝓡 n) projection (F a)).comp
        (mfderiv (𝓡 k) (𝓡 n) F a) = mfderiv (𝓡 k) (𝓡 n) f a := by
  obtain ⟨F, ⟨hF0, hproj⟩, _⟩ := hcover.existsUnique_continuousMap_lifts
    ⟨f, hf.continuous⟩ a0 p0 hp0
  have heq (a : A) : projection (F a) = f a := congrFun hproj a
  have hF : ContMDiff (𝓡 k) (𝓡 n) ∞ F := by
    intro a
    let hi := hlocal (F a)
    have hinv : ContMDiffAt (𝓡 n) (𝓡 n) ∞ hi.localInverse (f a) := by
      rw [← heq a]
      exact hi.localInverse_contMDiffAt
    have hevent : (fun z => hi.localInverse (f z)) =ᶠ[𝓝 a] F := by
      filter_upwards [F.continuous.continuousAt.eventually
        hi.localInverse_eventuallyEq_left] with z hz
      simpa only [Function.comp_apply, id_eq, heq] using hz
    exact (hinv.comp a (hf a)).congr_of_eventuallyEq hevent.symm
  refine ⟨F, hF, hF0, heq, ?_⟩
  intro a
  have hd := mfderiv_comp a ((hlocal (F a)).mdifferentiableAt (by simp))
    ((hF a).mdifferentiableAt (by simp))
  rw [hproj] at hd
  exact hd.symm

end PoincareConjecture.M47
