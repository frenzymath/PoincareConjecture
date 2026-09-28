import PoincareConjecture.Proofs.M47.TerminalGermsMetricRegularity
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.TimeDerivative
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.TangentCone.Real

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (g : ℝ → RiemannianMetric n M) (D : ∀ t, LeviCivitaData (g t))
  (hg : RiemannianMetric.IsSmoothFamilyOn g J)
  (hinterval : J.OrdConnected) (hnontrivial : J.Nontrivial)
  (hequation : ∀ t ∈ interior J, ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
    HasDerivAt (fun s => (g s).inner x v w) (-2 * (D t).ricci x v w) t)

include hg hinterval hnontrivial hequation

theorem terminalGerms_equation_of_interior :
    ∀ t ∈ J, ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s => (g s).inner x v w) (-2 * (D t).ricci x v w) J t := by
  have hconvex : Convex ℝ J := hinterval.convex
  have hne : (interior J).Nonempty :=
    hconvex.nontrivial_iff_nonempty_interior.mp hnontrivial
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex hconvex hne
  have hdense : J ⊆ closure (interior J) := by
    rw [hconvex.closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure
  intro t ht x v w
  have hm : ContDiffOn ℝ ∞ (fun s => (g s).inner x v w) J :=
    fun s hs => hg.contDiffWithinAt_inner_time hs x v w
  have hinside : EqOn (derivWithin (fun s => (g s).inner x v w) J)
      (fun s => -2 * (D s).ricci x v w) (interior J) := by
    intro s hs
    exact (hequation s hs x v w).hasDerivWithinAt.derivWithin (hJ s (interior_subset hs))
  have heq := hinside.of_subset_closure
    (hm.continuousOn_derivWithin hJ (by simp))
    (continuousOn_const.mul (terminalGerms_continuousOn_ricci hg D x v w))
    interior_subset hdense
  exact ((hm t ht).differentiableWithinAt (by simp)).hasDerivWithinAt.congr_deriv (heq ht)

theorem terminalGerms_exists_flow_of_interior :
    ∃ F : RicciFlow n M J, F.metric = g := by
  exact ⟨{
    metric := g
    connection := D
    interval := hinterval
    nontrivial := hnontrivial
    smooth := hg
    equation := terminalGerms_equation_of_interior g D hg hinterval hnontrivial hequation }, rfl⟩

end PoincareConjecture.M47
