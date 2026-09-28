import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Flow.CenteredGlobal
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Flow.Euclidean

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {N : Type*} [TopologicalSpace N] [T3Space N]
  [ConnectedSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]

theorem exists_euclidean_diffeomorph_of_singleton_horoball
    (g : RiemannianMetric n N) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    {o p : N} {c : ℝ}
    (hlevel : letI := g.toMetricSpace;
      Poincare.Riemannian.Soul.horoballIntersection o c = {p}) :
    ∃ e : Diffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) N ∞, e 0 = p := by
  obtain ⟨f, Y, Φ, hf, hfnear, hY, _, hYnear, hzero, horbit, hadd, hs, _, _, hradius⟩ :=
    g.exists_centered_complete_outward_flow_of_singleton_horoball D hc hsec hlevel
  exact g.exists_diffeomorph_of_centered_radial_flow p hf hfnear hY hYnear
    hzero horbit hadd hs hradius

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [NoncompactSpace M]

theorem exists_euclidean_diffeomorph_of_point_soul
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g)
    (hpos : D.StrictlyPositiveSectionalCurvature)
    {p : M} (hp : TotallyConvexSet g ({p} : Set M)) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3)
      (EuclideanSpace ℝ (Fin 3)) M ∞, e 0 = p := by
  obtain ⟨q, o, c, hlevel, _⟩ :=
    g.exists_singleton_horoball_of_strictlyPositiveSectionalCurvature D hcomplete hpos
  obtain ⟨e, _⟩ := g.exists_euclidean_diffeomorph_of_singleton_horoball D hcomplete
    (hpos.nonnegative D) hlevel
  let E := EuclideanSpace ℝ (Fin 3)
  let T : Diffeomorph (𝓡 3) (𝓡 3) E E ∞ := {
    toFun := fun v => v + e.symm p
    invFun := fun v => v - e.symm p
    left_inv := fun v => add_sub_cancel_right v _
    right_inv := fun v => sub_add_cancel v _
    contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
    contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff
  }
  refine ⟨T.trans e, ?_⟩
  change e (0 + e.symm p) = p
  rw [zero_add, e.apply_symm_apply]

end PoincareConjecture.RiemannianMetric
