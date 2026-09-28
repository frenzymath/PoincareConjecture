import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularHorizontalTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlowTube
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable (Φ : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
variable (hΦ : ContDiff ℝ ∞ (fun p : ℝ × E2 => Φ p.1 p.2))
variable (hi : ContDiff ℝ ∞ (fun p : ℝ × E2 => (Φ p.1).symm p.2))

noncomputable def planarFamilyGraphDiffeomorph :
    Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ) (E2 × ℝ) (E2 × ℝ) ∞ where
  toEquiv := {
    toFun := fun p => (Φ p.2 p.1, p.2)
    invFun := fun p => ((Φ p.2).symm p.1, p.2)
    left_inv := fun p => Prod.ext ((Φ p.2).symm_apply_apply p.1) rfl
    right_inv := fun p => Prod.ext ((Φ p.2).apply_symm_apply p.1) rfl }
  contMDiff_toFun := ((hΦ.comp (contDiff_snd.prodMk contDiff_fst)).prodMk
    contDiff_snd).contMDiff
  contMDiff_invFun := ((hi.comp (contDiff_snd.prodMk contDiff_fst)).prodMk
    contDiff_snd).contMDiff

noncomputable def horizontalTubeChart (u : UnitTwoSphere) (B : BallNeighborhoodChart E2 E2) :
    OpenPartialHomeomorph (E2 × ℝ) E3 :=
  (B.chart.prod (OpenPartialHomeomorph.refl ℝ)).trans
    ((planarFamilyGraphDiffeomorph Φ hΦ hi).trans
      (heightPlaneCoordinates u).symm.toDiffeomorph).toHomeomorph.toOpenPartialHomeomorph

theorem horizontalTubeChart_apply (u : UnitTwoSphere) (B : BallNeighborhoodChart E2 E2)
    (p : E2 × ℝ) : horizontalTubeChart Φ hΦ hi u B p =
      (heightPlaneCoordinates u).symm (Φ p.2 (B.chart p.1), p.2) := rfl

theorem horizontalTubeChart_source (u : UnitTwoSphere) (B : BallNeighborhoodChart E2 E2) :
    (horizontalTubeChart Φ hΦ hi u B).source = B.chart.source ×ˢ (univ : Set ℝ) := by
  ext p
  simp [horizontalTubeChart]

theorem horizontalTubeChart_closedBall_subset_source (u : UnitTwoSphere)
    (B : BallNeighborhoodChart E2 E2) :
    closedBall 0 1 ×ˢ (univ : Set ℝ) ⊆ (horizontalTubeChart Φ hΦ hi u B).source := by
  rw [horizontalTubeChart_source]
  exact prod_mono B.closedBall_subset_source (subset_refl _)

theorem horizontalTubeChart_contDiffOn (u : UnitTwoSphere) (B : BallNeighborhoodChart E2 E2) :
    ContDiffOn ℝ ∞ (horizontalTubeChart Φ hΦ hi u B)
      (horizontalTubeChart Φ hΦ hi u B).source := by
  rw [horizontalTubeChart_source]
  exact ((planarFamilyGraphDiffeomorph Φ hΦ hi).trans
    (heightPlaneCoordinates u).symm.toDiffeomorph).contMDiff_toFun.contDiff.comp_contDiffOn
      (B.smooth.prodMap contDiff_id.contDiffOn)

theorem horizontalTubeChart_symm_contDiffOn (u : UnitTwoSphere)
    (B : BallNeighborhoodChart E2 E2) :
    ContDiffOn ℝ ∞ (horizontalTubeChart Φ hΦ hi u B).symm
      (horizontalTubeChart Φ hΦ hi u B).target :=
  (B.smooth_symm.prodMap contDiff_id.contDiffOn).comp
    ((planarFamilyGraphDiffeomorph Φ hΦ hi).trans
      (heightPlaneCoordinates u).symm.toDiffeomorph).contMDiff_invFun.contDiff.contDiffOn
        (fun _ hp => hp.2)

theorem horizontalTubeChart_height (u : UnitTwoSphere) (B : BallNeighborhoodChart E2 E2)
    (p : E2 × ℝ) : ⟪(u : E3), horizontalTubeChart Φ hΦ hi u B p⟫_ℝ = p.2 := by
  rw [horizontalTubeChart_apply, ← heightPlaneCoordinates_snd]
  rw [ContinuousLinearEquiv.apply_symm_apply]

end PoincareConjecture.M25.Topology3D
