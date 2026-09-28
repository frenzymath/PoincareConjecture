import PoincareConjecture.Proofs.M25.Topology3D.Space3.SouthernSphereChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D.SurgeryCapTag

local notation "CINF" => ((Top.top : ENat) : WithTop ENat)



noncomputable def of_cap_patch
    (P : SurgeryCapProfile) (psi : Prod UnitTwoSphere Real -> E3) (u : UnitTwoSphere)
    (T : OpenPartialHomeomorph (Prod E2 Real) E3)
    (hsource : Set.Subset (Set.prod (closedBall (0 : E2) 1) (univ : Set Real)) T.source)
    (hT : ContDiffOn Real CINF T T.source)
    (hTi : ContDiffOn Real CINF T.symm T.target)
    (hheight : forall p, T.source p -> inner Real (u : E3) (T p) = p.2)
    (t c l sigma : Real) (hc : 0 < c) (hl : 0 < l) (hsigma : abs sigma = 1)
    (hlM : l * P.heightBound < c / 4)
    (eta : Real) (heta : 0 < eta) (heta1 : eta <= 1 / 4)
    (hcentral : forall q : UnitTwoSphere, (heightCoordinates (q : E3)).2 < eta ->
      psi (q, 0) = P.capMap T t sigma c l q)
    (beta : Real) (hbeta : Ne beta 0)
    (width : Real) (hwidth : 0 < width) (hwidth1 : width <= 1)
    (hflat : forall q : UnitTwoSphere, (heightCoordinates (q : E3)).2 <= 0 ->
      norm (heightCoordinates (q : E3)).1 <= 1 / 8 ->
      forall s : Real, abs s < width ->
        psi (q, s) = T ((heightCoordinates (q : E3)).1,
          t + sigma * (c - l) + beta * s)) : SurgeryCapTag psi u := by
  refine {
    profile := P
    cutHeight := t
    removal := c
    scale := l
    sign := sigma
    removal_pos := hc
    scale_pos := hl
    sign_abs := hsigma
    scale_small := hlM
    tube := T
    tube_source := hsource
    tube_smooth := hT
    tube_inverse := hTi
    tube_height := hheight
    sourceChart := OpenPartialHomeomorph.refl UnitTwoSphere
    source_smooth := contMDiff_id.contMDiffOn
    source_inverse := contMDiff_id.contMDiffOn
    overlapWidth := eta
    overlap_pos := heta
    overlap_le := heta1
    source_band := fun _ _ => mem_univ _
    central_eq := hcentral
    flatChart := southSphereChart
    flat_source := ?_
    flat_smooth := southSphereChart_contMDiff.1
    flat_inverse := southSphereChart_contMDiff.2
    flat_eq := ?_
    beta := beta
    beta_ne := hbeta
    collarWidth := width
    collar_pos := hwidth
    collar_le := hwidth1
    collar_eq := ?_ }
  · intro x hx
    apply mem_ball_zero_iff.mpr
    have hn := mem_closedBall_zero_iff.mp hx
    linarith
  · intro q hq hx
    have hs := sphere_height_coordinates_sq q
    have hneg : (heightCoordinates (q : E3)).2 < 0 := by
      have hn := norm_nonneg (heightCoordinates (q : E3)).1
      by_contra h
      have hz : (heightCoordinates (q : E3)).2 = 0 := le_antisymm hq (le_of_not_gt h)
      rw [hz] at hs
      nlinarith
    exact (southSpherePoint_coordinate q hneg).2
  · intro x hx s hs
    have hx1 : norm x < 1 := by linarith
    have hcoords := southSpherePoint_coordinates x hx1
    have hnonpos : (heightCoordinates (southSpherePoint x : E3)).2 <= 0 := by
      rw [hcoords]
      exact neg_nonpos.mpr (Real.sqrt_nonneg _)
    have heq := hflat (southSpherePoint x) hnonpos (by rw [hcoords]; exact hx) s hs
    change psi (southSpherePoint x, s) = _
    simpa only [hcoords] using heq

end PoincareConjecture.M25.Topology3D.SurgeryCapTag
