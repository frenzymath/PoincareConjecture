import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ContainedProfileBall
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NorthCapEndTransport
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_profile_end_replacement_below
    (P : SurgeryCapProfile) (u : UnitTwoSphere)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (hheight : ∀ p ∈ T.source, ⟪(u : E3), T p⟫_ℝ = p.2)
    (A : BallNeighborhoodChart E3 E3)
    (ell top lambda tau b ov : ℝ) (hlambda : 0 < lambda)
    (hgap : lambda * P.heightBound < top - ell)
    (hshort : lambda * P.heightBound < tau)
    (hov : 0 < ov) (hov1 : ov < 1)
    (E K : Set E3) (hK : IsClosed K)
    (hfilled : ∀ t ∈ Icc ell top,
      T '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ)) ⊆ A.closedRegion)
    (hboundary : A.boundary = E ∪
      (fun q : UnitTwoSphere =>
        T ((P.model q).1, top + lambda * (P.model q).2)) ''
          {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2})
    (hpatch : ∀ q : UnitTwoSphere, -ov < (heightCoordinates (q : E3)).2 →
      T ((P.model q).1, top + lambda * (P.model q).2) ∈ A.boundary)
    (hrim : E ∩ (fun q : UnitTwoSphere =>
      T ((P.model q).1, top + lambda * (P.model q).2)) ''
        {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} =
          T '' (sphere (0 : E2) 1 ×ˢ ({top} : Set ℝ)))
    (havoid : A.closedRegion ∩ K ⊆
      (fun q : UnitTwoSphere =>
        T ((P.model q).1, top + lambda * (P.model q).2)) ''
          {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2})
    (hupper : A.closedRegion ⊆ {y : E3 | ⟪(u : E3), y⟫_ℝ < b}) :
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let M := flatCapDiffeomorph P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    let north := (fun q : UnitTwoSphere =>
      T ((P.model q).1, top + lambda * (P.model q).2)) ''
        {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
    let south := (fun q : UnitTwoSphere =>
      T ((P.model q).1, top + lambda * (P.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    ∃ (N : BallNeighborhoodChart E3 E3)
      (G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) (C : Set E3),
      N.boundary = south ∪ north ∧
      N.chart.source = {y : E3 | ((M (heightCoordinates y)).1,
        top + lambda * (M (heightCoordinates y)).2) ∈ T.source} ∧
      N.chart.target = T.target ∧
      (∀ y : E3, N.chart y = T ((M (heightCoordinates y)).1,
        top + lambda * (M (heightCoordinates y)).2)) ∧
      (∀ y : E3, N.chart.symm y = heightCoordinates.symm
        (M.symm ((T.symm y).1, ((T.symm y).2 - top) / lambda))) ∧
      N.closedRegion ⊆ A.closedRegion ∧
      N.closedRegion ⊆ {y : E3 | |H y - top| < tau} ∧
      north = N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} ∧
      south ∩ north = T '' (sphere (0 : E2) 1 ×ˢ ({top} : Set ℝ)) ∧
      G '' E = south ∧ G.symm '' south = E ∧
      (∀ y ∈ north ∪ K ∪ {y : E3 | b ≤ H y},
        G y = y ∧ G.symm y = y) ∧
      IsCompact C ∧ C ⊆ (north ∪ K ∪ {y : E3 | b ≤ H y})ᶜ ∧
      C ⊆ {y : E3 | H y < b} ∧
      tsupport (fun y => G y - y) ⊆ C ∧
      tsupport (fun y => G.symm y - y) ⊆ C := by
  classical
  let H := InnerProductSpace.toDual ℝ E3 (u : E3)
  let north := (fun q : UnitTwoSphere =>
    T ((P.model q).1, top + lambda * (P.model q).2)) ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  let south := (fun q : UnitTwoSphere =>
    T ((P.model q).1, top + lambda * (P.model q).2)) ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  change A.boundary = E ∪ north at hboundary
  change A.closedRegion ∩ K ⊆ north at havoid
  change E ∩ north = T '' (sphere (0 : E2) 1 ×ˢ ({top} : Set ℝ)) at hrim
  change A.closedRegion ⊆ {y : E3 | H y < b} at hupper
  have hnorth : north ⊆ A.closedRegion := by
    intro y hy
    rw [← A.inside_union_boundary, hboundary]
    exact Or.inr (Or.inr hy)
  obtain ⟨N, hNb, hNs, hNt, hNp, hNi, hNc, hNshort, hNnorth, hNrim⟩ :=
    exists_saddle_contained_profile_ball P u T hsource hT hTi hheight
      A ell top lambda tau hlambda hgap hshort hfilled hnorth
  change N.boundary = south ∪ north at hNb
  change north = N.chart ''
    {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} at hNnorth
  change south ∩ north = T '' (sphere (0 : E2) 1 ×ˢ ({top} : Set ℝ)) at hNrim
  let Kfull := K ∪ {y : E3 | b ≤ H y}
  have hKfull : IsClosed Kfull := hK.union (isClosed_le continuous_const H.continuous)
  have hpatchN (q : UnitTwoSphere) (hq : -ov < (heightCoordinates (q : E3)).2) :
      N.chart (q : E3) ∈ A.boundary := by
    rw [hNp]
    exact hpatch q hq
  have hAn : A.boundary = E ∪ N.chart ''
      {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
    rw [← hNnorth]
    exact hboundary
  have hNn : N.boundary = south ∪ N.chart ''
      {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
    rw [← hNnorth]
    exact hNb
  have hmeet : E ∩ N.chart ''
      {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} =
      south ∩ N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
    rw [← hNnorth]
    exact hrim.trans hNrim.symm
  have havoidFull : A.closedRegion ∩ Kfull ⊆ N.chart ''
      {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
    rw [← hNnorth]
    rintro y ⟨hyA, hyK | hyH⟩
    · exact havoid ⟨hyA, hyK⟩
    · have hylt : H y < b := hupper hyA
      have hyle : b ≤ H y := hyH
      exact False.elim ((not_le_of_gt hylt) hyle)
  obtain ⟨G, C, hGE, hGi, hfix, hC, hCs, hsupp, hisupp⟩ :=
    exists_saddle_north_cap_end_transport A N ov hov hov1 hpatchN hNc
      E south Kfull hKfull hAn hNn hmeet havoidFull
  have hfix' : ∀ y ∈ north ∪ K ∪ {y : E3 | b ≤ H y},
      G y = y ∧ G.symm y = y := by
    simpa only [← hNnorth, Kfull, union_assoc] using hfix
  have hCs' : C ⊆ (north ∪ K ∪ {y : E3 | b ≤ H y})ᶜ := by
    simpa only [← hNnorth, Kfull, union_assoc] using hCs
  have hCbelow : C ⊆ {y : E3 | H y < b} := by
    intro y hy
    change H y < b
    exact lt_of_not_ge (fun hb => hCs' hy (Or.inr hb))
  exact ⟨N, G, C, hNb, hNs, hNt, hNp, hNi, hNc, hNshort,
    hNnorth, hNrim, hGE, hGi, hfix', hC, hCs', hCbelow, hsupp, hisupp⟩

end PoincareConjecture.M25.Topology3D
