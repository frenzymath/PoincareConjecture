import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallEventGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReunionMap











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem RegularSurgeryEvent.exists_event_reunion_diffeomorph
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) (i : Fin 2) :
    let a := E.data.width / 2 * (1 - E.radius)
    let sigma : ℝ := ![1, -1] i
    let core := (fun p : UnitTwoSphere => parent (p, 0)) ''
      ((![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i) ''
        closedBall (0 : E2) E.radius)
    let annulus := E.data.tube ''
      (sphere (0 : E2) 1 ×ˢ Ioo (E.cutHeight - a) (E.cutHeight + a))
    let north := E.profile.capMap E.data.tube E.cutHeight (-sigma) a E.scale ''
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
    ∃ G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      ∃ S : Set E3, IsCompact S ∧
        S ⊆ E.data.tube.target \ (core ∪ (E.newCap i).seam) ∧
        tsupport (fun y => G y - y) ⊆ S ∧
        tsupport (fun y => G.symm y - y) ⊆ S ∧
        (∀ y ∈ core ∪ (E.newCap i).seam, G y = y ∧ G.symm y = y) ∧
        G '' (E.newCap i).cap = (E.newCap i).seam ∪ annulus ∪ north ∧
        G.symm '' ((E.newCap i).seam ∪ annulus ∪ north) = (E.newCap i).cap ∧
        G '' (E.child i '' (univ ×ˢ ({0} : Set ℝ))) = core ∪ annulus ∪ north ∧
        G.symm '' (core ∪ annulus ∪ north) =
          E.child i '' (univ ×ˢ ({0} : Set ℝ)) := by
  let a := E.data.width / 2 * (1 - E.radius)
  let sigma : ℝ := ![1, -1] i
  let core := (fun p : UnitTwoSphere => parent (p, 0)) ''
    ((![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative] i) ''
      closedBall (0 : E2) E.radius)
  let annulus := E.data.tube ''
    (sphere (0 : E2) 1 ×ˢ Ioo (E.cutHeight - a) (E.cutHeight + a))
  let north := E.profile.capMap E.data.tube E.cutHeight (-sigma) a E.scale ''
    {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  obtain ⟨_happ, _hsourceEq, htarget, _hinverse, hsource, hT, hTi, _hheight⟩ :=
    E.reunionTube_spec i
  obtain ⟨_hdelta, ha, had, _hkd, hl, hsmall⟩ := E.parameter_bounds
  obtain ⟨G, S, hS, hSwhere, hs, his, hfix, hcapImage, hcapInverse⟩ :=
    exists_reunion_diffeomorph E.profile (E.reunionTube i) hsource hT hTi
      E.data.width a E.scale ha had hl hsmall core
      (E.reunion_core_isCompact i) (E.reunion_core_disjoint_strip i)
  obtain ⟨hcap, hseam, _hotherSeam, _hphysicalSeam, _hphysicalOtherSeam,
      hannulus, _hclosed, _hclosedUnion, hnorth, _hequator, _hseamNorth, _hinter⟩ :=
    E.reunion_region_identities i
  rw [htarget, hseam] at hSwhere
  rw [hseam] at hfix
  rw [hcap, hseam, hannulus, hnorth] at hcapImage hcapInverse
  obtain ⟨_hparent, _hcoreAnnulus, _hcoreDisjoint, hchild, hcoreCap, _hchildren⟩ :=
    E.region_identities
  have hchildImage : E.child i '' (univ ×ˢ ({0} : Set ℝ)) =
      core ∪ (E.newCap i).cap := hchild i
  have hseamCore : (E.newCap i).seam ⊆ core := by
    intro y hy
    have hmem : y ∈ core ∩ (E.newCap i).cap := by
      rw [hcoreCap i]
      exact hy
    exact hmem.1
  have hcoreImage : G '' core = core := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [(hfix x (Or.inl hx)).1]
      exact hx
    · intro hy
      exact ⟨y, hy, (hfix y (Or.inl hy)).1⟩
  have hwhole : G '' (E.child i '' (univ ×ˢ ({0} : Set ℝ))) =
      core ∪ annulus ∪ north := by
    rw [hchildImage, image_union, hcoreImage, hcapImage]
    apply Subset.antisymm
    · rintro y (hy | ((hy | hy) | hy))
      · exact Or.inl (Or.inl hy)
      · exact Or.inl (Or.inl (hseamCore hy))
      · exact Or.inl (Or.inr hy)
      · exact Or.inr hy
    · rintro y ((hy | hy) | hy)
      · exact Or.inl hy
      · exact Or.inr (Or.inl (Or.inr hy))
      · exact Or.inr (Or.inr hy)
  refine ⟨G, S, hS, hSwhere, hs, his, hfix, hcapImage, hcapInverse, hwhole, ?_⟩
  rw [← hwhole, image_image]
  change (fun y : E3 => G.symm (G y)) ''
    (E.child i '' (univ ×ˢ ({0} : Set ℝ))) = _
  simpa only [G.symm_apply_apply] using
    (image_id' (E.child i '' (univ ×ˢ ({0} : Set ℝ))))

end PoincareConjecture.M25.Topology3D
