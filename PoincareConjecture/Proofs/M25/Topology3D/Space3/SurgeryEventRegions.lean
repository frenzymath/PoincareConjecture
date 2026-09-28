import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryEvent
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryRegionIdentities











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem RegularSurgeryEvent.region_identities
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) :
    let c := E.data.width / 2 * (1 - E.radius)
    let e : Fin 2 → OpenPartialHomeomorph E2 UnitTwoSphere :=
      ![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative]
    let core : Fin 2 → Set E3 := fun i =>
      (fun p : UnitTwoSphere => parent (p, 0)) ''
        (e i '' closedBall (0 : E2) E.radius)
    let annulus := E.data.tube ''
      (sphere (0 : E2) 1 ×ˢ Ioo (E.cutHeight - c) (E.cutHeight + c))
    parent '' (univ ×ˢ ({0} : Set ℝ)) = core 0 ∪ core 1 ∪ annulus ∧
      (∀ i : Fin 2, Disjoint (core i) annulus) ∧
      Disjoint (core 0) (core 1) ∧
      (∀ i : Fin 2, E.child i '' (univ ×ˢ ({0} : Set ℝ)) =
        core i ∪ (E.newCap i).cap) ∧
      (∀ i : Fin 2, core i ∩ (E.newCap i).cap = (E.newCap i).seam) ∧
      Disjoint (E.child 0 '' (univ ×ˢ ({0} : Set ℝ)))
        (E.child 1 '' (univ ×ˢ ({0} : Set ℝ))) := by
  let c := E.data.width / 2 * (1 - E.radius)
  let e : Fin 2 → OpenPartialHomeomorph E2 UnitTwoSphere :=
    ![E.data.sourceDiscs.positive, E.data.sourceDiscs.negative]
  let sigma : Fin 2 → ℝ := ![1, -1]
  let core : Fin 2 → Set E3 := fun i =>
    (fun p : UnitTwoSphere => parent (p, 0)) '' (e i '' closedBall 0 E.radius)
  let annulus := E.data.tube ''
    (sphere (0 : E2) 1 ×ˢ Ioo (E.cutHeight - c) (E.cutHeight + c))
  change parent '' (univ ×ˢ ({0} : Set ℝ)) = core 0 ∪ core 1 ∪ annulus ∧
    (∀ i : Fin 2, Disjoint (core i) annulus) ∧ Disjoint (core 0) (core 1) ∧
    (∀ i : Fin 2, E.child i '' (univ ×ˢ ({0} : Set ℝ)) = core i ∪ (E.newCap i).cap) ∧
    (∀ i : Fin 2, core i ∩ (E.newCap i).cap = (E.newCap i).seam) ∧
    Disjoint (E.child 0 '' (univ ×ˢ ({0} : Set ℝ)))
      (E.child 1 '' (univ ×ˢ ({0} : Set ℝ)))
  obtain ⟨_hd, _hc, hck, hkw, hl, hlM⟩ := E.parameter_bounds
  have hk : 0 < E.data.width / 2 := by linarith [E.data.width_pos]
  have hcw : c < E.data.width := hck.trans hkw
  have hsigma (i : Fin 2) : |sigma i| = 1 := by fin_cases i <;> norm_num [sigma]
  have hsource (i : Fin 2) : closedBall (0 : E2) 1 ⊆ (e i).source := by
    fin_cases i
    · exact E.data.sourceDiscs.positive_source
    · exact E.data.sourceDiscs.negative_source
  have hzero (f : UnitTwoSphere × ℝ → E3) :
      f '' (univ ×ˢ ({0} : Set ℝ)) = range (fun p : UnitTwoSphere => f (p, 0)) := by
    ext y
    constructor
    · rintro ⟨⟨p, s⟩, hs, rfl⟩
      have hs0 : s = 0 := hs.2
      subst s
      exact mem_range_self p
    · rintro ⟨p, rfl⟩
      exact ⟨(p, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hchildImage (i : Fin 2) : E.child i '' (univ ×ˢ ({0} : Set ℝ)) =
      range (E.profile.replacementMap parent E.matching (e i) E.data.tube
        E.cutHeight (sigma i) E.radius (E.data.width / 2) E.scale) := by
    rw [hzero]
    congr 1
    funext p
    exact E.child_central i p
  have hcap (i : Fin 2) : (E.newCap i).cap =
      E.profile.capMap E.data.tube E.cutHeight (sigma i) c E.scale ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} := by
    obtain ⟨hp, hT, ht, hc, hl, hs⟩ := E.newCap_spec i
    rw [(E.newCap i).cap_eq_image, hp, hT, ht, hc, hl, hs]
  have hseam (i : Fin 2) : (E.newCap i).seam =
      E.data.tube '' (sphere (0 : E2) 1 ×ˢ ({E.cutHeight + sigma i * c} : Set ℝ)) := by
    obtain ⟨hp, hT, ht, hc, hl, hs⟩ := E.newCap_spec i
    rw [(E.newCap i).seam_eq_image, hp, hT, ht, hc, hl, hs]
    exact surgery_cap_equator_image E.profile E.data.tube E.cutHeight (sigma i) c E.scale
  obtain ⟨hparent, hannulus, hcores⟩ := surgery_parent_region_identities
    parent E.parent_embedding u E.cutHeight E.data E.radius_mem.1 E.radius_mem.2
      E.radius_near E.radial
  refine ⟨(hzero parent).trans hparent, hannulus, hcores, ?_, ?_, ?_⟩
  · intro i
    rw [hchildImage, hcap]
    exact E.profile.replacementMap_range parent u E.cutHeight E.data E.matching
      (e i) (sigma i) (hsigma i) E.radius_mem.1 E.radius_mem.2 E.radius_near hk hcw
      E.matching_closedBall E.matching_circle (E.radial i)
  · intro i
    rw [hcap, hseam]
    exact surgery_retained_cap_intersection E.profile parent E.parent_embedding u
      E.cutHeight E.data (e i) (hsource i) (sigma i) (hsigma i)
      E.radius_mem.1 E.radius_mem.2 E.radius_near hk hcw (E.radial i) hl hlM
  · rw [hchildImage, hchildImage]
    exact E.profile.replacementMap_disjoint_pair parent E.parent_embedding u
      E.cutHeight E.data E.matching E.radius_mem.1 E.radius_mem.2 E.radius_near hcw
      hl hlM E.matching_closedBall E.matching_circle
      (by simpa using E.radial 0) (by simpa using E.radial 1)

end PoincareConjecture.M25.Topology3D
