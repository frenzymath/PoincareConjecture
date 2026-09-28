import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.EventLevelDeletion
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalTubeChart










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem RegularSurgeryEvent.family_horizontal_levels_delete
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u)
    (R : Set E3)
    (hR : Disjoint R (parent '' (univ ×ˢ ({0} : Set ℝ))))
    (m : ℕ) (B : Fin m → BallNeighborhoodChart E2 E2)
    (hdisjoint : Pairwise (fun i j : Fin m =>
      Disjoint (B i).boundary (B j).boundary))
    (k : Fin m)
    (Phi : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (hPhi : ContDiff ℝ ∞ (fun p : ℝ × E2 => Phi p.1 p.2))
    (hinverse : ContDiff ℝ ∞ (fun p : ℝ × E2 => (Phi p.1).symm p.2))
    (htube : E.data.tube = horizontalTubeChart Phi hPhi hinverse u (B k))
    (hlevel : ∀ z ∈ Ioo (E.cutHeight - E.data.width)
        (E.cutHeight + E.data.width), ∀ p : E2,
      (heightPlaneCoordinates u).symm (Phi z p, z) ∈
        (parent '' (univ ×ˢ ({0} : Set ℝ))) ∪ R ↔
          p ∈ (⋃ i : Fin m, (B i).boundary)) :
    let c := E.data.width / 2 * (1 - E.radius)
    ∀ z ∈ Ioo (E.cutHeight - c / 2) (E.cutHeight + c / 2),
      ∀ p : E2,
        (heightPlaneCoordinates u).symm (Phi z p, z) ∈
          ((E.child 0 '' (univ ×ˢ ({0} : Set ℝ))) ∪
            (E.child 1 '' (univ ×ˢ ({0} : Set ℝ)))) ∪ R ↔
          p ∈ (⋃ i : {i : Fin m // i ≠ k}, (B i.1).boundary) := by
  let c := E.data.width / 2 * (1 - E.radius)
  let P := parent '' (univ ×ˢ ({0} : Set ℝ))
  let Q := (E.child 0 '' (univ ×ˢ ({0} : Set ℝ))) ∪
    (E.child 1 '' (univ ×ˢ ({0} : Set ℝ)))
  obtain ⟨_hd, hc, hck, hkw, _hl, _hlM⟩ := E.parameter_bounds
  change 0 < c at hc
  have hcw : c < E.data.width := hck.trans hkw
  change ∀ z ∈ Ioo (E.cutHeight - c / 2) (E.cutHeight + c / 2),
    ∀ p : E2, (heightPlaneCoordinates u).symm (Phi z p, z) ∈ Q ∪ R ↔
      p ∈ (⋃ i : {i : Fin m // i ≠ k}, (B i.1).boundary)
  intro z hz p
  let y := (heightPlaneCoordinates u).symm (Phi z p, z)
  let Az := E.data.tube '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))
  have hzabs : |z - E.cutHeight| < c / 2 :=
    abs_lt.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hzbig : z ∈ Ioo (E.cutHeight - E.data.width) (E.cutHeight + E.data.width) :=
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hyz : ⟪(u : E3), y⟫_ℝ = z := by
    dsimp only [y]
    rw [← heightPlaneCoordinates_snd, ContinuousLinearEquiv.apply_symm_apply]
  have hAzparent : Az ⊆ P := by
    rintro v ⟨⟨x, w⟩, ⟨hx, hw⟩, heq⟩
    have hwz : w = z := hw
    subst w
    have hparent := E.region_identities.1
    change parent '' (univ ×ˢ ({0} : Set ℝ)) = _ at hparent
    change v ∈ parent '' (univ ×ˢ ({0} : Set ℝ))
    rw [hparent]
    refine Or.inr ⟨(x, z), ⟨hx, ?_⟩, heq⟩
    exact ⟨by change E.cutHeight - c < z; linarith [hz.1],
      by change z < E.cutHeight + c; linarith [hz.2]⟩
  have hchild : y ∈ Q ↔ y ∈ P ∧ y ∉ Az := by
    have hdelete := E.children_middle_level z hzabs
    change Q ∩ {v : E3 | ⟪(u : E3), v⟫_ℝ = z} =
      (P ∩ {v : E3 | ⟪(u : E3), v⟫_ℝ = z}) \ Az at hdelete
    constructor
    · intro hyQ
      have hy := (Set.ext_iff.mp hdelete y).mp ⟨hyQ, hyz⟩
      exact ⟨hy.1.1, hy.2⟩
    · rintro ⟨hyP, hyAz⟩
      exact ((Set.ext_iff.mp hdelete y).mpr ⟨⟨hyP, hyz⟩, hyAz⟩).1
  have hfamily : y ∈ Q ∪ R ↔ y ∈ P ∪ R ∧ y ∉ Az := by
    constructor
    · rintro (hyQ | hyR)
      · obtain ⟨hyP, hyAz⟩ := hchild.mp hyQ
        exact ⟨Or.inl hyP, hyAz⟩
      · exact ⟨Or.inr hyR, fun hyAz => disjoint_left.mp hR hyR (hAzparent hyAz)⟩
    · rintro ⟨hy, hyAz⟩
      rcases hy with hyP | hyR
      · exact Or.inl (hchild.mpr ⟨hyP, hyAz⟩)
      · exact Or.inr hyR
  have hcircle : y ∈ Az ↔ p ∈ (B k).boundary := by
    constructor
    · rintro ⟨⟨x, w⟩, ⟨hx, hw⟩, heq⟩
      have hwz : w = z := hw
      subst w
      rw [htube, horizontalTubeChart_apply] at heq
      change (heightPlaneCoordinates u).symm (Phi z ((B k).chart x), z) =
        (heightPlaneCoordinates u).symm (Phi z p, z) at heq
      have hxp : (B k).chart x = p := (Phi z).injective
        (congrArg Prod.fst ((heightPlaneCoordinates u).symm.injective heq))
      exact ⟨x, hx, hxp⟩
    · rintro ⟨x, hx, hxp⟩
      refine ⟨(x, z), ⟨hx, rfl⟩, ?_⟩
      rw [htube, horizontalTubeChart_apply, hxp]
  have hold : y ∈ P ∪ R ↔ p ∈ (⋃ i : Fin m, (B i).boundary) := hlevel z hzbig p
  change y ∈ Q ∪ R ↔ p ∈ (⋃ i : {i : Fin m // i ≠ k}, (B i.1).boundary)
  rw [hfamily, hold, hcircle]
  constructor
  · rintro ⟨hp, hpk⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    have hik : i ≠ k := fun hik => hpk (hik ▸ hi)
    exact mem_iUnion.mpr ⟨⟨i, hik⟩, hi⟩
  · intro hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact ⟨mem_iUnion.mpr ⟨i.1, hi⟩,
      fun hk => disjoint_left.mp (hdisjoint i.2) hi hk⟩

end PoincareConjecture.M25.Topology3D
