import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Collars.PolygonLocalJordanSide
import PoincareConjecture.Proofs.M76.Brown.HalfspaceLocalCollars
import PoincareConjecture.Proofs.M76.Brown.CompactCollaring









set_option autoImplicit false

open Set BrownCollar

namespace Polygon

theorem exists_exterior_halfspace_chart {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) {q : ℝ × ℝ} (hq : q ∈ P.boundary ℝ) :
    ∃ B : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ), q ∈ B.source ∧
      (∀ x ∈ B.source, x ∈ P.boundary ℝ ↔ (B x).2 = 0) ∧
      (∀ x ∈ B.source, x ∈ P.insideᶜ ↔ 0 ≤ (B x).2) ∧
      ∀ x ∈ B.source, x ∈ P.outside ↔ 0 < (B x).2 := by
  obtain ⟨e, δ, hδ, he, hmodel, hsides⟩ :=
    P.exists_local_jordan_half_rectangles hP hinj hq
  let J := Ioo ((e q).1 - δ) ((e q).1 + δ)
  let U := e ⁻¹' (J ×ˢ Ioo (-δ) δ)
  let B := e.toOpenPartialHomeomorph.restr U
  have hU : IsOpen U := (isOpen_Ioo.prod isOpen_Ioo).preimage e.continuous
  have hsource : B.source = U := by
    simp only [B, OpenPartialHomeomorph.restr_source' _ _ hU,
      Homeomorph.toOpenPartialHomeomorph_source, univ_inter]
  have hqB : q ∈ B.source := by
    rw [hsource]
    change (e q).1 ∈ J ∧ (e q).2 ∈ Ioo (-δ) δ
    rw [he]
    exact ⟨⟨sub_lt_self _ hδ, lt_add_of_pos_right _ hδ⟩, neg_lt_zero.mpr hδ, hδ⟩
  have hpair (x : ℝ × ℝ) (hx : x ∈ B.source) :
      x ∈ P.boundary ℝ ↔ (B x).2 = 0 := by
    rw [hsource] at hx
    exact hmodel x hx
  have hnegative (hL : e ⁻¹' (J ×ˢ Ioo (-δ) 0) ⊆ P.inside)
      (hR : e ⁻¹' (J ×ˢ Ioo 0 δ) ⊆ P.outside) :
      (∀ x ∈ B.source, x ∈ P.inside ↔ (B x).2 < 0) ∧
      ∀ x ∈ B.source, x ∈ P.outside ↔ 0 < (B x).2 := by
    constructor
    · intro x hx
      have hxU : x ∈ U := hsource ▸ hx
      constructor
      · intro hi
        rcases lt_trichotomy (e x).2 0 with hn | hz | hp
        · exact hn
        · exact False.elim (hi.1 ((hmodel x hxU).mpr hz))
        · exact False.elim (Set.disjoint_left.mp P.disjoint_inside_outside hi
            (hR ⟨hxU.1, hp, hxU.2.2⟩))
      · intro hn
        exact hL ⟨hxU.1, hxU.2.1, hn⟩
    · intro x hx
      have hxU : x ∈ U := hsource ▸ hx
      constructor
      · intro ho
        rcases lt_trichotomy (e x).2 0 with hn | hz | hp
        · exact False.elim (Set.disjoint_left.mp P.disjoint_inside_outside
            (hL ⟨hxU.1, hxU.2.1, hn⟩) ho)
        · exact False.elim (ho.1 ((hmodel x hxU).mpr hz))
        · exact hp
      · intro hp
        exact hR ⟨hxU.1, hp, hxU.2.2⟩
  rcases hsides with ⟨hL, hR⟩ | ⟨hR, hL⟩
  · obtain ⟨hi, ho⟩ := hnegative hL hR
    exact ⟨B, hqB, hpair, fun x hx => by
      change x ∉ P.inside ↔ 0 ≤ (B x).2
      rw [hi x hx, not_lt], ho⟩
  · let C := B.transHomeomorph ((Homeomorph.refl ℝ).prodCongr (Homeomorph.neg ℝ))
    have hi (x : ℝ × ℝ) (hx : x ∈ B.source) : x ∈ P.inside ↔ 0 < (B x).2 := by
      have hxU : x ∈ U := hsource ▸ hx
      constructor
      · intro hi
        rcases lt_trichotomy (e x).2 0 with hn | hz | hp
        · exact False.elim (Set.disjoint_left.mp P.disjoint_inside_outside hi
            (hL ⟨hxU.1, hxU.2.1, hn⟩))
        · exact False.elim (hi.1 ((hmodel x hxU).mpr hz))
        · exact hp
      · intro hp
        exact hR ⟨hxU.1, hp, hxU.2.2⟩
    refine ⟨C, hqB, ?_, ?_, ?_⟩
    · intro x hx
      change x ∈ P.boundary ℝ ↔ -(B x).2 = 0
      rw [neg_eq_zero]
      exact hpair x hx
    · intro x hx
      change x ∉ P.inside ↔ 0 ≤ -(B x).2
      rw [hi x hx, not_lt, neg_nonneg]
    · intro x hx
      change x ∈ P.outside ↔ 0 < -(B x).2
      rw [neg_pos]
      have hxU : x ∈ U := hsource ▸ hx
      constructor
      · intro ho
        rcases lt_trichotomy (e x).2 0 with hn | hz | hp
        · exact hn
        · exact False.elim (ho.1 ((hmodel x hxU).mpr hz))
        · exact False.elim (Set.disjoint_left.mp P.disjoint_inside_outside
            (hR ⟨hxU.1, hp, hxU.2.2⟩) ho)
      · intro hn
        exact hL ⟨hxU.1, hxU.2.1, hn⟩

theorem exists_exterior_local_collar {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (q : P.boundary ℝ) :
    ∃ c : OpenPartialHomeomorph (P.boundary ℝ × Ico (0 : ℝ) 1)
      (Set.compl (P.inside : Set (ℝ × ℝ))),
      collarBase q ∈ c.source ∧
      ∀ (a : P.boundary ℝ), collarBase a ∈ c.source →
        (c (collarBase a) : ℝ × ℝ) = (a : ℝ × ℝ) := by
  have hsub : P.boundary ℝ ⊆ (P.inside)ᶜ := fun _ hb hi => hi.1 hb
  obtain ⟨B, hq, hpair, hside, _⟩ := P.exists_exterior_halfspace_chart hP hinj q.property
  obtain ⟨c, hc, hbase⟩ := exists_positive_halfspace_local_collar B hsub hpair hside q hq
  exact ⟨c, hc, fun a ha => congrArg Subtype.val (hbase a ha)⟩

theorem exists_exterior_full_collar {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) :
    ∃ U : Set (Set.compl (P.inside : Set (ℝ × ℝ))), IsOpen U ∧
      Set.range (Set.inclusion (show P.boundary ℝ ⊆ Set.compl (P.inside : Set (ℝ × ℝ)) from
        fun _ hb hi => hi.1 hb)) ⊆ U ∧
      ∃ c : (P.boundary ℝ × Ico (0 : ℝ) 1) ≃ₜ U,
        ∀ a, (c (collarBase a) : Set.compl (P.inside : Set (ℝ × ℝ))) =
          Set.inclusion (show P.boundary ℝ ⊆ Set.compl (P.inside : Set (ℝ × ℝ)) from
            fun _ hb hi => hi.1 hb) a := by
  let hsub : P.boundary ℝ ⊆ Set.compl (P.inside : Set (ℝ × ℝ)) := fun _ hb hi => hi.1 hb
  let i : P.boundary ℝ → Set.compl (P.inside : Set (ℝ × ℝ)) := Set.inclusion hsub
  have hiinj : Function.Injective i := by
    intro a b hab
    exact (Set.inclusion_injective hsub) hab
  have hlocal : ∀ a : P.boundary ℝ,
      ∃ c : OpenPartialHomeomorph (P.boundary ℝ × Ico (0 : ℝ) 1)
          (Set.compl (P.inside : Set (ℝ × ℝ))),
        collarBase a ∈ c.source ∧ ∀ b, collarBase b ∈ c.source → c (collarBase b) = i b := by
    intro a
    obtain ⟨c, hc, hb⟩ := P.exists_exterior_local_collar hP hinj a
    exact ⟨c, hc, fun b hcb => Subtype.ext (hb b hcb)⟩
  obtain ⟨eb⟩ := P.nonempty_boundary_homeomorph_circle hP hinj
  let z : Circle := Classical.choice inferInstance
  letI : Nonempty (P.boundary ℝ) := ⟨eb.symm z⟩
  letI : CompactSpace (P.boundary ℝ) :=
    isCompact_iff_compactSpace.mp P.isCompact_boundary
  obtain ⟨U, hU, hUi, c, hc⟩ := BrownCollar.exists_full_collar_of_compact_local_patches
    i hiinj hlocal
  exact ⟨U, hU, hUi, c, hc⟩

end Polygon
