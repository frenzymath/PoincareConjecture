import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.NestedSource









set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem disjoint_contractible_source_partition
    {S A₀ A₁ : Set P2} {L d : ℝ}
    (B₀ : OrientedPolygonCollar L d A₀) (B₁ : OrientedPolygonCollar L d A₁)
    (h₀ : closure B₀.outer.inside ⊆ S) (h₁ : closure B₁.outer.inside ⊆ S)
    (hdis : Disjoint (closure B₀.outer.inside) (closure B₁.outer.inside)) :
    let I₀ := closure B₀.inner.inside
    let I₁ := closure B₁.inner.inside
    let O := S \ (B₀.outer.inside ∪ B₁.outer.inside)
    ((I₀ ∪ A₀) ∪ (I₁ ∪ A₁)) ∪ O = S ∧
      I₀ ∩ A₀ = B₀.inner.boundary ℝ ∧ I₁ ∩ A₁ = B₁.inner.boundary ℝ ∧
      A₀ ∩ O = B₀.outer.boundary ℝ ∧ A₁ ∩ O = B₁.outer.boundary ℝ ∧
      Disjoint (I₀ ∪ A₀) (I₁ ∪ A₁) ∧ Disjoint (I₀ ∪ I₁) O ∧
      (A₀ ∪ A₁) ∩ I₀ = B₀.inner.boundary ℝ ∧
      (A₀ ∪ A₁) ∩ I₁ = B₁.inner.boundary ℝ ∧
      (A₀ ∪ A₁) ∩ O = B₀.outer.boundary ℝ ∪ B₁.outer.boundary ℝ := by
  dsimp only
  have hi₀ : closure B₀.inner.inside ⊆ closure B₀.outer.inside :=
    B₀.nested.trans subset_closure
  have hi₁ : closure B₁.inner.inside ⊆ closure B₁.outer.inside :=
    B₁.nested.trans subset_closure
  have ha₀ : A₀ ⊆ closure B₀.outer.inside := B₀.carrier.subset.trans sdiff_subset
  have ha₁ : A₁ ⊆ closure B₁.outer.inside := B₁.carrier.subset.trans sdiff_subset
  have hu₀ : closure B₀.inner.inside ∪ A₀ = closure B₀.outer.inside := by
    conv_lhs => rhs; rw [B₀.carrier]
    ext x
    constructor
    · rintro (hx | hx)
      exacts [hi₀ hx, hx.1]
    · intro hx
      by_cases hi : x ∈ B₀.inner.inside
      · exact Or.inl (subset_closure hi)
      · exact Or.inr ⟨hx, hi⟩
  have hu₁ : closure B₁.inner.inside ∪ A₁ = closure B₁.outer.inside := by
    conv_lhs => rhs; rw [B₁.carrier]
    ext x
    constructor
    · rintro (hx | hx)
      exacts [hi₁ hx, hx.1]
    · intro hx
      by_cases hi : x ∈ B₁.inner.inside
      · exact Or.inl (subset_closure hi)
      · exact Or.inr ⟨hx, hi⟩
  have hs₀ : closure B₀.inner.inside ∩ A₀ = B₀.inner.boundary ℝ := by
    conv_lhs => rhs; rw [B₀.carrier]
    rw [← B₀.inner.frontier_inside B₀.inner_simplicial B₀.inner_injective,
      frontier, (B₀.inner.isOpen_inside B₀.inner_simplicial B₀.inner_injective).interior_eq]
    ext x
    exact ⟨fun hx ↦ ⟨hx.1, hx.2.2⟩, fun hx ↦ ⟨hx.1, hi₀ hx.1, hx.2⟩⟩
  have hs₁ : closure B₁.inner.inside ∩ A₁ = B₁.inner.boundary ℝ := by
    conv_lhs => rhs; rw [B₁.carrier]
    rw [← B₁.inner.frontier_inside B₁.inner_simplicial B₁.inner_injective,
      frontier, (B₁.inner.isOpen_inside B₁.inner_simplicial B₁.inner_injective).interior_eq]
    ext x
    exact ⟨fun hx ↦ ⟨hx.1, hx.2.2⟩, fun hx ↦ ⟨hx.1, hi₁ hx.1, hx.2⟩⟩
  have ho₀ : A₀ ∩ (S \ (B₀.outer.inside ∪ B₁.outer.inside)) = B₀.outer.boundary ℝ := by
    rw [← B₀.outer.frontier_inside B₀.outer_simplicial B₀.outer_injective,
      frontier, (B₀.outer.isOpen_inside B₀.outer_simplicial B₀.outer_injective).interior_eq]
    ext x
    constructor
    · intro hx
      exact ⟨ha₀ hx.1, fun h ↦ hx.2.2 (Or.inl h)⟩
    · intro hx
      refine ⟨B₀.carrier.symm.subset ⟨hx.1, fun h ↦ hx.2 (B₀.nested (subset_closure h))⟩,
        h₀ hx.1, ?_⟩
      rintro (h | h)
      · exact hx.2 h
      · exact disjoint_left.mp hdis hx.1 (subset_closure h)
  have ho₁ : A₁ ∩ (S \ (B₀.outer.inside ∪ B₁.outer.inside)) = B₁.outer.boundary ℝ := by
    rw [← B₁.outer.frontier_inside B₁.outer_simplicial B₁.outer_injective,
      frontier, (B₁.outer.isOpen_inside B₁.outer_simplicial B₁.outer_injective).interior_eq]
    ext x
    constructor
    · intro hx
      exact ⟨ha₁ hx.1, fun h ↦ hx.2.2 (Or.inr h)⟩
    · intro hx
      refine ⟨B₁.carrier.symm.subset ⟨hx.1, fun h ↦ hx.2 (B₁.nested (subset_closure h))⟩,
        h₁ hx.1, ?_⟩
      rintro (h | h)
      · exact disjoint_left.mp hdis (subset_closure h) hx.1
      · exact hx.2 h
  refine ⟨?_, hs₀, hs₁, ho₀, ho₁, by rwa [hu₀, hu₁], ?_, ?_, ?_, ?_⟩
  · rw [hu₀, hu₁]
    apply Subset.antisymm (union_subset (union_subset h₀ h₁) sdiff_subset)
    intro x hx
    by_cases h : x ∈ B₀.outer.inside ∪ B₁.outer.inside
    · exact Or.inl (h.imp (fun h ↦ subset_closure h) (fun h ↦ subset_closure h))
    · exact Or.inr ⟨hx, h⟩
  · exact disjoint_left.mpr fun x hx hy ↦
      hy.2 (hx.elim (fun h ↦ Or.inl (B₀.nested h)) (fun h ↦ Or.inr (B₁.nested h)))
  · rw [union_inter_distrib_right, inter_comm A₀, hs₀,
      (hdis.symm.mono ha₁ hi₀).inter_eq, union_empty]
  · rw [union_inter_distrib_right, (hdis.mono ha₀ hi₁).inter_eq,
      empty_union, inter_comm, hs₁]
  · rw [union_inter_distrib_right, ho₀, ho₁]

theorem exists_disjoint_contractible_exterior
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {A₀ A₁ : Set P2} {L d : ℝ}
    (B₀ : OrientedPolygonCollar L d A₀) (B₁ : OrientedPolygonCollar L d A₁)
    (h₀ : closure B₀.outer.inside ⊆ interior J.space)
    (h₁ : closure B₁.outer.inside ⊆ interior J.space)
    (hdis : Disjoint (closure B₀.outer.inside) (closure B₁.outer.inside)) :
    ∃ O : SimplicialComplex ℝ P2, O.faces.Finite ∧
      O.space = J.space \ (B₀.outer.inside ∪ B₁.outer.inside) ∧
      frontier J.space ⊆ O.space := by
  have hp₀ := B₀.outer.isFinitePLBallPair_closed_inside B₀.outer_simplicial B₀.outer_injective
  have hp₁ := B₁.outer.isFinitePLBallPair_closed_inside B₁.outer_simplicial B₁.outer_injective
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨P₀, hP₀, hPs₀, _⟩, _⟩, _⟩ := hp₀
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨P₁, hP₁, hPs₁, _⟩, _⟩, _⟩ := hp₁
  obtain ⟨P, hP, hPs⟩ := P₀.exists_finite_triangulation_union P₁ hP₀ hP₁
  rw [hPs₀, hPs₁] at hPs
  obtain ⟨O, hO, hOs, _, _⟩ := exists_finite_interior_carrier_complement J P hJ hP
    (hPs.subset.trans (union_subset h₀ h₁))
  have hpint : interior P.space = B₀.outer.inside ∪ B₁.outer.inside := by
    rw [hPs, interior_union_of_disjoint_closure (by simpa only [closure_closure] using hdis),
      B₀.outer.interior_closure_inside B₀.outer_simplicial B₀.outer_injective,
      B₁.outer.interior_closure_inside B₁.outer_simplicial B₁.outer_injective]
  rw [hpint] at hOs
  refine ⟨O, hO, hOs, ?_⟩
  intro x hx
  rw [hOs]
  refine ⟨(J.isCompact_space_of_finite hJ).isClosed.frontier_subset hx, ?_⟩
  rintro (h | h)
  · exact hx.2 (h₀ (subset_closure h))
  · exact hx.2 (h₁ (subset_closure h))

end PoincareConjecture.M76.Dehn.Annuli
