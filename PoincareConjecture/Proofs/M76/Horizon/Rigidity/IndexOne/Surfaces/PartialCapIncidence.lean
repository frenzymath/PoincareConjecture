import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.OneBoundaryIncidence

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

private abbrev z (x : E) : E × ℝ := (x, 0)
private abbrev a : E × ℝ := (0, 1)

variable (K L : SimplicialComplex ℝ E) (J : SimplicialComplex ℝ (E × ℝ))
  (hfaces : ∀ s, s ∈ J.faces ↔
    (∃ t ∈ K.faces, s = t.image z) ∨ s = {a} ∨
      ∃ t ∈ L.faces, s = insert a (t.image z))

include hfaces

theorem one_boundary_cap_base_cofaces_count_of_not_mem
    (s : Finset E) (hsc : s.card = 2) (hs : s ∉ L.faces) :
    {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ s.image z ⊆ t}.ncard =
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard := by
  have he : {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ s.image z ⊆ t} =
      (fun t : Finset E => t.image z) ''
        {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t} := by
    ext t
    rw [mem_ofPred, one_boundary_cap_base_cofaces_iff K L J hfaces s hsc t]
    constructor
    · intro h
      obtain ⟨u, hu, hc, hsu, he⟩ := h.resolve_right (fun h => hs h.1)
      exact ⟨u, ⟨hu, hc, hsu⟩, he.symm⟩
    · rintro ⟨u, ⟨hu, hc, hsu⟩, he⟩
      exact Or.inl ⟨u, hu, hc, hsu, he.symm⟩
  rw [he]
  apply ncard_image_of_injective
  intro s t h
  have hi : Function.Injective (z (E := E)) := fun _ _ h => congrArg Prod.fst h
  exact Finset.image_injective hi h

open Classical in

theorem one_boundary_cap_base_cofaces_count_two_rims
    (M : SimplicialComplex ℝ E) (hdis : Disjoint L.space M.space)
    (s : Finset E) (hsc : s.card = 2)
    (hcount : {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
      if s ∈ L.faces ∨ s ∈ M.faces then 1 else 2) :
    {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ s.image z ⊆ t}.ncard =
      if s ∈ M.faces then 1 else 2 := by
  by_cases hs : s ∈ L.faces
  · have hsm : s ∉ M.faces := by
      intro hm
      obtain ⟨x, hx⟩ := L.nonempty_of_mem_faces hs
      exact disjoint_left.mp hdis (L.subset_space hs hx) (M.subset_space hm hx)
    rw [if_neg hsm]
    apply one_boundary_cap_base_cofaces_count K L J hfaces s hsc
    simpa only [hs, true_or, if_true] using hcount
  · rw [one_boundary_cap_base_cofaces_count_of_not_mem K L J hfaces s hsc hs]
    simpa only [hs, false_or] using hcount

open Classical in

theorem one_boundary_cap_cofaces_le_two_of_two_rims
    (M : SimplicialComplex ℝ E) (hdis : Disjoint L.space M.space)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if s ∈ L.faces ∨ s ∈ M.faces then 1 else 2)
    (hrim : ∀ v ∈ L.vertices,
      {t : Finset E | t ∈ L.faces ∧ t.card = 2 ∧ v ∈ t}.ncard = 2) :
    ∀ s ∈ J.faces, s.card = 2 →
      {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard ≤ 2 := by
  intro s hs hsc
  have hzcard (u : Finset E) : (u.image z).card = u.card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ h => congrArg Prod.fst h)
  have hanot (u : Finset E) : a ∉ u.image z := by
    rintro h
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h
    exact zero_ne_one (congrArg Prod.snd hx)
  rcases (hfaces s).mp hs with ⟨u, hu, rfl⟩ | rfl | ⟨u, hu, rfl⟩
  · have huc : u.card = 2 := (hzcard u).symm.trans hsc
    rw [one_boundary_cap_base_cofaces_count_two_rims K L J hfaces M hdis u huc
      (hboundary u hu huc)]
    split_ifs <;> omega
  · simp only [Finset.card_singleton] at hsc
    omega
  · have huc : u.card = 1 := by
      rw [Finset.card_insert_of_notMem (hanot u), hzcard] at hsc
      omega
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp huc
    simp only [Finset.image_singleton]
    rw [one_boundary_cap_radial_cofaces_count K L J hfaces, hrim v hu]

end PoincareConjecture.M76.Dehn.Annuli
