import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.OneBoundaryTriangulation

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

private abbrev z (x : E) : E × ℝ := (x, 0)
private abbrev a : E × ℝ := (0, 1)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E] in
private theorem zi : Function.Injective (z (E := E)) := fun _ _ h ↦ congrArg Prod.fst h

omit [NormedSpace ℝ E] [DecidableEq E] in
private theorem az (x : E) : a ≠ z x := by
  intro h
  exact one_ne_zero (congrArg Prod.snd h)

omit [NormedSpace ℝ E] in
private theorem anot (s : Finset E) : a ∉ s.image z := by
  rintro h
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h
  exact az x hx.symm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem zcard (s : Finset E) : (s.image z).card = s.card :=
  Finset.card_image_iff.mpr zi.injOn

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem zsubset (s t : Finset E) : s.image z ⊆ t.image z ↔ s ⊆ t := by
  constructor
  · intro h x hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp (h (Finset.mem_image_of_mem _ hx))
    exact zi hyx ▸ hy
  · exact Finset.image_subset_image

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem zimagei : Function.Injective (fun s : Finset E ↦ s.image z) := by
  intro s t h
  exact Finset.Subset.antisymm ((zsubset s t).mp h.subset) ((zsubset t s).mp h.symm.subset)

omit [NormedSpace ℝ E] in
private theorem zsubset_cone (s t : Finset E) :
    s.image z ⊆ insert a (t.image z) ↔ s ⊆ t := by
  constructor
  · intro h x hx
    rcases Finset.mem_insert.mp (h (Finset.mem_image_of_mem _ hx)) with he | hx'
    · exact (az x he.symm).elim
    · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx'
      exact zi hyx ▸ hy
  · intro h
    exact (Finset.image_subset_image h).trans (Finset.subset_insert _ _)

omit [NormedSpace ℝ E] in
private theorem conei : Function.Injective (fun s : Finset E ↦ insert a (s.image z)) := by
  intro s t h
  apply zimagei
  have he := congrArg (fun u : Finset (E × ℝ) ↦ u.erase a) h
  simpa only [Finset.erase_insert (anot s), Finset.erase_insert (anot t)] using he

variable (K L : SimplicialComplex ℝ E) (J : SimplicialComplex ℝ (E × ℝ))
  (hfaces : ∀ s, s ∈ J.faces ↔
    (∃ t ∈ K.faces, s = t.image z) ∨ s = {a} ∨
      ∃ t ∈ L.faces, s = insert a (t.image z))

include hfaces

theorem one_boundary_cap_triangle_iff (s : Finset (E × ℝ)) :
    (s ∈ J.faces ∧ s.card = 3) ↔
      (∃ t ∈ K.faces, t.card = 3 ∧ s = t.image z) ∨
      ∃ t ∈ L.faces, t.card = 2 ∧ s = insert a (t.image z) := by
  constructor
  · rintro ⟨hs, hc⟩
    rcases (hfaces s).mp hs with ⟨t, ht, rfl⟩ | rfl | ⟨t, ht, rfl⟩
    · exact Or.inl ⟨t, ht, (zcard t).symm.trans hc, rfl⟩
    · simp only [Finset.card_singleton] at hc; omega
    · rw [Finset.card_insert_of_notMem (anot t), zcard] at hc
      exact Or.inr ⟨t, ht, by omega, rfl⟩
  · rintro (⟨t, ht, hc, rfl⟩ | ⟨t, ht, hc, rfl⟩)
    · exact ⟨(hfaces _).mpr (Or.inl ⟨t, ht, rfl⟩), (zcard t).trans hc⟩
    · exact ⟨(hfaces _).mpr (Or.inr (Or.inr ⟨t, ht, rfl⟩)), by
        rw [Finset.card_insert_of_notMem (anot t), zcard, hc]⟩

theorem one_boundary_cap_pure
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hLpure : ∀ s ∈ L.faces, ∃ t ∈ L.faces, t.card = 2 ∧ s ⊆ t)
    (hne : L.space.Nonempty) :
    ∀ s ∈ J.faces, ∃ t ∈ J.faces, t.card = 3 ∧ s ⊆ t := by
  intro s hs
  rcases (hfaces s).mp hs with ⟨u, hu, rfl⟩ | rfl | ⟨u, hu, rfl⟩
  · obtain ⟨t, ht, hc, hut⟩ := hpure u hu
    exact ⟨t.image z, (hfaces _).mpr (Or.inl ⟨t, ht, rfl⟩),
      (zcard t).trans hc, Finset.image_subset_image hut⟩
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨u, hu, _⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨t, ht, hc, _⟩ := hLpure u hu
    refine ⟨insert a (t.image z),
      (hfaces _).mpr (Or.inr (Or.inr ⟨t, ht, rfl⟩)), ?_, by simp⟩
    rw [Finset.card_insert_of_notMem (anot t), zcard, hc]
  · obtain ⟨t, ht, hc, hut⟩ := hLpure u hu
    refine ⟨insert a (t.image z),
      (hfaces _).mpr (Or.inr (Or.inr ⟨t, ht, rfl⟩)), ?_,
      Finset.insert_subset_insert _ (Finset.image_subset_image hut)⟩
    rw [Finset.card_insert_of_notMem (anot t), zcard, hc]

theorem one_boundary_cap_base_cofaces_iff (s : Finset E) (hsc : s.card = 2)
    (t : Finset (E × ℝ)) :
    (t ∈ J.faces ∧ t.card = 3 ∧ s.image z ⊆ t) ↔
      (∃ u ∈ K.faces, u.card = 3 ∧ s ⊆ u ∧ t = u.image z) ∨
      (s ∈ L.faces ∧ t = insert a (s.image z)) := by
  constructor
  · rintro ⟨ht, htc, hst⟩
    rcases (one_boundary_cap_triangle_iff K L J hfaces t).mp ⟨ht, htc⟩ with
      ⟨u, hu, hc, rfl⟩ | ⟨u, hu, hc, rfl⟩
    · exact Or.inl ⟨u, hu, hc, (zsubset s u).mp hst, rfl⟩
    · have he : s = u := Finset.eq_of_subset_of_card_le
        ((zsubset_cone s u).mp hst) (by omega)
      exact Or.inr ⟨he.symm ▸ hu, by rw [he]⟩
  · rintro (⟨u, hu, hc, hsu, rfl⟩ | ⟨hs, rfl⟩)
    · exact ⟨(hfaces _).mpr (Or.inl ⟨u, hu, rfl⟩), (zcard u).trans hc,
        Finset.image_subset_image hsu⟩
    · exact ⟨(hfaces _).mpr (Or.inr (Or.inr ⟨s, hs, rfl⟩)), by
        rw [Finset.card_insert_of_notMem (anot s), zcard, hsc], Finset.subset_insert _ _⟩

open Classical in
theorem one_boundary_cap_base_cofaces_count (s : Finset E) (hsc : s.card = 2)
    (hcount : {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
      if s ∈ L.faces then 1 else 2) :
    {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ s.image z ⊆ t}.ncard = 2 := by
  by_cases hs : s ∈ L.faces
  · rw [if_pos hs] at hcount
    obtain ⟨u, hu⟩ := ncard_eq_one.mp hcount
    have huc : u ∈ K.faces ∧ u.card = 3 ∧ s ⊆ u := hu.symm.subset (mem_singleton u)
    apply ncard_eq_two.mpr
    refine ⟨u.image z, insert a (s.image z), ?_, ?_⟩
    · intro he
      exact anot u (he.symm ▸ Finset.mem_insert_self _ _)
    · ext t
      rw [mem_ofPred, one_boundary_cap_base_cofaces_iff K L J hfaces s hsc t]
      constructor
      · rintro (⟨v, hv, hc, hsv, rfl⟩ | ⟨_, rfl⟩)
        · left
          have he : v = u := hu.subset ⟨hv, hc, hsv⟩
          rw [he]
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact Or.inl ⟨u, huc.1, huc.2.1, huc.2.2, rfl⟩
        · exact Or.inr ⟨hs, rfl⟩
  · have he : {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ s.image z ⊆ t} =
        (fun t : Finset E ↦ t.image z) ''
          {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t} := by
      ext t
      rw [mem_ofPred, one_boundary_cap_base_cofaces_iff K L J hfaces s hsc t]
      exact ⟨fun h ↦ by
        obtain ⟨u, hu, hc, hsu, he⟩ := h.resolve_right (fun h ↦ hs h.1)
        exact ⟨u, ⟨hu, hc, hsu⟩, he.symm⟩,
        fun ⟨u, ⟨hu, hc, hsu⟩, he⟩ ↦ Or.inl ⟨u, hu, hc, hsu, he.symm⟩⟩
    rw [he, ncard_image_of_injective _ zimagei, hcount, if_neg hs]

theorem one_boundary_cap_radial_cofaces_iff (v : E) (t : Finset (E × ℝ)) :
    (t ∈ J.faces ∧ t.card = 3 ∧ {a, z v} ⊆ t) ↔
      ∃ u ∈ L.faces, u.card = 2 ∧ v ∈ u ∧ t = insert a (u.image z) := by
  constructor
  · rintro ⟨ht, htc, hst⟩
    rcases (one_boundary_cap_triangle_iff K L J hfaces t).mp ⟨ht, htc⟩ with
      ⟨u, hu, hc, rfl⟩ | ⟨u, hu, hc, rfl⟩
    · exact (anot u (hst (Finset.mem_insert_self _ _))).elim
    · have hvu : v ∈ u := by
        rcases Finset.mem_insert.mp (hst (show z v ∈ {a, z v} by simp)) with h | h
        · exact (az v h.symm).elim
        · obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp h
          exact zi hwv ▸ hw
      exact ⟨u, hu, hc, hvu, rfl⟩
  · rintro ⟨u, hu, hc, hv, rfl⟩
    refine ⟨(hfaces _).mpr (Or.inr (Or.inr ⟨u, hu, rfl⟩)), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (anot u), zcard, hc]
    · exact Finset.insert_subset_iff.mpr ⟨Finset.mem_insert_self _ _,
        Finset.singleton_subset_iff.mpr
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hv))⟩

theorem one_boundary_cap_radial_cofaces_count (v : E) :
    {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ {a, z v} ⊆ t}.ncard =
      {t : Finset E | t ∈ L.faces ∧ t.card = 2 ∧ v ∈ t}.ncard := by
  have he : {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ {a, z v} ⊆ t} =
      (fun t : Finset E ↦ insert a (t.image z)) ''
        {t : Finset E | t ∈ L.faces ∧ t.card = 2 ∧ v ∈ t} := by
    ext t
    rw [mem_ofPred, one_boundary_cap_radial_cofaces_iff K L J hfaces v t]
    exact ⟨fun ⟨u, hu, hc, hv, he⟩ ↦ ⟨u, ⟨hu, hc, hv⟩, he.symm⟩,
      fun ⟨u, ⟨hu, hc, hv⟩, he⟩ ↦ ⟨u, hu, hc, hv, he.symm⟩⟩
  rw [he, ncard_image_of_injective _ conei]

open Classical in
theorem one_boundary_cap_two_cofaces
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if s ∈ L.faces then 1 else 2)
    (hrim : ∀ v ∈ L.vertices,
      {t : Finset E | t ∈ L.faces ∧ t.card = 2 ∧ v ∈ t}.ncard = 2) :
    ∀ s ∈ J.faces, s.card = 2 →
      {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2 := by
  intro s hs hsc
  rcases (hfaces s).mp hs with ⟨u, hu, rfl⟩ | rfl | ⟨u, hu, rfl⟩
  · have huc : u.card = 2 := (zcard u).symm.trans hsc
    exact one_boundary_cap_base_cofaces_count K L J hfaces u huc (hboundary u hu huc)
  · simp only [Finset.card_singleton] at hsc; omega
  · have huc : u.card = 1 := by
      rw [Finset.card_insert_of_notMem (anot u), zcard] at hsc; omega
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp huc
    simp only [Finset.image_singleton]
    rw [one_boundary_cap_radial_cofaces_count K L J hfaces]
    exact hrim v hu

end PoincareConjecture.M76.Dehn.Annuli
