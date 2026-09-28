import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.TwoCapTriangulation









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]

private abbrev z (x : E) : E × ℝ := (x, 0)
private abbrev a (b : Bool) : E × ℝ := (0, capSign b)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E] in
private theorem zi : Function.Injective (z (E := E)) :=
  fun _ _ h ↦ congrArg Prod.fst h

omit [NormedSpace ℝ E] [DecidableEq E] in
private theorem az (b : Bool) (x : E) : a b ≠ z x := by
  intro h
  have hs := congrArg Prod.snd h
  cases b <;> norm_num [a, z, capSign] at hs

omit [NormedSpace ℝ E] in
private theorem anot (b : Bool) (s : Finset E) : a b ∉ s.image z := by
  simp only [Finset.mem_image]
  rintro ⟨x, _, hx⟩
  exact az b x hx.symm

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
private theorem zsubset_cone (s t : Finset E) (b : Bool) :
    s.image z ⊆ insert (a b) (t.image z) ↔ s ⊆ t := by
  constructor
  · intro h x hx
    have hx' := Finset.mem_insert.mp (h (Finset.mem_image_of_mem _ hx))
    rcases hx' with he | hx'
    · exact (az b x he.symm).elim
    · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx'
      exact zi hyx ▸ hy
  · intro h
    exact (Finset.image_subset_image h).trans (Finset.subset_insert _ _)

omit [NormedSpace ℝ E] [DecidableEq E] in
private theorem ai : Function.Injective (a (E := E)) := by
  intro b c h
  have hs := congrArg Prod.snd h
  cases b <;> cases c
  · rfl
  · norm_num [a, capSign] at hs
  · norm_num [a, capSign] at hs
  · rfl

omit [NormedSpace ℝ E] in
private theorem conei (b : Bool) :
    Function.Injective (fun s : Finset E ↦ insert (a b) (s.image z)) := by
  intro s t h
  apply zimagei
  have he := congrArg (fun u : Finset (E × ℝ) ↦ u.erase (a b)) h
  simpa only [Finset.erase_insert (anot b s), Finset.erase_insert (anot b t)] using he

variable (K : SimplicialComplex ℝ E) (L : Bool → SimplicialComplex ℝ E)
  (J : SimplicialComplex ℝ (E × ℝ))
  (hfaces : ∀ s, s ∈ J.faces ↔
    (∃ t ∈ K.faces, s = t.image z) ∨
    ∃ b : Bool, s = {a b} ∨ ∃ t ∈ (L b).faces, s = insert (a b) (t.image z))

include hfaces



theorem two_cap_triangle_iff (s : Finset (E × ℝ)) :
    (s ∈ J.faces ∧ s.card = 3) ↔
      (∃ t ∈ K.faces, t.card = 3 ∧ s = t.image z) ∨
      ∃ b : Bool, ∃ t ∈ (L b).faces, t.card = 2 ∧ s = insert (a b) (t.image z) := by
  constructor
  · rintro ⟨hs, hc⟩
    rcases (hfaces s).mp hs with ⟨t, ht, rfl⟩ | ⟨b, rfl | ⟨t, ht, rfl⟩⟩
    · exact Or.inl ⟨t, ht, (zcard t).symm.trans hc, rfl⟩
    · simp only [Finset.card_singleton] at hc
      omega
    · rw [Finset.card_insert_of_notMem (anot b t), zcard] at hc
      exact Or.inr ⟨b, t, ht, by omega, rfl⟩
  · rintro (⟨t, ht, hc, rfl⟩ | ⟨b, t, ht, hc, rfl⟩)
    · exact ⟨(hfaces _).mpr (Or.inl ⟨t, ht, rfl⟩), (zcard t).trans hc⟩
    · exact ⟨(hfaces _).mpr (Or.inr ⟨b, Or.inr ⟨t, ht, rfl⟩⟩), by
        rw [Finset.card_insert_of_notMem (anot b t), zcard, hc]⟩



theorem two_cap_pure
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hLpure : ∀ b s, s ∈ (L b).faces →
      ∃ t ∈ (L b).faces, t.card = 2 ∧ s ⊆ t)
    (hne : ∀ b, (L b).space.Nonempty) :
    ∀ s ∈ J.faces, ∃ t ∈ J.faces, t.card = 3 ∧ s ⊆ t := by
  intro s hs
  rcases (hfaces s).mp hs with ⟨u, hu, rfl⟩ | ⟨b, rfl | ⟨u, hu, rfl⟩⟩
  · obtain ⟨t, ht, hc, hut⟩ := hpure u hu
    exact ⟨t.image z, (hfaces _).mpr (Or.inl ⟨t, ht, rfl⟩),
      (zcard t).trans hc, Finset.image_subset_image hut⟩
  · obtain ⟨x, hx⟩ := hne b
    obtain ⟨u, hu, _⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨t, ht, hc, _⟩ := hLpure b u hu
    refine ⟨insert (a b) (t.image z),
      (hfaces _).mpr (Or.inr ⟨b, Or.inr ⟨t, ht, rfl⟩⟩), ?_, by simp⟩
    rw [Finset.card_insert_of_notMem (anot b t), zcard, hc]
  · obtain ⟨t, ht, hc, hut⟩ := hLpure b u hu
    refine ⟨insert (a b) (t.image z),
      (hfaces _).mpr (Or.inr ⟨b, Or.inr ⟨t, ht, rfl⟩⟩), ?_,
      Finset.insert_subset_insert _ (Finset.image_subset_image hut)⟩
    rw [Finset.card_insert_of_notMem (anot b t), zcard, hc]



theorem two_cap_base_edge_cofaces_iff (s : Finset E) (hsc : s.card = 2)
    (t : Finset (E × ℝ)) :
    (t ∈ J.faces ∧ t.card = 3 ∧ s.image z ⊆ t) ↔
      (∃ u ∈ K.faces, u.card = 3 ∧ s ⊆ u ∧ t = u.image z) ∨
      ∃ b : Bool, s ∈ (L b).faces ∧ t = insert (a b) (s.image z) := by
  constructor
  · rintro ⟨ht, htc, hst⟩
    rcases (two_cap_triangle_iff K L J hfaces t).mp ⟨ht, htc⟩ with
      ⟨u, hu, hc, rfl⟩ | ⟨b, u, hu, hc, rfl⟩
    · exact Or.inl ⟨u, hu, hc, (zsubset s u).mp hst, rfl⟩
    · have he : s = u := Finset.eq_of_subset_of_card_le
        ((zsubset_cone s u b).mp hst) (by omega)
      exact Or.inr ⟨b, he.symm ▸ hu, by rw [he]⟩
  · rintro (⟨u, hu, hc, hsu, rfl⟩ | ⟨b, hs, rfl⟩)
    · exact ⟨(hfaces _).mpr (Or.inl ⟨u, hu, rfl⟩), (zcard u).trans hc,
        Finset.image_subset_image hsu⟩
    · exact ⟨(hfaces _).mpr (Or.inr ⟨b, Or.inr ⟨s, hs, rfl⟩⟩), by
        rw [Finset.card_insert_of_notMem (anot b s), zcard, hsc],
        Finset.subset_insert _ _⟩


theorem two_cap_unmarked_edge_count (s : Finset E) (hsc : s.card = 2)
    (hmark : ∀ b, s ∉ (L b).faces) :
    {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ s.image z ⊆ t}.ncard =
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard := by
  have he : {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ s.image z ⊆ t} =
      (fun t : Finset E ↦ t.image z) ''
        {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t} := by
    ext t
    rw [mem_ofPred, two_cap_base_edge_cofaces_iff K L J hfaces s hsc t]
    constructor
    · rintro (⟨u, hu, hc, hsu, rfl⟩ | ⟨b, hb, _⟩)
      · exact ⟨u, ⟨hu, hc, hsu⟩, rfl⟩
      · exact (hmark b hb).elim
    · rintro ⟨u, ⟨hu, hc, hsu⟩, rfl⟩
      exact Or.inl ⟨u, hu, hc, hsu, rfl⟩
  rw [he, ncard_image_of_injective _ zimagei]


theorem two_cap_marked_edge_count (s : Finset E) (hsc : s.card = 2)
    (b : Bool) (hsb : s ∈ (L b).faces)
    (hdis : Disjoint (L false).space (L true).space)
    (hcount : {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 1) :
    {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ s.image z ⊆ t}.ncard = 2 := by
  have hlabel (c : Bool) (hc : s ∈ (L c).faces) : c = b := by
    obtain ⟨v, hv⟩ := (L b).nonempty_of_mem_faces hsb
    have hvb := (L b).subset_space hsb hv
    have hvc := (L c).subset_space hc hv
    cases b <;> cases c
    · rfl
    · exact (disjoint_left.mp hdis hvb hvc).elim
    · exact (disjoint_left.mp hdis hvc hvb).elim
    · rfl
  obtain ⟨u, hu⟩ := ncard_eq_one.mp hcount
  have huc : u ∈ K.faces ∧ u.card = 3 ∧ s ⊆ u := hu.symm.subset (mem_singleton u)
  apply ncard_eq_two.mpr
  refine ⟨u.image z, insert (a b) (s.image z), ?_, ?_⟩
  · intro he
    exact anot b u (he.symm ▸ Finset.mem_insert_self _ _)
  · ext t
    rw [mem_ofPred, two_cap_base_edge_cofaces_iff K L J hfaces s hsc t]
    constructor
    · rintro (⟨v, hv, hc, hsv, rfl⟩ | ⟨c, hc, rfl⟩)
      · left
        have he : v = u := hu.subset ⟨hv, hc, hsv⟩
        rw [he]
      · right
        rw [hlabel c hc]
        exact mem_singleton _
    · rintro (rfl | rfl)
      · exact Or.inl ⟨u, huc.1, huc.2.1, huc.2.2, rfl⟩
      · exact Or.inr ⟨b, hsb, rfl⟩



theorem two_cap_radial_edge_cofaces_iff (b : Bool) (v : E) (t : Finset (E × ℝ)) :
    (t ∈ J.faces ∧ t.card = 3 ∧ {a b, z v} ⊆ t) ↔
      ∃ u ∈ (L b).faces, u.card = 2 ∧ v ∈ u ∧ t = insert (a b) (u.image z) := by
  constructor
  · rintro ⟨ht, htc, hst⟩
    rcases (two_cap_triangle_iff K L J hfaces t).mp ⟨ht, htc⟩ with
      ⟨u, hu, hc, rfl⟩ | ⟨c, u, hu, hc, rfl⟩
    · exact (anot b u (hst (Finset.mem_insert_self _ _))).elim
    · have hbc : b = c := by
        rcases Finset.mem_insert.mp (hst (Finset.mem_insert_self _ _)) with h | h
        · exact ai h
        · exact (anot b u h).elim
      subst c
      have hvu : v ∈ u := by
        rcases Finset.mem_insert.mp (hst (show z v ∈ {a b, z v} by simp)) with h | h
        · exact (az b v h.symm).elim
        · obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp h
          exact zi hwv ▸ hw
      exact ⟨u, hu, hc, hvu, rfl⟩
  · rintro ⟨u, hu, hc, hv, rfl⟩
    refine ⟨(hfaces _).mpr (Or.inr ⟨b, Or.inr ⟨u, hu, rfl⟩⟩), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (anot b u), zcard, hc]
    · exact Finset.insert_subset_iff.mpr ⟨Finset.mem_insert_self _ _,
        Finset.singleton_subset_iff.mpr
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hv))⟩

theorem two_cap_radial_edge_count (b : Bool) (v : E) :
    {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ {a b, z v} ⊆ t}.ncard =
      {t : Finset E | t ∈ (L b).faces ∧ t.card = 2 ∧ v ∈ t}.ncard := by
  have he : {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ {a b, z v} ⊆ t} =
      (fun t : Finset E ↦ insert (a b) (t.image z)) ''
        {t : Finset E | t ∈ (L b).faces ∧ t.card = 2 ∧ v ∈ t} := by
    ext t
    rw [mem_ofPred, two_cap_radial_edge_cofaces_iff K L J hfaces b v t]
    exact ⟨fun ⟨u, hu, hc, hv, he⟩ ↦ ⟨u, ⟨hu, hc, hv⟩, he.symm⟩,
      fun ⟨u, ⟨hu, hc, hv⟩, he⟩ ↦ ⟨u, hu, hc, hv, he.symm⟩⟩
  rw [he, ncard_image_of_injective _ (conei b)]

open Classical in


theorem two_cap_two_triangle_cofaces
    (hdis : Disjoint (L false).space (L true).space)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if ∃ b, s ∈ (L b).faces then 1 else 2)
    (hrim : ∀ b v, v ∈ (L b).vertices →
      {t : Finset E | t ∈ (L b).faces ∧ t.card = 2 ∧ v ∈ t}.ncard = 2) :
    ∀ s ∈ J.faces, s.card = 2 →
      {t : Finset (E × ℝ) | t ∈ J.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2 := by
  classical
  intro s hs hsc
  rcases (hfaces s).mp hs with ⟨u, hu, rfl⟩ | ⟨b, rfl | ⟨u, hu, rfl⟩⟩
  · have huc : u.card = 2 := (zcard u).symm.trans hsc
    by_cases hm : ∃ b, u ∈ (L b).faces
    · obtain ⟨b, hb⟩ := hm
      apply two_cap_marked_edge_count K L J hfaces u huc b hb hdis
      simpa only [if_pos (show ∃ b, u ∈ (L b).faces from ⟨b, hb⟩)] using hboundary u hu huc
    · rw [two_cap_unmarked_edge_count K L J hfaces u huc (by simpa using hm)]
      simpa only [if_neg hm] using hboundary u hu huc
  · simp only [Finset.card_singleton] at hsc
    omega
  · have huc : u.card = 1 := by
      rw [Finset.card_insert_of_notMem (anot b u), zcard] at hsc
      omega
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp huc
    simp only [Finset.image_singleton]
    rw [two_cap_radial_edge_count K L J hfaces]
    exact hrim b v hu
end PoincareConjecture.M76.Dehn.Annuli
