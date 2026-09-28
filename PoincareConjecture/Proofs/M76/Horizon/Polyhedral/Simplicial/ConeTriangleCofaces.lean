import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.ConeTriangleFaces
import Mathlib.Data.Set.Card

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

theorem cone_radial_triangle_cofaces (K L : SimplicialComplex ℝ E) {c q : E}
    (hc : c ∉ K.vertices) (hq : q ∈ K.vertices)
    (hfaces : ∀ s, s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces))
    (hdim : ∀ s ∈ K.faces, s.card ≤ 2) :
    {t : Finset E | t ∈ L.faces ∧ t.card = 3 ∧ ({c, q} : Finset E) ⊆ t} =
      (fun e : Finset E => insert c e) '' {e | e ∈ K.faces ∧ e.card = 2 ∧ q ∈ e} := by
  have hqc : q ≠ c := fun h => hc (h ▸ hq)
  ext t
  constructor
  · rintro ⟨ht, htc, hsub⟩
    obtain ⟨e, he, hec, rfl⟩ := (K.cone_triangle_iff L hc hfaces hdim t).mp ⟨ht, htc⟩
    have hqe : q ∈ e := (Finset.mem_insert.mp (hsub (by simp))).resolve_left hqc
    exact ⟨e, ⟨he, hec, hqe⟩, rfl⟩
  · rintro ⟨e, ⟨he, hec, hqe⟩, rfl⟩
    have ht := (K.cone_triangle_iff L hc hfaces hdim (insert c e)).mpr ⟨e, he, hec, rfl⟩
    exact ⟨ht.1, ht.2, by simp [Finset.insert_subset_iff, hqe]⟩

theorem cone_vertex_triangle_cofaces (K L : SimplicialComplex ℝ E) {c q : E}
    (hc : c ∉ K.vertices) (hq : q ∈ K.vertices)
    (hfaces : ∀ s, s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces))
    (hdim : ∀ s ∈ K.faces, s.card ≤ 2) :
    {t : Finset E | t ∈ L.faces ∧ t.card = 3 ∧ q ∈ t} =
      (fun e : Finset E => insert c e) '' {e | e ∈ K.faces ∧ e.card = 2 ∧ q ∈ e} := by
  rw [← K.cone_radial_triangle_cofaces L hc hq hfaces hdim]
  ext t
  constructor
  · rintro ⟨ht, htc, hqt⟩
    obtain ⟨e, _, _, hte⟩ := (K.cone_triangle_iff L hc hfaces hdim t).mp ⟨ht, htc⟩
    exact ⟨ht, htc, by rw [hte] at hqt ⊢; simp [Finset.insert_subset_iff, hqt]⟩
  · rintro ⟨ht, htc, hsub⟩
    exact ⟨ht, htc, hsub (by simp)⟩

theorem ncard_cone_radial_triangle_cofaces (K L : SimplicialComplex ℝ E) {c q : E}
    (hc : c ∉ K.vertices) (hq : q ∈ K.vertices)
    (hfaces : ∀ s, s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces))
    (hdim : ∀ s ∈ K.faces, s.card ≤ 2) :
    {t : Finset E | t ∈ L.faces ∧ t.card = 3 ∧ ({c, q} : Finset E) ⊆ t}.ncard =
      {e : Finset E | e ∈ K.faces ∧ e.card = 2 ∧ q ∈ e}.ncard := by
  rw [K.cone_radial_triangle_cofaces L hc hq hfaces hdim]
  apply Set.InjOn.ncard_image
  intro e he f hf h
  have heq := congrArg (fun s : Finset E => s.erase c) h
  simpa only [Finset.erase_insert (K.apex_notMem_base_face hc he.1),
    Finset.erase_insert (K.apex_notMem_base_face hc hf.1)] using heq

theorem cone_boundary_triangle_cofaces (K L : SimplicialComplex ℝ E) {c : E}
    (hc : c ∉ K.vertices)
    (hfaces : ∀ s, s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces))
    (hdim : ∀ s ∈ K.faces, s.card ≤ 2) {e : Finset E}
    (he : e ∈ K.faces) (hec : e.card = 2) :
    {t : Finset E | t ∈ L.faces ∧ t.card = 3 ∧ e ⊆ t} = {insert c e} := by
  ext t
  constructor
  · rintro ⟨ht, htc, het⟩
    obtain ⟨f, hf, hfc, rfl⟩ := (K.cone_triangle_iff L hc hfaces hdim t).mp ⟨ht, htc⟩
    have hef : e ⊆ f := by
      intro x hx
      exact (Finset.mem_insert.mp (het hx)).resolve_left
        (fun h => K.apex_notMem_base_face hc he (h ▸ hx))
    have hef' : e = f := Finset.eq_of_subset_of_card_le hef (by omega)
    exact congrArg (insert c) hef'.symm
  · rintro rfl
    have ht := (K.cone_triangle_iff L hc hfaces hdim (insert c e)).mpr ⟨e, he, hec, rfl⟩
    exact ⟨ht.1, ht.2, Finset.subset_insert _ _⟩

theorem cone_vertex_triangle_cofaces_eq_pair (K L : SimplicialComplex ℝ E)
    {c q u v : E} (hc : c ∉ K.vertices) (hq : q ∈ K.vertices)
    (hfaces : ∀ s, s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces))
    (hdim : ∀ s ∈ K.faces, s.card ≤ 2)
    (hedges : {e : Finset E | e ∈ K.faces ∧ e.card = 2 ∧ q ∈ e} =
      {({q, u} : Finset E), {q, v}}) :
    {t : Finset E | t ∈ L.faces ∧ t.card = 3 ∧ q ∈ t} =
      {({q, c, u} : Finset E), {q, c, v}} := by
  rw [K.cone_vertex_triangle_cofaces L hc hq hfaces hdim, hedges]
  simp only [Set.image_pair, Finset.insert_comm c q]

theorem exists_cone_vertex_fan_of_two_boundary_edges (K L : SimplicialComplex ℝ E)
    {c q : E} (hc : c ∉ K.vertices) (hq : q ∈ K.vertices)
    (hfaces : ∀ s, s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces))
    (hdim : ∀ s ∈ K.faces, s.card ≤ 2)
    (hcount : {e : Finset E | e ∈ K.faces ∧ e.card = 2 ∧ q ∈ e}.ncard = 2) :
    ∃ u v : E, q ≠ u ∧ q ≠ v ∧ u ≠ v ∧
      {e : Finset E | e ∈ K.faces ∧ e.card = 2 ∧ q ∈ e} =
        {({q, u} : Finset E), {q, v}} ∧
      {t : Finset E | t ∈ L.faces ∧ t.card = 3 ∧ q ∈ t} =
        {({q, c, u} : Finset E), {q, c, v}} ∧
      {t : Finset E | t ∈ L.faces ∧ t.card = 3 ∧ ({c, q} : Finset E) ⊆ t}.ncard = 2 := by
  obtain ⟨e, f, hef, hset⟩ := Set.ncard_eq_two.mp hcount
  have he : e ∈ K.faces ∧ e.card = 2 ∧ q ∈ e := by
    change e ∈ {e : Finset E | e ∈ K.faces ∧ e.card = 2 ∧ q ∈ e}
    rw [hset]
    simp
  have hf : f ∈ K.faces ∧ f.card = 2 ∧ q ∈ f := by
    change f ∈ {e : Finset E | e ∈ K.faces ∧ e.card = 2 ∧ q ∈ e}
    rw [hset]
    simp
  have hpair (s : Finset E) (hsc : s.card = 2) (hqs : q ∈ s) :
      ∃ u : E, q ≠ u ∧ s = {q, u} := by
    have hcard : (s.erase q).card = 1 := by rw [Finset.card_erase_of_mem hqs, hsc]
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard
    have hum : u ∈ s.erase q := by rw [hu]; simp
    refine ⟨u, (Finset.mem_erase.mp hum).1.symm, ?_⟩
    rw [← Finset.insert_erase hqs, hu]
  obtain ⟨u, hqu, rfl⟩ := hpair e he.2.1 he.2.2
  obtain ⟨v, hqv, rfl⟩ := hpair f hf.2.1 hf.2.2
  have huv : u ≠ v := fun h => hef (by rw [h])
  exact ⟨u, v, hqu, hqv, huv, hset,
    K.cone_vertex_triangle_cofaces_eq_pair L hc hq hfaces hdim hset,
    (K.ncard_cone_radial_triangle_cofaces L hc hq hfaces hdim).trans hcount⟩

end Geometry.SimplicialComplex
