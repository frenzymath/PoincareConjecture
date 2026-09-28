import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryFaceHeight
import PoincareConjecture.Proofs.M76.Wall.Mathlib.PiecewiseVertexSuperlevel











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : SimplicialComplex ℝ E} {f : E → ℝ}



theorem AffineOnFaces.half_le_binaryFaceCenter_iff (hf : K.AffineOnFaces f)
    {s : Finset E} (hs : s ∈ K.faces) (A : Set E)
    (hvalues : ∀ v ∈ s, (v ∈ A → f v = 1) ∧ (v ∉ A → f v = 0)) :
    (1 / 2 : ℝ) ≤ f (s.binaryFaceCenter A) ↔ ∃ v ∈ s, v ∈ A := by
  classical
  by_cases hpos : ∃ v ∈ s, v ∈ A
  · have hge : (1 / 2 : ℝ) ≤ f (s.binaryFaceCenter A) := by
      by_cases hneg : ∃ v ∈ s, v ∉ A
      · have hm : (s.filter (fun x => x ∈ A)).Nonempty ∧
            (s.filter (fun x => x ∉ A)).Nonempty := by
          constructor
          · obtain ⟨v, hv, hvA⟩ := hpos
            exact ⟨v, Finset.mem_filter.mpr ⟨hv, hvA⟩⟩
          · obtain ⟨v, hv, hvA⟩ := hneg
            exact ⟨v, Finset.mem_filter.mpr ⟨hv, hvA⟩⟩
        rw [hf.binaryFaceCenter_mixed hs A hm hvalues]
      · have hone : f (s.binaryFaceCenter A) = 1 :=
          hf.binaryFaceCenter_const hs A 1 (fun v hv =>
            (hvalues v hv).1 (by by_contra h; exact hneg ⟨v, hv, h⟩))
        rw [hone]
        norm_num
    exact ⟨fun _ => hpos, fun _ => hge⟩
  · have hzero : f (s.binaryFaceCenter A) = 0 :=
      hf.binaryFaceCenter_const hs A 0 (fun v hv =>
        (hvalues v hv).2 (fun h => hpos ⟨v, hv, h⟩))
    rw [hzero]
    constructor
    · intro h
      norm_num at h
    · intro h
      exact (hpos h).elim



theorem AffineOnFaces.binaryFaceCenter_le_half (hf : K.AffineOnFaces f)
    {s : Finset E} (hs : s ∈ K.faces) (A : Set E)
    (hvalues : ∀ v ∈ s, (v ∈ A → f v = 1) ∧ (v ∉ A → f v = 0))
    (hneg : ∃ v ∈ s, v ∉ A) : f (s.binaryFaceCenter A) ≤ (1 / 2 : ℝ) := by
  classical
  by_cases hpos : ∃ v ∈ s, v ∈ A
  · have hm : (s.filter (fun x => x ∈ A)).Nonempty ∧
        (s.filter (fun x => x ∉ A)).Nonempty := by
      constructor
      · obtain ⟨v, hv, hvA⟩ := hpos
        exact ⟨v, Finset.mem_filter.mpr ⟨hv, hvA⟩⟩
      · obtain ⟨v, hv, hvA⟩ := hneg
        exact ⟨v, Finset.mem_filter.mpr ⟨hv, hvA⟩⟩
    rw [hf.binaryFaceCenter_mixed hs A hm hvalues]
  · have hzero : f (s.binaryFaceCenter A) = 0 :=
      hf.binaryFaceCenter_const hs A 0 (fun v hv =>
        (hvalues v hv).2 (fun h => hpos ⟨v, hv, h⟩))
    rw [hzero]
    norm_num





theorem AffineOnFaces.binaryDerived_vertex_sides [Fintype K.faces]
    (hf : K.AffineOnFaces f) (A : Set E)
    (hvalues : ∀ v ∈ K.vertices, (v ∈ A → f v = 1) ∧ (v ∉ A → f v = 0)) :
    ∀ t ∈ (K.derivedSubdivision (fun s => s.val.binaryFaceCenter A)
      (K.positive_binary_face_centers A)).faces,
      (∀ v ∈ t, f v ≤ (1 / 2 : ℝ)) ∨ (∀ v ∈ t, (1 / 2 : ℝ) ≤ f v) := by
  classical
  have hface (s : K.faces) (v : E) (hv : v ∈ s.val) :
      (v ∈ A → f v = 1) ∧ (v ∉ A → f v = 0) :=
    hvalues v (K.down_closed s.property (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v))
  intro t ht
  obtain ⟨a, _, hchain, rfl⟩ := (K.derivedSubdivision_faces
    (fun s => s.val.binaryFaceCenter A) (K.positive_binary_face_centers A) t).mp ht
  by_cases hall : ∀ s ∈ a, ∃ v ∈ s.val, v ∈ A
  · right
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact (hf.half_le_binaryFaceCenter_iff s.property A (hface s)).mpr (hall s hs)
  · push Not at hall
    obtain ⟨u, hu, hnone⟩ := hall
    left
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    apply hf.binaryFaceCenter_le_half s.property A (hface s)
    rcases hchain s hs u hu with hsu | hus
    · obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces s.property
      exact ⟨v, hv, hnone v (hsu hv)⟩
    · obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces u.property
      exact ⟨v, hus hv, hnone v hv⟩




theorem AffineOnFaces.binaryDerived_superlevel_space [Fintype K.faces]
    (hf : K.AffineOnFaces f) (A : Set E)
    (hvalues : ∀ v ∈ K.vertices, (v ∈ A → f v = 1) ∧ (v ∉ A → f v = 0)) :
    ((K.derivedSubdivision (fun s => s.val.binaryFaceCenter A)
      (K.positive_binary_face_centers A)).vertexSubcomplex
        {x | (1 / 2 : ℝ) ≤ f x}).space = K.space ∩ {x | (1 / 2 : ℝ) ≤ f x} := by
  have hsub := K.derivedSubdivision_isSubdivision (fun s => s.val.binaryFaceCenter A)
    (K.positive_binary_face_centers A)
  rw [(hsub.affineOnFaces hf).vertexSuperlevel_space (1 / 2)
    (hf.binaryDerived_vertex_sides A hvalues)]
  rw [K.derivedSubdivision_space]

end Geometry.SimplicialComplex
