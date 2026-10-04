import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.DerivedSubdivision

/-!
# Coherent derived subdivisions of finite subcomplexes

Writing chains using their actual finite vertex sets makes the
derived construction compatible with subcomplex inclusion when
the centers are fixed face by face. See Hudson 1969, pp. 8--9
and M76 derivation 85.
-/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E) [Fintype K.faces]

/-- Derived faces can be indexed by chains of actual finite
vertex sets, with one center assignment shared between all
subcomplexes. See Hudson pp. 8--9 and M76 derivation 85. -/
theorem derivedSubdivision_faces_of_ambient_centers (c : Finset E → E)
    (hc : ∀ s ∈ K.faces, ∃ w : E → ℝ, (∀ v ∈ s, 0 < w v) ∧
      (∑ v ∈ s, w v) = 1 ∧ (∑ v ∈ s, w v • v) = c s) (t : Finset E) :
    t ∈ (K.derivedSubdivision (fun s => c s.val) (fun s => hc s.val s.property)).faces ↔
      ∃ a : Finset (Finset E), a.Nonempty ∧ (∀ s ∈ a, s ∈ K.faces) ∧
        (∀ s ∈ a, ∀ u ∈ a, s ⊆ u ∨ u ⊆ s) ∧ t = a.image c := by
  classical
  rw [K.derivedSubdivision_faces]
  constructor
  · rintro ⟨a, ha, hchain, rfl⟩
    refine ⟨a.image Subtype.val, ha.image _, ?_, ?_, ?_⟩
    · intro s hs
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
      exact i.property
    · intro s hs u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
      exact hchain i hi j hj
    · rw [Finset.image_image]
      rfl
  · rintro ⟨a, ha, hfaces, hchain, rfl⟩
    let v : a → K.faces := fun s => ⟨s.val, hfaces s.val s.property⟩
    refine ⟨a.attach.image v, ha.attach.image v, ?_, ?_⟩
    · intro i hi j hj
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hj
      exact hchain s.val s.property u.val u.property
    · rw [Finset.image_image]
      change a.image c = a.attach.image (c ∘ ((↑) : a → Finset E))
      rw [← Finset.image_image, Finset.attach_image_val]

omit [DecidableEq E] in
/-- Coherent positive centers make derived subdivision preserve
finite subcomplex inclusion. See Hudson pp. 8--9 and M76
derivation 85. -/
theorem derivedSubdivision_mono {L : SimplicialComplex ℝ E} [Fintype L.faces]
    (hKL : K ≤ L) (c : Finset E → E)
    (hc : ∀ s ∈ L.faces, ∃ w : E → ℝ, (∀ v ∈ s, 0 < w v) ∧
      (∑ v ∈ s, w v) = 1 ∧ (∑ v ∈ s, w v • v) = c s) :
    K.derivedSubdivision (fun s => c s.val) (fun s => hc s.val (hKL s.property)) ≤
      L.derivedSubdivision (fun s => c s.val) (fun s => hc s.val s.property) := by
  classical
  change K.faces ⊆ L.faces at hKL
  intro t ht
  change t ∈ (K.derivedSubdivision (fun s => c s.val)
    (fun s => hc s.val (hKL s.property))).faces at ht
  change t ∈ (L.derivedSubdivision (fun s => c s.val)
    (fun s => hc s.val s.property)).faces
  obtain ⟨a, ha, hfaces, hchain, rfl⟩ :=
    (K.derivedSubdivision_faces_of_ambient_centers c
      (fun s hs => hc s (hKL hs)) t).mp ht
  apply (L.derivedSubdivision_faces_of_ambient_centers c hc (a.image c)).mpr
  exact ⟨a, ha, fun s hs => hKL (hfaces s hs), hchain, rfl⟩

end Geometry.SimplicialComplex
