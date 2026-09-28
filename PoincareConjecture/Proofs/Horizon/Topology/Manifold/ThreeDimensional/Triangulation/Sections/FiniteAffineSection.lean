import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Polyhedral.FiniteConvexSeparation
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas










set_option autoImplicit false

open Set

universe u v

namespace Poincare.Topology

theorem affine_constraint_direction_surjective_of_small_faces_gap
    {E : Type u} [AddCommGroup E] [Module Real E]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace Real F]
    [FiniteDimensional Real F]
    (A : E →ᵃ[Real] F) (s : Finset E) (a : Real) (ha : 0 < a)
    (hgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real F →
      ∀ x ∈ convexHull Real (t : Set E), a ≤ ‖A x‖)
    (hzero : ∃ x ∈ convexHull Real (s : Set E), A x = 0) :
    Submodule.map A.linear (vectorSpan Real (s : Set E)) = ⊤ := by
  classical
  rw [A.map_vectorSpan]
  by_contra hproper
  have hdim := Submodule.finrank_lt hproper
  have hz : (0 : F) ∈ convexHull Real (A '' (s : Set E)) := by
    rw [← A.image_convexHull]
    exact hzero
  rw [convexHull_eq_union] at hz
  simp only [mem_iUnion, exists_prop] at hz
  obtain ⟨t, ht, hind, htzero⟩ := hz
  have hspan : vectorSpan Real (t : Set F) ≤ vectorSpan Real (A '' (s : Set E)) :=
    vectorSpan_mono Real ht
  have htcard : t.card ≤ Module.finrank Real F := by
    have hc : t.card ≤ Module.finrank Real (vectorSpan Real (t : Set F)) + 1 := by
      have hrange : Set.range (Subtype.val : t → F) = (t : Set F) := by
        ext q
        simp
      have h := hind.card_le_finrank_succ
      rw [hrange] at h
      simpa only [Fintype.card_coe] using h
    have hm := Submodule.finrank_mono hspan
    omega
  have hpre (q : t) : ∃ p ∈ s, A p = (q : F) := ht q.property
  choose p hps hpA using hpre
  let r : Finset E := Finset.univ.image p
  have hrs : r ⊆ s := by
    intro z hz
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz
    exact hps q
  have hrcard : r.card ≤ Module.finrank Real F := by
    calc
      r.card ≤ Fintype.card t := Finset.card_image_le
      _ = t.card := Fintype.card_coe _
      _ ≤ Module.finrank Real F := htcard
  have hArt : A '' (r : Set E) = (t : Set F) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hw
      rw [hpA q]
      exact q.property
    · intro hz
      exact ⟨p ⟨z, hz⟩, Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, rfl⟩,
        hpA ⟨z, hz⟩⟩
  have hzimage : (0 : F) ∈ A '' convexHull Real (r : Set E) := by
    rw [A.image_convexHull, hArt]
    exact htzero
  obtain ⟨z, hz, hz0⟩ := hzimage
  have h := hgap r hrs hrcard z hz
  rw [hz0, norm_zero] at h
  exact (not_le_of_gt ha) h

theorem exists_minimal_affine_section_inverse
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace Real F]
    [FiniteDimensional Real F]
    (A : E →ᵃ[Real] F) (s : Finset E) (a : Real) (ha : 0 < a)
    (hcard : s.card = Module.finrank Real F + 1)
    (hgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real F →
      ∀ x ∈ convexHull Real (t : Set E), a ≤ ‖A x‖)
    (hzero : ∃ x ∈ convexHull Real (s : Set E), A x = 0) :
    ∃ B : F ≃L[Real] (vectorSpan Real (s : Set E)),
      (∀ z : F, A.linear (B z) = z) ∧
      (∀ v : vectorSpan Real (s : Set E), B (A.linear v) = v) := by
  classical
  let V := vectorSpan Real (s : Set E)
  let L : V →ₗ[Real] F := A.linear.domRestrict V
  have hmap := affine_constraint_direction_surjective_of_small_faces_gap A s a ha hgap hzero
  have hsurj : Function.Surjective L := by
    apply LinearMap.range_eq_top.mp
    simpa only [L, LinearMap.range_domRestrict] using hmap
  have hbound : Module.finrank Real V ≤ Module.finrank Real F := by
    change Module.finrank Real (vectorSpan Real (s : Set E)) ≤ Module.finrank Real F
    have h := finrank_vectorSpan_image_finset_le Real (fun x : E => x) s hcard
    rw [Finset.image_id'] at h
    exact h
  have hdim : Module.finrank Real V = Module.finrank Real F :=
    Nat.le_antisymm hbound (LinearMap.finrank_le_finrank_of_surjective hsurj)
  have hinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  let e : V ≃L[Real] F := (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  exact ⟨e.symm, fun z => e.apply_symm_apply z, fun v => e.symm_apply_apply v⟩

theorem exists_minimal_affine_section_of_near_point
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F]
    (A : E →ᵃ[Real] F) (s : Finset E) (a : Real) (ha : 0 < a)
    (hcard : s.card = Module.finrank Real F + 1)
    (hgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real F →
      ∀ x ∈ convexHull Real (t : Set E), a ≤ ‖A x‖)
    (hnear : ∃ x ∈ convexHull Real (s : Set E), ‖A x‖ < a) :
    ∃ x ∈ convexHull Real (s : Set E), A x = 0 ∧
      ∃ B : F ≃L[Real] (vectorSpan Real (s : Set E)),
        (∀ z : F, A.linear (B z) = z) ∧
        (∀ v : vectorSpan Real (s : Set E), B (A.linear v) = v) := by
  obtain ⟨x, hx, hx0⟩ := exists_zero_of_small_affine_faces_gap A s a hgap hnear
  exact ⟨x, hx, hx0, exists_minimal_affine_section_inverse A s a ha hcard hgap ⟨x, hx, hx0⟩⟩

end Poincare.Topology
