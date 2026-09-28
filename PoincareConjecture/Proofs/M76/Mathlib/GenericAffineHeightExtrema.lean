import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import Mathlib.Data.Set.Finite.Lemmas










set_option autoImplicit false

open Set

namespace Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]





theorem eq_vertex_of_generic_affine_minimum
    (s : Finset E) (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A (s : Set E))
    {p x : E} (hp : p ∈ s) (hmin : ∀ v ∈ s, A p ≤ A v)
    (hx : x ∈ convexHull ℝ (s : Set E)) (hxA : A x = A p) : x = p := by
  let B := A - AffineMap.const ℝ E (A p)
  have hB : ∀ v ∈ s, 0 ≤ B v := by
    intro v hv
    change 0 ≤ A v - A p
    exact sub_nonneg.mpr (hmin v hv)
  have hxB : B x = 0 := by
    change A x - A p = 0
    exact sub_eq_zero.mpr hxA
  have hz := s.mem_convexHull_zero_vertices B hB hx hxB
  have hsub : (s : Set E) ∩ {v | B v = 0} ⊆ {p} := by
    intro v hv
    exact hA hv.1 hp (sub_eq_zero.mp hv.2)
  simpa only [convexHull_singleton, mem_singleton_iff] using convexHull_mono hsub hz

end Finset

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]





theorem minimum_section_eq_singleton_of_generic_vertices
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices)
    {p : E} (hp : p ∈ K.vertices) (hmin : ∀ v ∈ K.vertices, A p ≤ A v) :
    (∀ x ∈ K.space, A p ≤ A x) ∧ K.space ∩ {x | A x = A p} = {p} := by
  have hbound : ∀ x ∈ K.space, A p ≤ A x := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    apply convexHull_min (s := (s : Set E)) _ ((convex_Ici (A p)).affine_preimage A) hxs
    exact fun v hv => hmin v (K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v))
  refine ⟨hbound, Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨K.vertices_subset_space hp, rfl⟩)⟩
  rintro x ⟨hx, hxA⟩
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  have hverts : (s : Set E) ⊆ K.vertices := fun v hv =>
    K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  let B := A - AffineMap.const ℝ E (A p)
  have hz := s.mem_convexHull_zero_vertices B
    (fun v hv => sub_nonneg.mpr (hmin v (hverts hv))) hxs (sub_eq_zero.mpr hxA)
  have hsub : (s : Set E) ∩ {v | B v = 0} ⊆ {p} := by
    intro v hv
    exact hA (hverts hv.1) hp (sub_eq_zero.mp hv.2)
  simpa only [convexHull_singleton] using convexHull_mono hsub hz



theorem maximum_section_eq_singleton_of_generic_vertices
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices)
    {p : E} (hp : p ∈ K.vertices) (hmax : ∀ v ∈ K.vertices, A v ≤ A p) :
    (∀ x ∈ K.space, A x ≤ A p) ∧ K.space ∩ {x | A x = A p} = {p} := by
  have hnegA : InjOn (-A) K.vertices := fun _ hx _ hy h => hA hx hy (neg_injective h)
  simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_le_neg_iff, neg_inj] using
    K.minimum_section_eq_singleton_of_generic_vertices (-A) hnegA hp
      (fun v hv => neg_le_neg (hmax v hv))





theorem exists_unique_extreme_sections_of_generic_vertices
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hne : K.space.Nontrivial)
    (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices) :
    ∃ p q : E, p ∈ K.vertices ∧ q ∈ K.vertices ∧ A p < A q ∧
      (∀ x ∈ K.space, A p ≤ A x ∧ A x ≤ A q) ∧
      K.space ∩ {x | A x = A p} = {p} ∧
      K.space ∩ {x | A x = A q} = {q} := by
  have hverts : K.vertices.Nonempty := by
    obtain ⟨x, hx⟩ := hne.nonempty
    obtain ⟨s, hs, _⟩ := mem_space_iff.mp hx
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    exact ⟨v, K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v)⟩
  have hfinite : K.vertices.Finite := hK.preimage Finset.singleton_injective.injOn
  obtain ⟨p, hp, hmin⟩ := Set.exists_min_image K.vertices A hfinite hverts
  obtain ⟨q, hq, hmax⟩ := Set.exists_max_image K.vertices A hfinite hverts
  obtain ⟨hlo, hminsec⟩ := K.minimum_section_eq_singleton_of_generic_vertices A hA hp hmin
  obtain ⟨hhi, hmaxsec⟩ := K.maximum_section_eq_singleton_of_generic_vertices A hA hq hmax
  have hpq : A p < A q := by
    apply lt_of_le_of_ne (hmin q hq)
    intro heq
    apply hne.not_subsingleton
    intro x hx y hy
    have hxsec : x = p := hminsec.subset
      ⟨hx, le_antisymm ((hhi x hx).trans_eq heq.symm) (hlo x hx)⟩
    have hysec : y = p := hminsec.subset
      ⟨hy, le_antisymm ((hhi y hy).trans_eq heq.symm) (hlo y hy)⟩
    exact hxsec.trans hysec.symm
  exact ⟨p, q, hp, hq, hpq, fun x hx => ⟨hlo x hx, hhi x hx⟩, hminsec, hmaxsec⟩

end Geometry.SimplicialComplex
