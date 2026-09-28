import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Planar.PairedTriangleSigns
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineInjectivity










set_option autoImplicit false

open Set

namespace Geometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def transverseTriangleFunctional (b : Module.Basis (Fin 3) ℝ F)
    (v n : F) : F →ₗ[ℝ] ℝ :=
  b.det.toMultilinearMap.toLinearMap ![v, 0, n] 1

theorem transverseTriangleFunctional_apply (b : Module.Basis (Fin 3) ℝ F)
    (v n z : F) : transverseTriangleFunctional b v n z = b.det ![v, z, n] := by
  change b.det (Function.update ![v, 0, n] 1 z) = _
  congr 1
  funext i
  fin_cases i <;> simp

namespace SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem AffineOnFaces.strict_vertex_signs_of_centroid
    (K : SimplicialComplex ℝ E) (f : E → F) (hf : K.AffineOnFaces f)
    (t : Finset E) (ht : t ∈ K.faces) (a : E)
    (L : F →ₗ[ℝ] ℝ) (o : F)
    (hzero : ∀ x ∈ t, x ≠ a → L (f x - o) = 0) :
    (L (f (t.centroid ℝ id) - o) < 0 → L (f a - o) < 0) ∧
      (0 < L (f (t.centroid ℝ id) - o) → 0 < L (f a - o)) := by
  obtain ⟨A, hA⟩ := hf t ht
  let B : E →ᵃ[ℝ] ℝ := L.toAffineMap.comp A.toAffineMap - AffineMap.const ℝ E (L o)
  have hB (x : E) (hx : x ∈ convexHull ℝ (t : Set E)) : B x = L (f x - o) := by
    change L (A x) - L o = _
    rw [← hA hx, map_sub]
  have hcent : t.centroid ℝ id ∈ convexHull ℝ (t : Set E) :=
    t.centroid_mem_convexHull (K.nonempty_of_mem_faces ht)
  constructor
  · intro hneg
    by_contra hnot
    have hvertices : (t : Set E) ⊆ B ⁻¹' Ici 0 := by
      intro x hx
      rw [mem_preimage, mem_Ici, hB x (subset_convexHull ℝ _ hx)]
      by_cases he : x = a
      · exact he.symm ▸ le_of_not_gt hnot
      · exact (hzero x hx he).symm.le
    have hwhole := convexHull_min hvertices ((convex_Ici (0 : ℝ)).affine_preimage B)
    have hnonneg : 0 ≤ B (t.centroid ℝ id) := hwhole hcent
    rw [hB _ hcent] at hnonneg
    exact (not_lt_of_ge hnonneg) hneg
  · intro hpos
    by_contra hnot
    have hvertices : (t : Set E) ⊆ B ⁻¹' Iic 0 := by
      intro x hx
      rw [mem_preimage, mem_Iic, hB x (subset_convexHull ℝ _ hx)]
      by_cases he : x = a
      · exact he.symm ▸ le_of_not_gt hnot
      · exact (hzero x hx he).le
    have hwhole := convexHull_min hvertices ((convex_Iic (0 : ℝ)).affine_preimage B)
    have hnonpos : B (t.centroid ℝ id) ≤ 0 := hwhole hcent
    rw [hB _ hcent] at hnonpos
    exact (not_lt_of_ge hnonpos) hpos

theorem AffineOnFaces.opposite_centroid_determinants_in_zero_plane
    (K : SimplicialComplex ℝ E) (f : E → F)
    (hf : K.AffineOnFaces f) (hi : InjOn f K.space)
    (b : Module.Basis (Fin 3) ℝ F)
    (ell : F →ᴬ[ℝ] ℝ) (n : F) (hn : ell.contLinear n = 1)
    (hplane : ∀ x ∈ K.space, ell (f x) = 0)
    {s t u : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hsc : s.card = 2) (htc : t.card = 3) (huc : u.card = 3)
    (hst : s ⊆ t) (hsu : s ⊆ u) (htu : t ≠ u)
    (p : Fin 3 → E) (hp : AffineIndependent ℝ p)
    (hpt : ∀ i, p i ∈ t) (hsp : ∀ x ∈ s, x = p 0 ∨ x = p 1) :
    let D := fun x => b.det ![f (p 1) - f (p 0), f x - f (p 0), n]
    (D (t.centroid ℝ id) < 0 ∧ 0 < D (u.centroid ℝ id)) ∨
      (0 < D (t.centroid ℝ id) ∧ D (u.centroid ℝ id) < 0) := by
  have hhull : convexHull ℝ (range p) ⊆ convexHull ℝ (t : Set E) :=
    convexHull_mono (by rintro x ⟨i, rfl⟩; exact hpt i)
  obtain ⟨A, hA⟩ := hf t ht
  have hAi : InjOn A (convexHull ℝ (range p)) := by
    intro x hx y hy he
    exact hi (K.convexHull_subset_space ht (hhull hx))
      (K.convexHull_subset_space ht (hhull hy))
      ((hA (hhull hx)).trans (he.trans (hA (hhull hy)).symm))
  have hpA := A.toAffineMap.affineIndependent_comp_of_injOn_convexHull hp hAi
  have heq : A.toAffineMap ∘ p = f ∘ p := by
    funext i
    exact (hA (subset_convexHull ℝ _ (hpt i))).symm
  rw [heq] at hpA
  have hz (i : Fin 3) : ell ((f ∘ p) i) = 0 := hplane _ (K.subset_space ht (hpt i))
  have hdet := boundary_triangle_det_ne_zero b ell n hn (f ∘ p) hpA hz
  let L := transverseTriangleFunctional b (f (p 1) - f (p 0)) n
  have hL (z : F) : L z = b.det ![f (p 1) - f (p 0), z, n] :=
    transverseTriangleFunctional_apply _ _ _ _
  have hzero (x : E) (hx : x ∈ s) : L (f x - f (p 0)) = 0 := by
    rcases hsp x hx with rfl | rfl
    · simp only [sub_self, map_zero]
    · rw [hL]
      exact b.det.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  have hnonzero : L (f (p 2) - f (p 0)) ≠ 0 := by
    rw [hL]
    exact hdet
  have hdim : Module.finrank ℝ F = 3 := by simpa using Module.finrank_eq_card_basis b
  have hsign := hf.opposite_centroid_signs_in_zero_plane K f hi hdim ell n (f (p 0)) hn
    (hz 0) hplane hs ht hu hsc htc huc hst hsu htu L hzero (p 2)
    (K.subset_space ht (hpt 2)) hnonzero
  simpa only [hL] using hsign

open Classical in
theorem AffineOnFaces.exists_opposite_triangle_determinants
    (K : SimplicialComplex ℝ E) (f : E → F)
    (hf : K.AffineOnFaces f) (hi : InjOn f K.space)
    (b : Module.Basis (Fin 3) ℝ F)
    (ell : F →ᴬ[ℝ] ℝ) (n : F) (hn : ell.contLinear n = 1)
    (hplane : ∀ x ∈ K.space, ell (f x) = 0)
    {s t u : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hsc : s.card = 2) (htc : t.card = 3) (huc : u.card = 3)
    (hst : s ⊆ t) (hsu : s ⊆ u) (htu : t ≠ u)
    (p : Fin 3 → E) (hp : AffineIndependent ℝ p)
    (hpt : ∀ i, p i ∈ t) (hsp : ∀ x ∈ s, x = p 0 ∨ x = p 1) :
    ∃ q : E, q ∉ s ∧ u = insert q s ∧
      b.det ![f (p 1) - f (p 0), f (p 2) - f (p 0), n] *
        b.det ![f (p 1) - f (p 0), f q - f (p 0), n] < 0 := by
  classical
  obtain ⟨q, hqs, hqu⟩ := Finset.exists_eq_insert_iff.mpr ⟨hsu, by omega⟩
  have hpimage : Finset.univ.image p = t := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hpt i
    · rw [Finset.card_image_iff.mpr hp.injective.injOn, htc]
      decide
  let L := transverseTriangleFunctional b (f (p 1) - f (p 0)) n
  have hL (z : F) : L z = b.det ![f (p 1) - f (p 0), z, n] :=
    transverseTriangleFunctional_apply _ _ _ _
  have hz0 : L (f (p 0) - f (p 0)) = 0 := by rw [sub_self, map_zero]
  have hz1 : L (f (p 1) - f (p 0)) = 0 := by
    rw [hL]
    exact b.det.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  have hzeroT (x : E) (hx : x ∈ t) (hx2 : x ≠ p 2) : L (f x - f (p 0)) = 0 := by
    rw [← hpimage] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    fin_cases i
    · exact hz0
    · exact hz1
    · exact (hx2 rfl).elim
  have hzeroU (x : E) (hx : x ∈ u) (hxq : x ≠ q) : L (f x - f (p 0)) = 0 := by
    rw [← hqu] at hx
    rcases Finset.mem_insert.mp hx with he | hx
    · exact (hxq he).elim
    · rcases hsp x hx with rfl | rfl
      · exact hz0
      · exact hz1
  have hT := hf.strict_vertex_signs_of_centroid K f t ht (p 2) L (f (p 0)) hzeroT
  have hU := hf.strict_vertex_signs_of_centroid K f u hu q L (f (p 0)) hzeroU
  have hsign := hf.opposite_centroid_determinants_in_zero_plane K f hi b ell n hn hplane
    hs ht hu hsc htc huc hst hsu htu p hp hpt hsp
  simp only [hL] at hT hU
  refine ⟨q, hqs, hqu.symm, ?_⟩
  rcases hsign with ⟨hneg, hpos⟩ | ⟨hpos, hneg⟩
  · exact mul_neg_of_neg_of_pos (hT.1 hneg) (hU.2 hpos)
  · exact mul_neg_of_pos_of_neg (hT.2 hpos) (hU.1 hneg)

end SimplicialComplex

end Geometry
