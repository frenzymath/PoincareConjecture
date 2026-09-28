import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GeometricGraphEdgeIntervals
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import PoincareConjecture.Proofs.M76.Mathlib.FiniteOrderedPartition

set_option autoImplicit false

open Set

namespace ContinuousAffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem injective_or_const_real (A : ℝ →ᴬ[ℝ] E) :
    Function.Injective A ∨ ∀ t : ℝ, A t = A 0 := by
  have hformula (t : ℝ) : A t = AffineMap.lineMap (A 0) (A 1) t := by
    simpa only [AffineMap.lineMap_apply_module, sub_zero, add_zero, smul_eq_mul,
      mul_one, mul_zero, zero_add]
      using A.apply_lineMap (0 : ℝ) 1 t
  by_cases h : A 0 = A 1
  · right
    intro t
    rw [hformula, ← h, AffineMap.lineMap_same_apply]
  · left
    intro t u htu
    apply AffineMap.lineMap_injective ℝ h
    rw [← hformula, ← hformula]
    exact htu

end ContinuousAffineMap

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E)

theorem exists_affine_graph_partition
    (hK : K.faces.Finite) (hdim : ∀ s ∈ K.faces, s.card ≤ 2)
    (A : ℝ →ᴬ[ℝ] E) (hinj : Function.Injective A)
    {l u : ℝ} (hlu : l < u) (hA : MapsTo A (Icc l u) K.space)
    (hl : A l ∈ K.vertices) (hu : A u ∈ K.vertices) :
    ∃ (n : ℕ) (t : Fin (n + 2) → ℝ), StrictMono t ∧ t 0 = l ∧
      t (Fin.last (n + 1)) = u ∧ (∀ i, A (t i) ∈ K.vertices) ∧
      ∀ i : Fin (n + 1), ({A (t i.castSucc), A (t i.succ)} : Finset E) ∈ K.faces := by
  classical
  have hfinite : (A ⁻¹' K.vertices ∩ Icc l u).Finite :=
    ((K.finite_vertices_of_finite_faces hK).preimage hinj.injOn).subset inter_subset_left
  let T := hfinite.toFinset
  have hT : (T : Set ℝ) ⊆ Icc l u := fun _ hx => (hfinite.mem_toFinset.mp hx).2
  have hlT : l ∈ T := hfinite.mem_toFinset.mpr ⟨hl, le_rfl, hlu.le⟩
  have huT : u ∈ T := hfinite.mem_toFinset.mpr ⟨hu, hlu.le, le_rfl⟩
  obtain ⟨n, t, ht, ht0, ht1, htrange, hgap⟩ := T.exists_ordered_partition hlu hT hlT huT
  have htmem (i : Fin (n + 2)) : t i ∈ T := htrange.subset (mem_range_self i)
  have hvertices (i : Fin (n + 2)) : A (t i) ∈ K.vertices :=
    (hfinite.mem_toFinset.mp (htmem i)).1
  refine ⟨n, t, ht, ht0, ht1, hvertices, fun i => ?_⟩
  have hlt : t i.castSucc < t i.succ := ht Fin.castSucc_lt_succ
  have hlocal : Icc (t i.castSucc) (t i.succ) ⊆ Icc l u := fun x hx =>
    ⟨(hT (htmem _)).1.trans hx.1, hx.2.trans (hT (htmem _)).2⟩
  have hclosed : A '' Icc (t i.castSucc) (t i.succ) =
      segment ℝ (A (t i.castSucc)) (A (t i.succ)) := by
    rw [← segment_eq_Icc hlt.le]
    exact image_segment ℝ A.toAffineMap _ _
  have hopen : A '' Ioo (t i.castSucc) (t i.succ) =
      openSegment ℝ (A (t i.castSucc)) (A (t i.succ)) := by
    rw [← openSegment_eq_Ioo hlt]
    exact image_openSegment ℝ A.toAffineMap _ _
  apply K.pair_mem_faces_of_segment_avoids_vertices hK hdim (hvertices _) (hvertices _)
  · rw [← hclosed]
    rintro _ ⟨x, hx, rfl⟩
    exact hA (hlocal hx)
  · apply disjoint_left.mpr
    intro x hx hxv
    obtain ⟨y, hy, rfl⟩ := hopen.symm ▸ hx
    exact disjoint_left.mp (hgap i) hy
      (hfinite.mem_toFinset.mpr ⟨hxv, hlocal ⟨hy.1.le, hy.2.le⟩⟩)

end Geometry.SimplicialComplex
