import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions
import PoincareConjecture.Proofs.M76.Mathlib.FinitePositiveHeightGap
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialStar
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarCarrierNeighborhood












set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem exists_ball_inter_space_subset_closedStar [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {q : E} (hq : q ∈ K.vertices) :
    ∃ η : ℝ, 0 < η ∧ K.space ∩ Metric.ball q η ⊆ (K.closedStar q).space := by
  let a : K.space := ⟨q, K.vertices_subset_space hq⟩
  have hstars : K.closedFaceStar {q} = K.closedStar q := by
    ext s
    change (s ∈ K.faces ∧ {q} ∪ s ∈ K.faces) ↔
      (s ∈ K.faces ∧ insert q s ∈ K.faces)
    rw [Finset.singleton_union]
  have hnh : (Subtype.val ⁻¹' (K.closedStar q).space : Set K.space) ∈ 𝓝 a := by
    rw [← hstars]
    apply K.closedFaceStar_mem_nhds_of_intrinsicInterior hK hq a
    simp [a, intrinsicInterior_singleton]
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hnh
  refine ⟨η, hη, fun x hx => ?_⟩
  exact hball (show (⟨x, hx.1⟩ : K.space) ∈ Metric.ball a η from hx.2)

variable [FiniteDimensional ℝ E]






theorem exists_local_minimum_union_triangulation [DecidableEq E]
    (Kd Ks : SimplicialComplex ℝ E) (hd : Kd.faces.Finite) (hs : Ks.faces.Finite)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqd : q ∈ Kd.space) (hqs : q ∉ Ks.space)
    (hmin : ∀ x ∈ Kd.space, A q ≤ A x)
    (hunique : ∀ x ∈ Kd.space, A x = A q → x = q)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = Kd.space ∪ Ks.space ∧
      q ∈ L.vertices ∧ (L.closedStar q).space ⊆ Kd.space ∧
      (∃ η : ℝ, 0 < η ∧ L.space ∩ Metric.ball q η ⊆ (L.closedStar q).space) ∧
      ∃ β : ℝ, β ∈ Ioo 0 δ ∧
        ∀ v ∈ (L.closedStar q).vertices, v ≠ q → β < A v - A q := by
  classical
  let C : Bool → SimplicialComplex ℝ E := fun i => if i then Kd else Ks
  have hC (i : Bool) : (C i).faces.Finite := by cases i <;> assumption
  obtain ⟨L, hL, hLs, hfaces⟩ := exists_finite_triangulation_iUnion C hC
  have hspace : L.space = Kd.space ∪ Ks.space := by
    rw [hLs]
    ext x
    simp only [mem_iUnion, Bool.exists_bool, C, Bool.false_eq_true, if_false,
      if_true, mem_union]
    exact or_comm
  have hfaceCap (s : Finset E) (hsL : s ∈ L.faces)
      (hqsHull : q ∈ convexHull ℝ (s : Set E)) : convexHull ℝ (s : Set E) ⊆ Kd.space := by
    obtain ⟨i, r, hr, hsr⟩ := hfaces s hsL
    cases i with
    | false => exact (hqs ((C false).convexHull_subset_space hr (hsr hqsHull))).elim
    | true => exact hsr.trans ((C true).convexHull_subset_space hr)
  have hqL : q ∈ L.vertices := by
    obtain ⟨s, hsL, hqsHull⟩ := mem_space_iff.mp (hspace.symm.subset (Or.inl hqd))
    have hscap := hfaceCap s hsL hqsHull
    have hqsFace : q ∈ s := by
      by_contra hnot
      have hstrict : (s : Set E) ⊆ {x | A q < A x} := by
        intro x hx
        have hxd : x ∈ Kd.space := hscap (subset_convexHull ℝ _ hx)
        exact lt_of_le_of_ne (hmin x hxd) (fun heq =>
          hnot ((hunique x hxd heq.symm) ▸ hx))
      have hqq : A q < A q :=
        convexHull_min hstrict ((convex_Ioi (A q)).affine_preimage A) hqsHull
      exact (lt_irrefl _ hqq).elim
    exact L.down_closed hsL (Finset.singleton_subset_iff.mpr hqsFace)
      (Finset.singleton_nonempty q)
  have hstarCap : (L.closedStar q).space ⊆ Kd.space := by
    intro x hx
    obtain ⟨s, hsL, hxs⟩ := mem_space_iff.mp hx
    have hqinsert : q ∈ convexHull ℝ ((insert q s : Finset E) : Set E) :=
      subset_convexHull ℝ _ (Finset.mem_insert_self q s)
    exact hfaceCap (insert q s) hsL.2 hqinsert
      (convexHull_mono (Finset.subset_insert q s) hxs)
  have hpositive (v : E) (hv : v ∈ (L.closedStar q).vertices) (hvq : v ≠ q) :
      0 < A v - A q := by
    have hvd := hstarCap ((L.closedStar q).vertices_subset_space hv)
    exact sub_pos.mpr (lt_of_le_of_ne (hmin v hvd)
      (fun heq => hvq (hunique v hvd heq.symm)))
  have hvertices :=
    (L.closedStar q).finite_vertices_of_finite_faces (finite_closedStar_faces hL q)
  obtain ⟨β, hβ, hgap⟩ := hvertices.exists_pos_lt_positive_values (fun x => A x - A q) hδ
  exact ⟨L, hL, hspace, hqL, hstarCap,
    L.exists_ball_inter_space_subset_closedStar hL hqL, β, hβ,
    fun v hv hvq => hgap v hv (hpositive v hv hvq)⟩

end Geometry.SimplicialComplex
