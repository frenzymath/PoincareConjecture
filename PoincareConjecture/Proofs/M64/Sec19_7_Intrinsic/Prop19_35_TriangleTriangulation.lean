import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleCoordinateParents
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleCollarConstruction
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_MarkedRegionTriangulation





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

namespace M64IntrinsicTriangleCollar





theorem exists_triangulation
    {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ} {U : Set AnnulusCoordinates}
    {C : M64IntrinsicTriangleCaps base alpha beta D A B U} (P : M64IntrinsicTriangleCollar C)
    (hU : IsOpen U) (hcompact : IsCompact (closure U))
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B)) :
    ∃ R : M64IntrinsicCoordinateTriangulation (closure U),
      ∃ v0 v1 vT : Euler.CoordinateVertex R.coordinates R.basis,
        v0.1 = base 0 ∧ v1.1 = base D ∧ vT.1 = alpha A := by
  classical
  obtain ⟨_, F, basis, hF, hFi, hsource, hparents, hcover⟩ :=
    P.exists_coordinate_parents hU hcompact hfront
  let marks : Finset AnnulusCoordinates := {base 0, base D, alpha A}
  have hD : 0 < D := (C.radius_pos 0).trans (C.radius_lt_left 0)
  have hA : 0 < A := (C.radius_pos 0).trans (C.radius_lt_right 0)
  have hmarks : (marks : Set AnnulusCoordinates) ⊆ closure U := by
    intro p hp
    apply frontier_subset_closure
    rw [hfront]
    simp only [marks, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact Or.inl ⟨0, ⟨le_rfl, hD.le⟩, rfl⟩
    · exact Or.inl ⟨D, ⟨hD.le, le_rfl⟩, rfl⟩
    · exact Or.inr (Or.inl ⟨A, ⟨hA.le, le_rfl⟩, rfl⟩)
  obtain ⟨R, hvertices⟩ := m64Intrinsic_exists_marked_region_triangulation
    F basis hF hFi hsource hparents hcover marks hmarks
  obtain ⟨v0, hv0⟩ := hvertices (base 0) (by simp [marks])
  obtain ⟨v1, hv1⟩ := hvertices (base D) (by simp [marks])
  obtain ⟨vT, hvT⟩ := hvertices (alpha A) (by simp [marks])
  exact ⟨R, v0, v1, vT, hv0, hv1, hvT⟩

end M64IntrinsicTriangleCollar







theorem m64Intrinsic_exists_triangle_region_triangulation
    {base alpha beta : ℝ → AnnulusCoordinates}
    (hc : ContDiff ℝ ∞ base) (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    {D A B : ℝ} (hD : 0 < D) (hA : 0 < A) (hB : 0 < B)
    (hci : InjOn base (Icc 0 D)) (hai : InjOn alpha (Icc 0 A))
    (hbi : InjOn beta (Icc 0 B))
    (hcreg : ∀ t ∈ Ioo 0 D, deriv base t ≠ 0)
    (hareg : ∀ t ∈ Ioo 0 A, deriv alpha t ≠ 0)
    (hbreg : ∀ t ∈ Ioo 0 B, deriv beta t ≠ 0)
    (hstartA : base 0 = alpha 0) (hstartB : base D = beta 0)
    (hmeet : alpha A = beta B)
    (hbaseA : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 A, base s = alpha t → s = 0 ∧ t = 0)
    (hbaseB : ∀ s ∈ Icc 0 D, ∀ t ∈ Icc 0 B, base s = beta t → s = D ∧ t = 0)
    (hsides : ∀ s ∈ Icc 0 A, ∀ t ∈ Icc 0 B, alpha s = beta t → s = A ∧ t = B)
    (hindA : LinearIndependent ℝ
      (![deriv base 0, deriv alpha 0] : Fin 2 → AnnulusCoordinates))
    (hindB : LinearIndependent ℝ
      (![-deriv base D, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    (hindT : LinearIndependent ℝ
      (![-deriv alpha A, -deriv beta B] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V)
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B))
    (hfV : frontier V = frontier U) (hcompact : IsCompact (closure U)) :
    ∃ R : M64IntrinsicCoordinateTriangulation (closure U),
      ∃ v0 v1 vT : Euler.CoordinateVertex R.coordinates R.basis,
        v0.1 = base 0 ∧ v1.1 = base D ∧ vT.1 = alpha A := by
  obtain ⟨C⟩ := m64Intrinsic_exists_triangle_corner_caps hc ha hb hD hA hB hci hai hbi
    hstartA hstartB hmeet hbaseA hbaseB hindA hindB hindT hU hV hUV hfront hfV
  obtain ⟨P⟩ := m64Intrinsic_exists_triangle_collar hc ha hb hci hai hbi hcreg hareg hbreg
    hbaseA hbaseB hsides hU hV hUV hfront hfV C
  exact P.exists_triangulation hU hcompact hfront

end PoincareConjecture
