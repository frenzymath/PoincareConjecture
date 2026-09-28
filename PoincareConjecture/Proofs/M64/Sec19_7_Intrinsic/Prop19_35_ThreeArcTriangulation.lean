import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCoordinateParents
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_MarkedRegionTriangulation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture.M64IntrinsicThreeArcCollar

theorem exists_triangulation
    {gamma : Bool → ℝ → AnnulusCoordinates} {sigma : ℝ → AnnulusCoordinates}
    {T b : Bool → ℝ} {S : ℝ} {U : Set AnnulusCoordinates}
    {C : M64IntrinsicThreeArcCaps gamma sigma T S U}
    (D : M64IntrinsicThreeArcCollar C b)
    (hU : IsOpen U) (hcompact : IsCompact (closure U))
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S) :
    ∃ R : M64IntrinsicCoordinateTriangulation (closure U),
      ∃ v0 vj v1 : Euler.CoordinateVertex R.coordinates R.basis,
        v0.1 = gamma false 0 ∧ vj.1 = gamma false (T false) ∧ v1.1 = gamma true (T true) := by
  classical
  obtain ⟨_, F, basis, hF, hFi, hsource, hparents, hcover⟩ :=
    D.exists_coordinate_parents hU hcompact hfront
  let marks : Finset AnnulusCoordinates :=
    {gamma false 0, gamma false (T false), gamma true (T true)}
  have hT (e : Bool) : 0 < T e := (D.joined.attachment e).1.trans (D.joined.attachment e).2
  have hmarks : (marks : Set AnnulusCoordinates) ⊆ closure U := by
    intro p hp
    apply frontier_subset_closure
    rw [hfront]
    simp only [marks, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact Or.inl (Or.inl ⟨0, ⟨le_rfl, (hT false).le⟩, rfl⟩)
    · exact Or.inl (Or.inl ⟨T false, ⟨(hT false).le, le_rfl⟩, rfl⟩)
    · exact Or.inl (Or.inr ⟨T true, ⟨(hT true).le, le_rfl⟩, rfl⟩)
  obtain ⟨R, hvertices⟩ := m64Intrinsic_exists_marked_region_triangulation
    F basis hF hFi hsource hparents hcover marks hmarks
  obtain ⟨v0, hv0⟩ := hvertices (gamma false 0) (by simp [marks])
  obtain ⟨vj, hvj⟩ := hvertices (gamma false (T false)) (by simp [marks])
  obtain ⟨v1, hv1⟩ := hvertices (gamma true (T true)) (by simp [marks])
  exact ⟨R, v0, vj, v1, hv0, hvj, hv1⟩

end PoincareConjecture.M64IntrinsicThreeArcCollar
