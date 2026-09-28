import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcStraightFan
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcSideClassification

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_three_arc_unpaired_side_classification
    {U V : Set AnnulusCoordinates} (R : M64IntrinsicCoordinateTriangulation (closure U))
    (gamma : Bool → ℝ → AnnulusCoordinates) (sigma : ℝ → AnnulusCoordinates)
    (T : Bool → ℝ) {S : ℝ} (hg : ∀ e, Continuous (gamma e)) (hs : Continuous sigma)
    (hab : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 (T true),
      gamma false x = gamma true y → x = T false ∧ y = 0)
    (has : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 S,
      gamma false x = sigma y → x = 0 ∧ y = 0)
    (hbs : ∀ x ∈ Icc 0 (T true), ∀ y ∈ Icc 0 S,
      gamma true x = sigma y → x = T true ∧ y = S)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfU : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
    (hfV : frontier V = frontier U)
    (v0 vj v1 : Euler.CoordinateVertex R.coordinates R.basis)
    (hv0 : v0.1 = gamma false 0) (hvj : vj.1 = gamma false (T false))
    (hv1 : v1.1 = gamma true (T true))
    (p : Fin R.count × Fin 3)
    (hp : ∀ q : Fin R.count × Fin 3,
      faceBoundaryIndex R.face q.1 q.2 = faceBoundaryIndex R.face p.1 p.2 → q = p) :
    ((R.face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆ gamma false '' Icc 0 (T false) ∨
      ((R.face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆ gamma true '' Icc 0 (T true) ∨
      ((R.face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆ sigma '' Icc 0 S := by
  have htrace : frontier (⋃ i, (R.face i).carrier) = frontier U := by
    rw [R.cover, (m64Intrinsic_jordan_interior_closure hU hV hUV hfV.symm).2]
  have himage : ((R.face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 ⊆
      gamma false '' Icc 0 (T false) ∪
        (gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S) := by
    rw [← union_assoc, ← hfU, ← htrace]
    exact m64Intrinsic_unpaired_side_subset_region_frontier R.face R.coordinates R.basis
      R.source R.boundary R.intersections p hp
  have hfirst : (gamma false '' Icc 0 (T false)) ∩
      (gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S) ⊆ {v0.1, vj.1} := by
    rintro z ⟨⟨x, hx, hxz⟩, hz⟩
    simp only [mem_insert_iff, mem_singleton_iff]
    rcases hz with ⟨y, hy, hyz⟩ | ⟨y, hy, hyz⟩
    · exact Or.inr (hxz.symm.trans ((congrArg (gamma false)
        (hab x hx y hy (hxz.trans hyz.symm)).1).trans hvj.symm))
    · exact Or.inl (hxz.symm.trans ((congrArg (gamma false)
        (has x hx y hy (hxz.trans hyz.symm)).1).trans hv0.symm))
  rcases m64Intrinsic_unpaired_side_subset_one_of_two_arcs R.face R.coordinates R.basis
      R.source R.carrier R.boundary R.intersections p hp
      (isCompact_Icc.image (hg false)).isClosed
      ((isCompact_Icc.image (hg true)).union (isCompact_Icc.image hs)).isClosed
      himage v0 vj hfirst with hleft | hright
  · exact Or.inl hleft
  · right
    apply m64Intrinsic_unpaired_side_subset_one_of_two_arcs R.face R.coordinates R.basis
      R.source R.carrier R.boundary R.intersections p hp
      (isCompact_Icc.image (hg true)).isClosed (isCompact_Icc.image hs).isClosed
      hright v1 v1
    rintro z ⟨⟨x, hx, hxz⟩, ⟨y, hy, hyz⟩⟩
    exact mem_insert_of_mem _ (mem_singleton_iff.mpr (hxz.symm.trans
      ((congrArg (gamma true) (hbs x hx y hy (hxz.trans hyz.symm)).1).trans hv1.symm)))

end PoincareConjecture
