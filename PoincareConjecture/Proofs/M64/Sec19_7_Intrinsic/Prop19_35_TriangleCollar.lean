import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TriangleCapAvoidance
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerArcCollar




noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture





structure M64IntrinsicTriangleCollar
    {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ} {U : Set AnnulusCoordinates}
    (C : M64IntrinsicTriangleCaps base alpha beta D A B U) where
  baseArc : M64IntrinsicCornerArcCollar C (fun e => if e then 1 else 0) base D
  firstSide : M64IntrinsicCornerArcCollar C (fun e => if e then 2 else 0) alpha A
  secondSide : M64IntrinsicCornerArcCollar C (fun e => if e then 2 else 1) beta B
  base_opposite : Disjoint baseArc.bands (C.carrier 2)
  first_opposite : Disjoint firstSide.bands (C.carrier 1)
  second_opposite : Disjoint secondSide.bands (C.carrier 0)
  base_first : Disjoint baseArc.bands firstSide.bands
  base_second : Disjoint baseArc.bands secondSide.bands
  first_second : Disjoint firstSide.bands secondSide.bands

namespace M64IntrinsicTriangleCollar

variable {base alpha beta : ℝ → AnnulusCoordinates} {D A B : ℝ} {U : Set AnnulusCoordinates}
  {C : M64IntrinsicTriangleCaps base alpha beta D A B U} (P : M64IntrinsicTriangleCollar C)




abbrev carrier : Set AnnulusCoordinates :=
  (⋃ j, C.carrier j) ∪ (P.baseArc.bands ∪ (P.firstSide.bands ∪ P.secondSide.bands))




theorem isClosed_carrier : IsClosed P.carrier :=
  (isClosed_iUnion_of_finite fun j => (C.compact j).isClosed).union
    (P.baseArc.bands_closed.union (P.firstSide.bands_closed.union P.secondSide.bands_closed))




theorem occupied : P.carrier ⊆ closure U :=
  union_subset (iUnion_subset C.occupied) (union_subset P.baseArc.bands_occupied
    (union_subset P.firstSide.bands_occupied P.secondSide.bands_occupied))




theorem boundary_covered
    (hfront : frontier U = base '' Icc 0 D ∪ (alpha '' Icc 0 A ∪ beta '' Icc 0 B)) :
    ∀ p ∈ frontier U, ∃ W : Set AnnulusCoordinates, IsOpen W ∧ p ∈ W ∧
      W ∩ closure U ⊆ P.carrier := by
  have hcap (j : Fin 3) : C.carrier j ⊆ P.carrier :=
    (subset_iUnion (fun k => C.carrier k) j).trans subset_union_left
  intro p hp
  rw [hfront] at hp
  rcases hp with ⟨t, ht, rfl⟩ | (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
  · obtain ⟨W, hW, hpW, hcov⟩ := P.baseArc.covered t ht
    exact ⟨W, hW, hpW, hcov.trans (union_subset (union_subset (hcap 0) (hcap 1))
      (subset_union_left.trans subset_union_right))⟩
  · obtain ⟨W, hW, hpW, hcov⟩ := P.firstSide.covered t ht
    exact ⟨W, hW, hpW, hcov.trans (union_subset (union_subset (hcap 0) (hcap 2))
      (subset_union_left.trans (subset_union_right.trans subset_union_right)))⟩
  · obtain ⟨W, hW, hpW, hcov⟩ := P.secondSide.covered t ht
    exact ⟨W, hW, hpW, hcov.trans (union_subset (union_subset (hcap 1) (hcap 2))
      (subset_union_right.trans (subset_union_right.trans subset_union_right)))⟩

end M64IntrinsicTriangleCollar

end PoincareConjecture
