import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.Carriers.Sum
import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.Reindex

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open Topology

universe u

namespace PoincareConjecture

namespace SmoothDisjointUnionData

noncomputable def append {m n : ℕ}
    {pieces : Fin m → GeneralizedSliceCarrier.{u}}
    {pieces' : Fin n → GeneralizedSliceCarrier.{u}}
    {A B : GeneralizedSliceCarrier.{u}}
    (D : SmoothDisjointUnionData pieces A)
    (E : SmoothDisjointUnionData pieces' B)
    (hp : ∀ i, Nonempty (pieces i).carrier)
    (hq : ∀ i, Nonempty (pieces' i).carrier) :
    SmoothDisjointUnionData (Fin.append pieces pieces') (A.sum B) where
  region := Fin.append (fun i => Sum.inl '' D.region i) (fun i => Sum.inr '' E.region i)
  region_open := by
    intro i
    cases i using Fin.addCases with
    | left i =>
        simp only [Fin.append_left]
        exact isOpenMap_inl _ (D.region_open i)
    | right i =>
        simp only [Fin.append_right]
        exact isOpenMap_inr _ (E.region_open i)
  region_closed := by
    intro i
    cases i using Fin.addCases with
    | left i =>
        simp only [Fin.append_left]
        exact IsClosedEmbedding.inl.isClosed_iff_image_isClosed.mp (D.region_closed i)
    | right i =>
        simp only [Fin.append_right]
        exact IsClosedEmbedding.inr.isClosed_iff_image_isClosed.mp (E.region_closed i)
  identify := by
    intro i
    cases i using Fin.addCases with
    | left i =>
        rw [Fin.append_left pieces pieces' i]
        simp only [Fin.append_left]
        exact (D.identify i).sumInl B (Classical.choice (hp i))
    | right i =>
        rw [Fin.append_right pieces pieces' i]
        simp only [Fin.append_right]
        exact (E.identify i).sumInr A (Classical.choice (hq i))
  pairwise_disjoint := by
    intro i j hij
    cases i using Fin.addCases with
    | left i =>
        cases j using Fin.addCases with
        | left j =>
            simp only [Fin.append_left]
            exact Set.disjoint_image_of_injective Sum.inl_injective
              (D.pairwise_disjoint i j (fun h => hij (congrArg (Fin.castAdd n) h)))
        | right j =>
            simp only [Fin.append_left, Fin.append_right]
            exact Set.disjoint_left.mpr (by
              rintro _ ⟨x, _, rfl⟩ ⟨y, _, h⟩
              cases h)
    | right i =>
        cases j using Fin.addCases with
        | left j =>
            simp only [Fin.append_left, Fin.append_right]
            exact Set.disjoint_left.mpr (by
              rintro _ ⟨x, _, rfl⟩ ⟨y, _, h⟩
              cases h)
        | right j =>
            simp only [Fin.append_right]
            exact Set.disjoint_image_of_injective Sum.inr_injective
              (E.pairwise_disjoint i j (fun h => hij (congrArg (Fin.natAdd m) h)))
  cover := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    intro x _
    cases x with
    | inl x =>
        have hx : x ∈ ⋃ i, D.region i := by rw [D.cover]; exact Set.mem_univ x
        rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
        refine Set.mem_iUnion.mpr ⟨Fin.castAdd n i, ?_⟩
        simpa only [Fin.append_left] using Set.mem_image_of_mem Sum.inl hi
    | inr x =>
        have hx : x ∈ ⋃ i, E.region i := by rw [E.cover]; exact Set.mem_univ x
        rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
        refine Set.mem_iUnion.mpr ⟨Fin.natAdd m i, ?_⟩
        simpa only [Fin.append_right] using Set.mem_image_of_mem Sum.inr hi

noncomputable def sumRight {A B X : GeneralizedSliceCarrier.{u}}
    (D : SmoothDisjointUnionData ![A, B] X)
    (Z : GeneralizedSliceCarrier.{u}) (a : A.carrier) :
    SmoothDisjointUnionData ![A, B.sum Z] (X.sum Z) where
  region := ![Sum.inl '' D.region 0, (Sum.inl '' D.region 1) ∪ Set.range Sum.inr]
  region_open := by
    intro i
    fin_cases i
    · exact isOpenMap_inl _ (D.region_open 0)
    · exact (isOpenMap_inl _ (D.region_open 1)).union isOpen_range_inr
  region_closed := by
    intro i
    fin_cases i
    · exact IsClosedEmbedding.inl.isClosed_iff_image_isClosed.mp (D.region_closed 0)
    · exact (IsClosedEmbedding.inl.isClosed_iff_image_isClosed.mp
        (D.region_closed 1)).union isClosed_range_inr
  identify := by
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i
    · exact (D.identify 0).sumInl Z a
    · change SurgeryRegionEquivalence (B.sum Z) (X.sum Z) Set.univ
        ((Sum.inl '' D.region 1) ∪ Set.range Sum.inr)
      have E : SurgeryRegionEquivalence B X Set.univ (D.region 1) := D.identify 1
      have h := E.sumRight Z isOpen_univ (D.region_open 1)
      rw [Set.image_univ, Set.range_inl_union_range_inr] at h
      exact h
  pairwise_disjoint := by
    have hd : Disjoint (Sum.inl '' D.region 0 : Set (X.sum Z).carrier)
        ((Sum.inl '' D.region 1) ∪ Set.range Sum.inr) := by
      apply Set.disjoint_left.mpr
      rintro _ ⟨x, hx, rfl⟩ (hy | hy)
      · rcases hy with ⟨y, hy, heq⟩
        have heq' : y = x := Sum.inl_injective heq
        subst y
        exact Set.disjoint_left.mp (D.pairwise_disjoint 0 1 (by decide)) hx hy
      · rcases hy with ⟨y, heq⟩
        cases heq
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hij rfl).elim
  cover := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    intro x _
    cases x with
    | inl x =>
        have hx : x ∈ ⋃ i, D.region i := by rw [D.cover]; exact Set.mem_univ x
        rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
        fin_cases i
        · exact Set.mem_iUnion.mpr ⟨0, Set.mem_image_of_mem Sum.inl hi⟩
        · exact Set.mem_iUnion.mpr ⟨1, Or.inl (Set.mem_image_of_mem Sum.inl hi)⟩
    | inr x =>
        exact Set.mem_iUnion.mpr ⟨1, Or.inr ⟨x, rfl⟩⟩

end SmoothDisjointUnionData

end PoincareConjecture
