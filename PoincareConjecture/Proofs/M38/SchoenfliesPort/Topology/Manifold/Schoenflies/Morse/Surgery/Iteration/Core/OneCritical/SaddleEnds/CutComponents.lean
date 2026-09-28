import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.CutCircles
import Mathlib.Topology.Connected.Clopen

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.AnnularEndFamily

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : EuclideanSpace Real (Fin 2)) 1
private abbrev S2 := sphere (0 : E3) 1

private theorem range_eq_component_of_circle_family
    {ι : Type*} [Finite ι] (f : ι → S1 → S2) (hf : ∀ i, Continuous (f i))
    (hinj : Injective (fun z : ι × S1 => f z.1 z.2))
    {L : Set S2} (hcover : (⋃ i, range (f i)) = L)
    (i : ι) {p : S2} (hp : p ∈ range (f i)) :
    range (f i) = connectedComponentIn L p := by
  classical
  let R : Set S2 := ⋃ j : {j : ι // j ≠ i}, range (f j)
  have hR : IsClosed R :=
    isClosed_iUnion_of_finite (fun j => (isCompact_range (hf j)).isClosed)
  have hdisjoint : Disjoint (range (f i)) R := by
    apply disjoint_left.mpr
    rintro x ⟨q, hq⟩ hx
    obtain ⟨j, z, hz⟩ := by simpa only [R, mem_iUnion, mem_range] using hx
    exact j.property ((congrArg Prod.fst
      (hinj (a₁ := (i, q)) (a₂ := (j.1, z)) (hq.trans hz.symm))).symm)
  have hsub : range (f i) ⊆ L := fun x hx =>
    hcover.subset (mem_iUnion.mpr ⟨i, hx⟩)
  have hLR : L ⊆ range (f i) ∪ R := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover.superset hx)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  apply Subset.antisymm
  · exact (isPreconnected_range (hf i)).subset_connectedComponentIn hp hsub
  · have hparts := isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (x := p) (F := L))
      (range (f i)) R (isCompact_range (hf i)).isClosed hR
      ((connectedComponentIn_subset L p).trans hLR)
      (by rw [hdisjoint.inter_eq, inter_empty])
    rcases hparts with hleft | hright
    · exact hleft
    · exact False.elim (disjoint_left.mp hdisjoint hp
        (hright (mem_connectedComponentIn (hsub hp))))

variable {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}

theorem lowerCutCircle_range_eq_connectedComponentIn
    (A : AnnularEndFamily v g B C) (i : A.LowerCutIndex)
    {p : S2} (hp : p ∈ range (A.lowerCutCircle i)) :
    range (A.lowerCutCircle i) =
      connectedComponentIn {q | inner Real v (g q) = A.lowerCut} p :=
  range_eq_component_of_circle_family A.lowerCutCircle
    (fun j => (A.lowerCutCircle_geometry j).1.continuous)
    A.lowerCutCircle_joint_injective A.iUnion_range_lowerCutCircle i hp

theorem upperCutCircle_range_eq_connectedComponentIn
    (A : AnnularEndFamily v g B C) (i : A.UpperCutIndex)
    {p : S2} (hp : p ∈ range (A.upperCutCircle i)) :
    range (A.upperCutCircle i) =
      connectedComponentIn {q | inner Real v (g q) = A.upperCut} p :=
  range_eq_component_of_circle_family A.upperCutCircle
    (fun j => (A.upperCutCircle_geometry j).1.continuous)
    A.upperCutCircle_joint_injective A.iUnion_range_upperCutCircle i hp

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.AnnularEndFamily

end

end M38Schoenflies
