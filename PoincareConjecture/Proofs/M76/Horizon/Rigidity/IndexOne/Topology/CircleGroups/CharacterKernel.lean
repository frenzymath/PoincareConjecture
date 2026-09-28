import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.CocycleCharacters
import PoincareConjecture.Proofs.M76.Mathlib.ConvexSubtypePaths

set_option autoImplicit false

open Set StdSimplexCore

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

variable {ι : Type*} [Fintype ι] {A : PreAbstractSimplicialComplex ι}

theorem quotientValue_symm (c : A.ModTwoEdgeCocycle)
    {x y : A.barycentricSpace} (p : Path.Homotopic.Quotient x y) :
    c.quotientValue p.symm = -c.quotientValue p := by
  have h := c.quotientValue_trans p p.symm
  rw [Path.Homotopic.Quotient.trans_symm, c.quotientValue_refl] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem pathValue_eq_of_loopCharacter_eq_one (c : A.ModTwoEdgeCocycle)
    (x : A.barycentricSpace) (hzero : ∀ g, c.loopCharacter x g = 1)
    {y : A.barycentricSpace} (p q : Path x y) : c.pathValue p = c.pathValue q := by
  have h := congrArg Multiplicative.toAdd
    (hzero ((Path.Homotopic.Quotient.mk p).trans (Path.Homotopic.Quotient.mk q).symm))
  change c.quotientValue
    ((Path.Homotopic.Quotient.mk p).trans (Path.Homotopic.Quotient.mk q).symm) = 0 at h
  rw [c.quotientValue_trans, c.quotientValue_symm] at h
  simp only [quotientValue_mk, ← sub_eq_add_neg] at h
  exact sub_eq_zero.mp h

theorem isCoboundary_of_loopCharacter_eq_one
    [PathConnectedSpace A.barycentricSpace] (c : A.ModTwoEdgeCocycle)
    (hvertex : ∀ i : ι, {i} ∈ A.faces) (x : A.barycentricSpace)
    (hzero : ∀ g, c.loopCharacter x g = 1) : c.IsCoboundary := by
  classical
  let q (i : ι) := A.barycentricVertex i (hvertex i)
  let P (i : ι) : Path x (q i) := PathConnectedSpace.somePath x (q i)
  refine ⟨fun i => c.pathValue (P i) + c.value i (c.bundle.indexAt (q i)), ?_⟩
  intro s hs i hi j hj
  have hqi : (q i).val ∈ barycentricFace s := single_mem_barycentricFace hi
  have hqj : (q j).val ∈ barycentricFace s := single_mem_barycentricFace hj
  have hseg := ((convex_barycentricFace s).segment_subset hqi hqj).trans
    (A.barycentricFace_subset_barycentricSpace hs)
  let e : Path (q i) (q j) := Path.segmentIn _ _ _ hseg
  have he : ∀ t, (e t).val ∈ barycentricFace s :=
    Path.segmentIn_mem_convex (convex_barycentricFace s) _ _ _ hqi hqj
  obtain ⟨L, hL⟩ := c.exists_closedFace_lift hs hi hj 0 e he
  have hval := c.pathValue_of_lift e L hL
  change c.pathValue e = (0 + c.value i j + c.value j (c.bundle.indexAt (q j))) -
    (0 + c.value i (c.bundle.indexAt (q i))) at hval
  have hpaths := c.pathValue_eq_of_loopCharacter_eq_one x hzero ((P i).trans e) (P j)
  rw [c.pathValue_trans, hval] at hpaths
  simp only [zero_add, sub_eq_add_neg, CharTwo.neg_eq] at hpaths
  linear_combination (norm := ring_nf) hpaths
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, neg_zero, sub_zero]

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle
