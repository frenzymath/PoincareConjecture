import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TetrahedronBoundary

set_option autoImplicit false

open scoped BigOperators

namespace PreAbstractSimplicialComplex.ModTwoCochains

theorem dual_apply_eq_sum_coordinates {κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : Module.Dual (ZMod 2) (κ → ZMod 2)) (f : κ → ZMod 2) :
    c f = ∑ q : κ, f q * c (Pi.single q 1) := by
  calc
    c f = c (∑ q : κ, Pi.single q (f q)) :=
      congrArg c (Finset.univ_sum_single f).symm
    _ = ∑ q : κ, c (Pi.single q (f q)) := by rw [map_sum]
    _ = ∑ q : κ, f q * c (Pi.single q 1) := by
      apply Finset.sum_congr rfl
      intro q _
      have hsingle : Pi.single q (f q) = f q • Pi.single q (1 : ZMod 2) := by
        rw [← Pi.single_smul']
        simp only [smul_eq_mul, mul_one]
      rw [hsingle, map_smul, smul_eq_mul]

variable {ι : Type*} [Fintype ι] (A : PreAbstractSimplicialComplex ι)

open Classical in

theorem triangleCoboundary_single (t : Triangle A) (q : Tetrahedron A) :
    triangleCoboundary A (Pi.single t 1) q = if t.val ⊆ q.val then 1 else 0 := by
  rw [triangleCoboundary_apply, Finset.sum_pi_single']
  simp only [tetrahedronTriangles, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in

theorem boundary3_single_eq_sum_coordinates
    (c : Module.Dual (ZMod 2) (Tetrahedron A → ZMod 2)) (t : Triangle A) :
    (triangleCoboundary A).dualMap c (Pi.single t 1) =
      ∑ q ∈ tetrahedronCofaces A t, c (Pi.single q 1) := by
  classical
  change c (triangleCoboundary A (Pi.single t 1)) = _
  rw [dual_apply_eq_sum_coordinates]
  simp_rw [triangleCoboundary_single]
  rw [tetrahedronCofaces, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases htq : t.val ⊆ q.val <;> simp only [htq, ite_true, ite_false, one_mul, zero_mul]

open Classical in

theorem tetrahedronChain_eq_smul_total_of_coordinates
    (c : Module.Dual (ZMod 2) (Tetrahedron A → ZMod 2)) (r : ZMod 2)
    (h : ∀ q : Tetrahedron A, c (Pi.single q 1) = r) :
    c = r • totalTetrahedronChain A := by
  apply LinearMap.ext
  intro f
  change c f = r * totalTetrahedronChain A f
  rw [dual_apply_eq_sum_coordinates, totalTetrahedronChain_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [h q, mul_comm]

open Classical in

theorem markedTriangleChain_single (B : Triangle A → Prop) (t : Triangle A) :
    markedTriangleChain A B (Pi.single t 1) = if B t then 1 else 0 := by
  rw [markedTriangleChain_apply, Finset.sum_pi_single']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end PreAbstractSimplicialComplex.ModTwoCochains
