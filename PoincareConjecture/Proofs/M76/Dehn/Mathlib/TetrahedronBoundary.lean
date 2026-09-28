import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TetrahedronIncidence

set_option autoImplicit false

open Set
open scoped BigOperators

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} [Fintype ι] (A : PreAbstractSimplicialComplex ι)

open Classical in

noncomputable def tetrahedronCofaces (t : Triangle A) : Finset (Tetrahedron A) :=
  Finset.univ.filter (fun q => t.val ⊆ q.val)

open Classical in

noncomputable def totalTetrahedronChain :
    Module.Dual (ZMod 2) (Tetrahedron A → ZMod 2) :=
  ∑ q : Tetrahedron A, LinearMap.proj q

open Classical in

noncomputable def markedTriangleChain (B : Triangle A → Prop) :
    Module.Dual (ZMod 2) (Triangle A → ZMod 2) :=
  ∑ t ∈ Finset.univ.filter B, LinearMap.proj t

open Classical in
theorem totalTetrahedronChain_apply (c : Tetrahedron A → ZMod 2) :
    totalTetrahedronChain A c = ∑ q : Tetrahedron A, c q := by
  simp [totalTetrahedronChain]

open Classical in
theorem markedTriangleChain_apply (B : Triangle A → Prop) (c : Triangle A → ZMod 2) :
    markedTriangleChain A B c = ∑ t ∈ Finset.univ.filter B, c t := by
  simp [markedTriangleChain]

open Classical in

theorem boundary3_total_apply (c : Triangle A → ZMod 2) :
    (triangleCoboundary A).dualMap (totalTetrahedronChain A) c =
      ∑ t : Triangle A, (tetrahedronCofaces A t).card • c t := by
  classical
  change totalTetrahedronChain A (triangleCoboundary A c) = _
  rw [totalTetrahedronChain_apply]
  simp_rw [triangleCoboundary_apply]
  calc
    (∑ q : Tetrahedron A, ∑ t ∈ tetrahedronTriangles A q, c t) =
        ∑ t : Triangle A, ∑ q ∈ tetrahedronCofaces A t, c t := by
      simp only [tetrahedronTriangles, tetrahedronCofaces, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = _ := by simp only [Finset.sum_const]

open Classical in

theorem boundary3_total_eq_marked (B : Triangle A → Prop)
    (hcofaces : ∀ t : Triangle A,
      (tetrahedronCofaces A t).card = if B t then 1 else 2) :
    (triangleCoboundary A).dualMap (totalTetrahedronChain A) = markedTriangleChain A B := by
  classical
  apply LinearMap.ext
  intro c
  rw [boundary3_total_apply, markedTriangleChain_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  rw [hcofaces t]
  by_cases ht : B t
  · simp only [if_pos ht, one_nsmul]
  · simp only [if_neg ht]
    exact CharTwo.two_nsmul (c t)

open Classical in

theorem boundary2_marked_eq_zero (B : Triangle A → Prop)
    (hcofaces : ∀ t : Triangle A,
      (tetrahedronCofaces A t).card = if B t then 1 else 2) :
    (edgeCoboundary A).dualMap (markedTriangleChain A B) = 0 := by
  rw [← boundary3_total_eq_marked A B hcofaces]
  exact boundary2_boundary3 A (totalTetrahedronChain A)

end PreAbstractSimplicialComplex.ModTwoCochains
