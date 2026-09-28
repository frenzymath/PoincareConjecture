import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TetrahedronChainCoordinates









set_option autoImplicit false

open scoped BigOperators

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} [Fintype ι] (A : PreAbstractSimplicialComplex ι)

open Classical in


noncomputable def triangleCofaces (e : Edge A) : Finset (Triangle A) :=
  Finset.univ.filter (fun t => e.val ⊆ t.val)



noncomputable abbrev totalTriangleChain :
    Module.Dual (ZMod 2) (Triangle A → ZMod 2) :=
  markedTriangleChain A (fun _ => True)

open Classical in


noncomputable def markedEdgeChain (B : Edge A → Prop) :
    Module.Dual (ZMod 2) (Edge A → ZMod 2) :=
  ∑ e ∈ Finset.univ.filter B, LinearMap.proj e

open Classical in


theorem totalTriangleChain_apply (c : Triangle A → ZMod 2) :
    totalTriangleChain A c = ∑ t : Triangle A, c t := by
  simp [totalTriangleChain, markedTriangleChain_apply]

open Classical in


theorem markedEdgeChain_apply (B : Edge A → Prop) (c : Edge A → ZMod 2) :
    markedEdgeChain A B c = ∑ e ∈ Finset.univ.filter B, c e := by
  simp [markedEdgeChain]

open Classical in


theorem totalTriangleChain_single (t : Triangle A) :
    totalTriangleChain A (Pi.single t 1) = 1 := by
  rw [totalTriangleChain_apply]
  simp

open Classical in


theorem edgeCoboundary_single (e : Edge A) (t : Triangle A) :
    edgeCoboundary A (Pi.single e 1) t = if e.val ⊆ t.val then 1 else 0 := by
  rw [edgeCoboundary_apply, Finset.sum_pi_single']
  simp only [triangleEdges, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in


theorem boundary2_single_eq_sum_coordinates
    (c : Module.Dual (ZMod 2) (Triangle A → ZMod 2)) (e : Edge A) :
    (edgeCoboundary A).dualMap c (Pi.single e 1) =
      ∑ t ∈ triangleCofaces A e, c (Pi.single t 1) := by
  change c (edgeCoboundary A (Pi.single e 1)) = _
  rw [dual_apply_eq_sum_coordinates]
  simp_rw [edgeCoboundary_single]
  rw [triangleCofaces, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases het : e.val ⊆ t.val <;> simp only [het, ite_true, ite_false, one_mul, zero_mul]

open Classical in


theorem triangleChain_eq_smul_total_of_coordinates
    (c : Module.Dual (ZMod 2) (Triangle A → ZMod 2)) (r : ZMod 2)
    (h : ∀ t : Triangle A, c (Pi.single t 1) = r) :
    c = r • totalTriangleChain A := by
  apply LinearMap.ext
  intro f
  change c f = r * totalTriangleChain A f
  rw [dual_apply_eq_sum_coordinates, totalTriangleChain_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [h t, mul_comm]

open Classical in


theorem boundary2_total_apply (c : Edge A → ZMod 2) :
    (edgeCoboundary A).dualMap (totalTriangleChain A) c =
      ∑ e : Edge A, (triangleCofaces A e).card • c e := by
  classical
  change totalTriangleChain A (edgeCoboundary A c) = _
  rw [totalTriangleChain_apply]
  simp_rw [edgeCoboundary_apply]
  calc
    (∑ t : Triangle A, ∑ e ∈ triangleEdges A t, c e) =
        ∑ e : Edge A, ∑ t ∈ triangleCofaces A e, c e := by
      simp only [triangleEdges, triangleCofaces, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = _ := by simp only [Finset.sum_const]

open Classical in


theorem boundary2_total_eq_marked (B : Edge A → Prop)
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = if B e then 1 else 2) :
    (edgeCoboundary A).dualMap (totalTriangleChain A) = markedEdgeChain A B := by
  classical
  apply LinearMap.ext
  intro c
  rw [boundary2_total_apply, markedEdgeChain_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  rw [hcofaces e]
  by_cases he : B e
  · simp only [if_pos he, one_nsmul]
  · simp only [if_neg he]
    exact CharTwo.two_nsmul (c e)



theorem boundary2_total_eq_zero_of_two
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2) :
    (edgeCoboundary A).dualMap (totalTriangleChain A) = 0 := by
  apply LinearMap.ext
  intro c
  rw [boundary2_total_apply]
  simp only [hcofaces, CharTwo.two_nsmul, Finset.sum_const_zero, LinearMap.zero_apply]

end PreAbstractSimplicialComplex.ModTwoCochains
