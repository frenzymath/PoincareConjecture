import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleChainKernel

set_option autoImplicit false
open scoped BigOperators

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} [Fintype ι] (A : PreAbstractSimplicialComplex ι)

open Classical in
theorem markedEdgeChain_single (B : Edge A → Prop) (e : Edge A) :
    markedEdgeChain A B (Pi.single e 1) = if B e then 1 else 0 := by
  rw [markedEdgeChain_apply, Finset.sum_pi_single']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
theorem markedEdgeChain_boundary_eq_zero_of_degrees
    (B : Edge A → Prop)
    (hdegree : ∀ v : ι, (Finset.univ.filter (fun e : Edge A ↦ B e ∧ v ∈ e.val)).card = 0 ∨
      (Finset.univ.filter (fun e : Edge A ↦ B e ∧ v ∈ e.val)).card = 2) :
    (vertexCoboundary A).dualMap (markedEdgeChain A B) = 0 := by
  classical
  apply LinearMap.ext
  intro f
  change markedEdgeChain A B (vertexCoboundary A f) = 0
  rw [markedEdgeChain_apply]
  simp only [vertexCoboundary_apply]
  calc
    (∑ e ∈ Finset.univ.filter B, ∑ v ∈ e.val, f v) =
        ∑ e : Edge A, ∑ v : ι, if B e ∧ v ∈ e.val then f v else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : B e
      · simp only [he, true_and, ite_true]
        rw [← Finset.sum_filter]
        have hf : Finset.univ.filter (fun v ↦ v ∈ e.val) = e.val := by ext v; simp
        rw [hf]
      · simp only [he, false_and, if_false, Finset.sum_const_zero]
    _ = ∑ v : ι, (Finset.univ.filter (fun e : Edge A ↦ B e ∧ v ∈ e.val)).card • f v := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.sum_filter, Finset.sum_const]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      rcases hdegree v with h | h
      · rw [h, zero_nsmul]
      · rw [h, CharTwo.two_nsmul]

open Classical in
theorem exists_scalar_totalTriangle_of_relative_boundary
    (B : Edge A → Prop)
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = if B e then 1 else 2)
    (hconn : (triangleGraph A).Connected)
    (c : Module.Dual (ZMod 2) (Triangle A → ZMod 2))
    (hrelative : ∀ e : Edge A, ¬ B e →
      (edgeCoboundary A).dualMap c (Pi.single e 1) = 0) :
    ∃ r : ZMod 2, c = r • totalTriangleChain A ∧
      (edgeCoboundary A).dualMap c = r • markedEdgeChain A B := by
  classical
  have hle (e : Edge A) : (triangleCofaces A e).card ≤ 2 := by
    rw [hcofaces]
    split_ifs <;> norm_num
  have hadj {q r : Triangle A} (hqr : (triangleGraph A).Adj q r) :
      c (Pi.single q 1) = c (Pi.single r 1) := by
    obtain ⟨hne, e, heq, her⟩ := hqr
    have hpair := triangleCofaces_eq_pair_of_distinct A hle e q r hne heq her
    have hnot : ¬ B e := by
      intro he
      have hcard := hcofaces e
      rw [if_pos he, hpair, Finset.card_pair hne] at hcard
      omega
    have hz := hrelative e hnot
    rw [boundary2_single_eq_sum_coordinates, hpair, Finset.sum_pair hne] at hz
    exact CharTwo.add_eq_zero.mp hz
  have hconstant (q r : Triangle A) : c (Pi.single q 1) = c (Pi.single r 1) := by
    obtain ⟨p⟩ := hconn.preconnected q r
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hadj h).trans ih
  obtain ⟨q⟩ := hconn.nonempty
  let r := c (Pi.single q 1)
  have hc : c = r • totalTriangleChain A :=
    triangleChain_eq_smul_total_of_coordinates A c r (fun t ↦ hconstant t q)
  refine ⟨r, hc, ?_⟩
  rw [hc, map_smul, boundary2_total_eq_marked A B hcofaces]

end PreAbstractSimplicialComplex.ModTwoCochains
