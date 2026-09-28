import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TetrahedronAdjacency
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TetrahedronChainCoordinates









set_option autoImplicit false

open scoped BigOperators

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} [Fintype ι] (A : PreAbstractSimplicialComplex ι)

open Classical in



theorem tetrahedronCofaces_eq_pair_of_distinct
    (B : Triangle A → Prop)
    (hcofaces : ∀ t : Triangle A,
      (tetrahedronCofaces A t).card = if B t then 1 else 2)
    (t : Triangle A) (q r : Tetrahedron A) (hqr : q ≠ r)
    (htq : t.val ⊆ q.val) (htr : t.val ⊆ r.val) :
    ¬ B t ∧ tetrahedronCofaces A t = {q, r} := by
  classical
  have hq : q ∈ tetrahedronCofaces A t := Finset.mem_filter.mpr ⟨Finset.mem_univ q, htq⟩
  have hr : r ∈ tetrahedronCofaces A t := Finset.mem_filter.mpr ⟨Finset.mem_univ r, htr⟩
  have hpair : {q, r} ⊆ tetrahedronCofaces A t :=
    Finset.insert_subset_iff.mpr ⟨hq, Finset.singleton_subset_iff.mpr hr⟩
  have hle : 2 ≤ (tetrahedronCofaces A t).card := by
    simpa only [Finset.card_pair hqr] using Finset.card_le_card hpair
  have hnot : ¬ B t := by
    intro ht
    rw [hcofaces t, if_pos ht] at hle
    omega
  refine ⟨hnot, (Finset.eq_of_subset_of_card_le hpair ?_).symm⟩
  rw [hcofaces t, if_neg hnot, Finset.card_pair hqr]

open Classical in



theorem exists_scalar_total_of_relative_boundary
    (B : Triangle A → Prop)
    (hcofaces : ∀ t : Triangle A,
      (tetrahedronCofaces A t).card = if B t then 1 else 2)
    (hconn : (tetrahedronGraph A).Connected)
    (c : Module.Dual (ZMod 2) (Tetrahedron A → ZMod 2))
    (hrelative : ∀ t : Triangle A, ¬ B t →
      (triangleCoboundary A).dualMap c (Pi.single t 1) = 0) :
    ∃ r : ZMod 2, c = r • totalTetrahedronChain A ∧
      (triangleCoboundary A).dualMap c = r • markedTriangleChain A B := by
  classical
  have hadj {q r : Tetrahedron A} (hqr : (tetrahedronGraph A).Adj q r) :
      c (Pi.single q 1) = c (Pi.single r 1) := by
    obtain ⟨hne, t, htq, htr⟩ := hqr
    obtain ⟨hnot, hpair⟩ :=
      tetrahedronCofaces_eq_pair_of_distinct A B hcofaces t q r hne htq htr
    have hz := hrelative t hnot
    rw [boundary3_single_eq_sum_coordinates, hpair, Finset.sum_pair hne] at hz
    exact CharTwo.add_eq_zero.mp hz
  have hconstant (q r : Tetrahedron A) : c (Pi.single q 1) = c (Pi.single r 1) := by
    obtain ⟨p⟩ := hconn.preconnected q r
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hadj h).trans ih
  obtain ⟨q⟩ := hconn.nonempty
  let r := c (Pi.single q 1)
  have hc : c = r • totalTetrahedronChain A :=
    tetrahedronChain_eq_smul_total_of_coordinates A c r (fun t => hconstant t q)
  refine ⟨r, hc, ?_⟩
  rw [hc, map_smul, boundary3_total_eq_marked A B hcofaces]

open Classical in



theorem boundary3_injective_of_boundary_nonempty
    (B : Triangle A → Prop)
    (hcofaces : ∀ t : Triangle A,
      (tetrahedronCofaces A t).card = if B t then 1 else 2)
    (hconn : (tetrahedronGraph A).Connected) (hne : ∃ t : Triangle A, B t) :
    Function.Injective (triangleCoboundary A).dualMap := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro c hc
  obtain ⟨r, hcr, hboundary⟩ := exists_scalar_total_of_relative_boundary A B hcofaces
    hconn c (fun t _ => by rw [hc]; rfl)
  obtain ⟨t, ht⟩ := hne
  have hz : (r • markedTriangleChain A B) (Pi.single t 1) = 0 := by
    rw [← hboundary, hc]
    rfl
  have hr : r = 0 := by
    simpa only [LinearMap.smul_apply, smul_eq_mul, markedTriangleChain_single,
      if_pos ht, mul_one] using hz
  rw [hcr, hr, zero_smul]

end PreAbstractSimplicialComplex.ModTwoCochains
