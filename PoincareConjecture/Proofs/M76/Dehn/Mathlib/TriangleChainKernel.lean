import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleAdjacency
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleChainCoordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

open scoped BigOperators

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} [Fintype ι] (A : PreAbstractSimplicialComplex ι)

open Classical in

theorem triangleCofaces_eq_pair_of_distinct
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card ≤ 2)
    (e : Edge A) (q r : Triangle A) (hqr : q ≠ r)
    (heq : e.val ⊆ q.val) (her : e.val ⊆ r.val) :
    triangleCofaces A e = {q, r} := by
  have hq : q ∈ triangleCofaces A e := Finset.mem_filter.mpr ⟨Finset.mem_univ q, heq⟩
  have hr : r ∈ triangleCofaces A e := Finset.mem_filter.mpr ⟨Finset.mem_univ r, her⟩
  have hpair : {q, r} ⊆ triangleCofaces A e :=
    Finset.insert_subset_iff.mpr ⟨hq, Finset.singleton_subset_iff.mpr hr⟩
  apply (Finset.eq_of_subset_of_card_le hpair ?_).symm
  rw [Finset.card_pair hqr]
  exact hcofaces e

open Classical in

theorem boundary2_ker_coordinates_eq
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card ≤ 2)
    (hconn : (triangleGraph A).Preconnected)
    (c : Module.Dual (ZMod 2) (Triangle A → ZMod 2))
    (hc : (edgeCoboundary A).dualMap c = 0) (q r : Triangle A) :
    c (Pi.single q 1) = c (Pi.single r 1) := by
  have hadj {q r : Triangle A} (hqr : (triangleGraph A).Adj q r) :
      c (Pi.single q 1) = c (Pi.single r 1) := by
    obtain ⟨hne, e, heq, her⟩ := hqr
    have hpair := triangleCofaces_eq_pair_of_distinct A hcofaces e q r hne heq her
    have hz : (edgeCoboundary A).dualMap c (Pi.single e 1) = 0 := by rw [hc]; rfl
    rw [boundary2_single_eq_sum_coordinates, hpair, Finset.sum_pair hne] at hz
    exact CharTwo.add_eq_zero.mp hz
  obtain ⟨p⟩ := hconn q r
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hadj h).trans ih

open Classical in

theorem boundary2_ker_eq_smul_total
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card ≤ 2)
    (hconn : (triangleGraph A).Preconnected)
    (c : Module.Dual (ZMod 2) (Triangle A → ZMod 2))
    (hc : (edgeCoboundary A).dualMap c = 0) (q : Triangle A) :
    c = c (Pi.single q 1) • totalTriangleChain A :=
  triangleChain_eq_smul_total_of_coordinates A c _
    (fun t => boundary2_ker_coordinates_eq A hcofaces hconn c hc t q)

open Classical in

theorem boundary2_ker_eq_bot_of_one_coface
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card ≤ 2)
    (hconn : (triangleGraph A).Preconnected)
    (hne : ∃ e : Edge A, (triangleCofaces A e).card = 1) :
    LinearMap.ker (edgeCoboundary A).dualMap = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro c hc
  obtain ⟨e, he⟩ := hne
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp he
  have hz : c (Pi.single q 1) = 0 := by
    have hz : (edgeCoboundary A).dualMap c (Pi.single e 1) = 0 := by rw [hc]; rfl
    rw [boundary2_single_eq_sum_coordinates, hq, Finset.sum_singleton] at hz
    exact hz
  rw [boundary2_ker_eq_smul_total A hcofaces hconn c hc q, hz, zero_smul]

open Classical in

noncomputable def boundary2KerEquiv
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (hconn : (triangleGraph A).Preconnected) (q : Triangle A) :
    LinearMap.ker (edgeCoboundary A).dualMap ≃ₗ[ZMod 2] ZMod 2 where
  toFun c := c.val (Pi.single q 1)
  invFun r := ⟨r • totalTriangleChain A, by
    change (edgeCoboundary A).dualMap (r • totalTriangleChain A) = 0
    rw [map_smul, boundary2_total_eq_zero_of_two A hcofaces, smul_zero]⟩
  left_inv c := by
    apply Subtype.ext
    exact (boundary2_ker_eq_smul_total A (fun e => (hcofaces e).le)
      hconn c.val c.property q).symm
  right_inv r := by
    simp only [LinearMap.smul_apply, smul_eq_mul, totalTriangleChain_single, mul_one]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_boundary2_ker_of_two_cofaces
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (hconn : (triangleGraph A).Connected) :
    Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary A).dualMap) = 1 := by
  let q : Triangle A := Classical.choice hconn.nonempty
  simpa using (boundary2KerEquiv A hcofaces hconn.preconnected q).finrank_eq

theorem finrank_boundary2_ker_of_one_coface
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card ≤ 2)
    (hconn : (triangleGraph A).Preconnected)
    (hne : ∃ e : Edge A, (triangleCofaces A e).card = 1) :
    Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary A).dualMap) = 0 := by
  rw [boundary2_ker_eq_bot_of_one_coface A hcofaces hconn hne]
  simp

end PreAbstractSimplicialComplex.ModTwoCochains
