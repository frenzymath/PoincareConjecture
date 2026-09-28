import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionEdgeGluing














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

section Faces

variable {I : Type*} (face : I → SmoothFace AnnulusCoordinates)
  (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
  (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
  (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
  (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
  (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
    affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
  (hfront : ∀ i j, i ≠ j → (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)

include hsource hcarrier hboundary hfront







theorem m64Intrinsic_region_edge_has_at_most_two_slots
    (p q r : I × Fin 3)
    (hpq : faceBoundaryIndex face p.1 p.2 = faceBoundaryIndex face q.1 q.2)
    (hpr : faceBoundaryIndex face p.1 p.2 = faceBoundaryIndex face r.1 r.2) :
    p = q ∨ p = r ∨ q = r := by
  by_cases hpqe : p = q
  · exact Or.inl hpqe
  by_cases hpre : p = r
  · exact Or.inr (Or.inl hpre)
  by_cases hqre : q = r
  · exact Or.inr (Or.inr hqre)
  exfalso
  have hfaces {u v : I × Fin 3} (huv : u ≠ v)
      (he : faceBoundaryIndex face u.1 u.2 = faceBoundaryIndex face v.1 v.2) : u.1 ≠ v.1 := by
    intro h
    apply huv
    apply Prod.ext h
    apply Euler.coordinate_faceBoundaryIndex_injective face F b hsource hboundary v.1
    simpa only [h] using he
  have hpqf := hfaces hpqe hpq
  have hrpf := hfaces (Ne.symm hpre) hpr.symm
  have hrqf := hfaces (Ne.symm hqre) (hpr.symm.trans hpq)
  let x := ((face p.1).boundary p.2).map (1 / 2 : ℝ)
  have hxint : x ∈ interior ((face p.1).carrier ∪ (face q.1).carrier) :=
    m64Intrinsic_shared_edge_image_mem_interior (face p.1) (face q.1) (F p.1) (F q.1)
      (b p.1) (b q.1) (hsource p.1) (hsource q.1) (hcarrier p.1) (hcarrier q.1)
      (hboundary p.1) (hboundary q.1) (hfront _ _ hpqf) p.2 q.2
      ((faceBoundaryIndex_eq_iff face _ _ _ _).mp hpq) (by norm_num)
  have hxr : x ∈ (face r.1).carrier := by
    apply (face r.1).isClosed_carrier.frontier_subset
    apply (face r.1).boundary_image_subset_frontier r.2
    rw [← (faceBoundaryIndex_eq_iff face _ _ _ _).mp hpr]
    exact mem_image_of_mem _ (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
  have hdisjoint : Disjoint (interior (face r.1).carrier)
      (interior ((face p.1).carrier ∪ (face q.1).carrier)) := by
    apply disjoint_left.mpr
    intro z hz hzpq
    rcases interior_subset hzpq with hzp | hzq
    · exact (hfront _ _ hrpf ⟨interior_subset hz, hzp⟩).2 hz
    · exact (hfront _ _ hrqf ⟨interior_subset hz, hzq⟩).2 hz
  have hreg : closure (interior (face r.1).carrier) = (face r.1).carrier := by
    rw [hcarrier]
    exact coordinate_triangle_closure_interior (F r.1) (b r.1) (hsource r.1)
  have hclosed := hdisjoint.closure_left isOpen_interior
  rw [hreg] at hclosed
  exact disjoint_left.mp hclosed hxr hxint







theorem m64Intrinsic_region_edge_fiber_card_one_or_two [Finite I]
    (e : FaceBoundaryEdge face) :
    Nat.card {p : I × Fin 3 // faceBoundaryIndex face p.1 p.2 = e} = 1 ∨
      Nat.card {p : I × Fin 3 // faceBoundaryIndex face p.1 p.2 = e} = 2 := by
  classical
  let A := {p : I × Fin 3 // faceBoundaryIndex face p.1 p.2 = e}
  let _ := Fintype.ofFinite A
  let a : A := ⟨e.out, Quotient.out_eq e⟩
  by_cases hex : ∃ b : A, b ≠ a
  · obtain ⟨d, hda⟩ := hex
    have had : a ≠ d := Ne.symm hda
    have huniv : (Finset.univ : Finset A) = {a, d} := by
      ext c
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      rcases m64Intrinsic_region_edge_has_at_most_two_slots face F b hsource hcarrier hboundary
        hfront a.1 d.1 c.1 (a.2.trans d.2.symm) (a.2.trans c.2.symm) with h | h | h
      · exact False.elim (had (Subtype.ext h))
      · exact Or.inl (Subtype.ext h.symm)
      · exact Or.inr (Subtype.ext h.symm)
    right
    change Nat.card A = 2
    rw [Nat.card_eq_fintype_card, Fintype.card, huniv, Finset.card_pair had]
  · have huniv : (Finset.univ : Finset A) = {a} := by
      ext c
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      by_contra hca
      exact hex ⟨c, hca⟩
    left
    change Nat.card A = 1
    rw [Nat.card_eq_fintype_card, Fintype.card, huniv, Finset.card_singleton]







theorem m64Intrinsic_region_edge_slot_count [Finite I] :
    3 * Nat.card I + Nat.card {e : FaceBoundaryEdge face //
      Nat.card {p : I × Fin 3 // faceBoundaryIndex face p.1 p.2 = e} = 1} =
      2 * Nat.card (FaceBoundaryEdge face) := by
  classical
  let _ := Fintype.ofFinite I
  let _ := Fintype.ofFinite (FaceBoundaryEdge face)
  let slot (p : I × Fin 3) := faceBoundaryIndex face p.1 p.2
  have hsumfiber : (∑ e : FaceBoundaryEdge face, Nat.card {p : I × Fin 3 // slot p = e}) =
      3 * Nat.card I := by
    have h := Fintype.card_congr (Equiv.sigmaFiberEquiv slot)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_prod,
      Fintype.card_fin, Nat.mul_comm] using h
  have hboundarycount : (∑ e : FaceBoundaryEdge face,
      if Nat.card {p : I × Fin 3 // slot p = e} = 1 then (1 : ℕ) else 0) =
      Nat.card {e : FaceBoundaryEdge face // Nat.card {p : I × Fin 3 // slot p = e} = 1} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [Finset.sum_boole, Nat.cast_id]
  have hsum : (∑ e : FaceBoundaryEdge face,
      (Nat.card {p : I × Fin 3 // slot p = e} +
        if Nat.card {p : I × Fin 3 // slot p = e} = 1 then 1 else 0)) =
      ∑ _e : FaceBoundaryEdge face, 2 := by
    apply Finset.sum_congr rfl
    intro e _
    rcases m64Intrinsic_region_edge_fiber_card_one_or_two face F b hsource hcarrier
      hboundary hfront e with h | h <;> simp only [slot, h] <;> norm_num
  rw [Finset.sum_add_distrib, hsumfiber, hboundarycount] at hsum
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Nat.mul_comm, Nat.cast_id, slot] using hsum

end Faces

end PoincareConjecture
