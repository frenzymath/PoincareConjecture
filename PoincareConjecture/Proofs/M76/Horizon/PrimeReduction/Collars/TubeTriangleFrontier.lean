import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.TriangleHalfplaneFrontier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.EndpointCappedTube
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)
local notation "I" => Icc (0 : ℝ) 1






theorem exists_open_returning_triangle_base_neighborhood
    (t a : Finset V3) (ht : AffineIndependent ℝ ((↑) : t → V3))
    (ht3 : t.card = 3) (hat : a ⊆ t) (ha2 : a.card = 2)
    {d : Set V3}
    (hcontact : d ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set V3)) ⊆
      intrinsicInterior ℝ (convexHull ℝ (a : Set V3))) :
    ∃ U : Set V3, IsOpen U ∧ d ⊆ U ∧
      ∀ x ∈ U, x ∈ intrinsicFrontier ℝ (convexHull ℝ (t : Set V3)) ↔
        x ∈ convexHull ℝ (a : Set V3) := by
  classical
  let bad := t.powerset.filter (fun b => b.card = 2 ∧ b ≠ a)
  let D := ⋃ b ∈ bad, convexHull ℝ (b : Set V3)
  have hD : IsClosed D := bad.finite_toSet.isClosed_biUnion
    (fun b _ => (b.finite_toSet.isCompact_convexHull ℝ).isClosed)
  have hproper {b : Finset V3} (hbt : b ⊆ t) (hb2 : b.card = 2) : b ⊂ t :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hbt, fun he => by
      have := congrArg Finset.card he
      omega⟩
  have hdD : Disjoint d D := by
    apply disjoint_left.mpr
    intro x hxd hxD
    obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hxD
    obtain ⟨hbt, hb2, hba⟩ : b ⊆ t ∧ b.card = 2 ∧ b ≠ a := by
      simpa [bad] using hb
    have hxa := hcontact ⟨hxd, ht.convexHull_subset_intrinsicFrontier (hproper hbt hb2) hxb⟩
    have hab : a ⊆ b := by
      by_contra hab
      have hproper' : a ∩ b ⊂ a := Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.inter_subset_left, fun he => hab (he ▸ Finset.inter_subset_right)⟩
      have hxab : x ∈ convexHull ℝ ((a ∩ b : Finset V3) : Set V3) := by
        rw [Finset.coe_inter, ht.convexHull_inter hat hbt]
        exact ⟨intrinsicInterior_subset hxa, hxb⟩
      have hf := (ht.mono (show (a : Set V3) ⊆ (t : Set V3) from hat)).convexHull_subset_intrinsicFrontier
        hproper' hxab
      rw [← intrinsicClosure_sdiff_intrinsicInterior] at hf
      exact hf.2 hxa
    exact hba (Finset.eq_of_subset_of_card_le hab (by omega)).symm
  refine ⟨Dᶜ, hD.isOpen_compl, fun x hx hxD => disjoint_left.mp hdD hx hxD, ?_⟩
  intro x hx
  constructor
  · intro hf
    obtain ⟨v, hvt, hxv⟩ :=
      (ht.mem_intrinsicFrontier_convexHull_finset (by apply Finset.card_pos.mp; omega) x).mp hf
    have hecard : (t.erase v).card = 2 := by rw [Finset.card_erase_of_mem hvt, ht3]
    by_cases he : t.erase v = a
    · simpa only [he] using hxv
    · have heBad : t.erase v ∈ bad := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.erase_subset _ _), hecard, he⟩
      exact (hx (mem_iUnion₂.mpr ⟨t.erase v, heBad, hxv⟩)).elim
  · exact fun hxa => ht.convexHull_subset_intrinsicFrontier (hproper hat ha2) hxa

section Tube

variable (t : Finset V3) (ht : AffineIndependent ℝ ((↑) : t → V3))
  (ht3 : t.card = 3) {T R : Set V3}
  (tube : ↥(Dehn.signedTubeDiamond ×ˢ I) ≃ₜ T)
  (E : Fin 2 → OpenPartialHomeomorph V3 V3)
  (hE : ∀ i, E i ∈ piecewiseAffineGroupoid V3)
  (htriangle : ∀ i y, y ∈ (E i).source →
    (y ∈ convexHull ℝ (t : Set V3) ↔ E i y 0 = 0 ∧ 0 ≤ E i y 2))
  (V : Fin 2 → Set V3) (hVE : ∀ i, V i ⊆ (E i).source)
  (hcover : T ⊆ (⋃ i, V i) ∪ interior R)
  (hfr : ∀ i y, y ∈ V i → (y ∈ frontier R ↔ E i y 2 = 0))
  (hfront : ∀ z : ↥(Dehn.signedTubeDiamond ×ˢ I),
    (tube z : V3) ∈ frontier R ↔ (z : P3).2 = 0 ∨ (z : P3).2 = 1)

include ht ht3 hE htriangle hVE hcover hfr hfront



theorem tube_endface_triangle_mem_intrinsicFrontier
    (z : ↥(Dehn.signedTubeDiamond ×ˢ I))
    (hz : (z : P3).2 = 0 ∨ (z : P3).2 = 1)
    (hzt : (tube z : V3) ∈ convexHull ℝ (t : Set V3)) :
    (tube z : V3) ∈ intrinsicFrontier ℝ (convexHull ℝ (t : Set V3)) := by
  have hzfr := (hfront z).mpr hz
  obtain hcap | hin := hcover (tube z).property
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hcap
    apply ((E i).triangle_intrinsicFrontier_iff_of_halfplane (hE i) t ht ht3
      (htriangle i) (hVE i hi)).mpr
    exact ⟨((htriangle i _ (hVE i hi)).mp hzt).1, (hfr i _ hi).mp hzfr⟩
  · exact (disjoint_left.mp disjoint_interior_frontier hin hzfr).elim



theorem tube_endface_triangle_planar_axis
    (a : Finset V3) {U : Set V3} (hTU : T ⊆ U)
    (hUbase : ∀ y ∈ U,
      y ∈ intrinsicFrontier ℝ (convexHull ℝ (t : Set V3)) ↔
        y ∈ convexHull ℝ (a : Set V3))
    (F : V3 → P2) (hFbase : ∀ y ∈ convexHull ℝ (a : Set V3), (F y).2 = 0)
    (hsheet : ∀ z : ↥(Dehn.signedTubeDiamond ×ˢ I),
      (z : P3).1 ∈ Dehn.signedTubeSheet 0 ↔
        (tube z : V3) ∈ convexHull ℝ (t : Set V3))
    (z : ↥(Dehn.signedTubeDiamond ×ˢ I))
    (hz : (z : P3).2 = 0 ∨ (z : P3).2 = 1)
    (hzsheet : (z : P3).1 ∈ Dehn.signedTubeSheet 0) :
    (F (tube z)).2 = 0 := by
  apply hFbase
  apply (hUbase _ (hTU (tube z).property)).mp
  exact tube_endface_triangle_mem_intrinsicFrontier t ht ht3 tube E hE htriangle V hVE
    hcover hfr hfront z hz ((hsheet z).mp hzsheet)

end Tube

end PoincareConjecture.M76
