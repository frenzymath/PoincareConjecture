import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.WholeCircleAdjustments
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.RimCircleCoordinates
import Mathlib.Order.Interval.Set.Infinite

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

open PoincareConjecture.M76.Dehn
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem injective_planar_annulus_rim (b : Bool) :
    Function.Injective (annulusRimPoint b) := by
  intro z w h
  have hh := injective_annulusMap (L := 8) (d := 1) (by norm_num) (by norm_num)
    (a₁ := (z, ⟨if b then 1 else -1, by cases b <;> norm_num⟩))
    (a₂ := (w, ⟨if b then 1 else -1, by cases b <;> norm_num⟩))
    (congrArg Subtype.val h)
  exact congrArg Prod.fst hh

theorem exists_depth_preserving_planar_annulus_phase (a : Circle) :
    ∃ S : Ann ≃ₜ Ann, S.IsFinitePL ∧
      (∀ x : Ann, depth 8 (S x) = depth 8 x) ∧
      ∀ b z, S (annulusRimPoint b z) = annulusRimPoint b (z + a) := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let t : ℝ := AddCircle.equivIco (4 * (8 : ℝ)) 0 a
  have ht : t ∈ Icc 0 (4 * (8 : ℝ)) :=
    ⟨(AddCircle.equivIco (4 * (8 : ℝ)) 0 a).property.1,
      by simpa only [zero_add] using (AddCircle.equivIco (4 * (8 : ℝ)) 0 a).property.2.le⟩
  have hta : (t : Circle) = a := AddCircle.coe_equivIco
  obtain ⟨S, hS, hd, hv⟩ := exists_annulus_prescribed_phase_shear
    (L := 8) (d := 1) (by norm_num) (by norm_num) ht ht
  refine ⟨S, hS, hd, ?_⟩
  intro b z
  let s : ℝ := AddCircle.equivIco (4 * (8 : ℝ)) 0 z
  have hs : s ∈ Icc 0 (4 * (8 : ℝ)) :=
    ⟨(AddCircle.equivIco (4 * (8 : ℝ)) 0 z).property.1,
      by simpa only [zero_add] using (AddCircle.equivIco (4 * (8 : ℝ)) 0 z).property.2.le⟩
  have hsz : (s : Circle) = z := AddCircle.coe_equivIco
  have hh := hv s hs ⟨if b then 1 else -1, by cases b <;> norm_num⟩
  have heq : s + (t + t) / 2 + (t - t) / (2 * 1) *
      (if b then 1 else -1) = s + t := by ring
  simp only [heq, AddCircle.coe_add, hsz, hta] at hh
  exact Subtype.ext hh

theorem exists_planar_annulus_phase_avoiding_finite_contacts
    (Q : Set Ann) (hQ : Q.Finite) (P : Set Circle) (hP : P.Finite) :
    ∃ (a : Circle) (S : Ann ≃ₜ Ann), S.IsFinitePL ∧
      (∀ x : Ann, depth 8 (S x) = depth 8 x) ∧
      (∀ b z, S (annulusRimPoint b z) = annulusRimPoint b (z + a)) ∧
      ∀ b z, z ∈ P → S (annulusRimPoint b z) ∉ Q := by
  classical
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let : Infinite (Ico (0 : ℝ) (0 + 4 * 8)) := Ico.infinite (by norm_num)
  let : Infinite Circle := Infinite.of_injective (AddCircle.equivIco (4 * (8 : ℝ)) 0).symm
    (AddCircle.equivIco (4 * (8 : ℝ)) 0).symm.injective
  let bad : Set Circle := ⋃ (b : Bool) (z ∈ P),
    (fun a => annulusRimPoint b (z + a)) ⁻¹' Q
  have hbad : bad.Finite := by
    apply Set.finite_iUnion
    intro b
    apply hP.biUnion
    intro z _
    exact hQ.preimage ((injective_planar_annulus_rim b).comp (add_right_injective z)).injOn
  obtain ⟨a, _, ha⟩ := (Set.infinite_univ (α := Circle)).exists_notMem_finite hbad
  obtain ⟨S, hS, hd, hr⟩ := exists_depth_preserving_planar_annulus_phase a
  refine ⟨a, S, hS, hd, hr, ?_⟩
  intro b z hz h
  apply ha
  exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨z,
    Set.mem_iUnion.mpr ⟨hz, by simpa only [mem_preimage, ← hr] using h⟩⟩⟩

theorem exists_planar_annulus_phase_avoiding_finite_rim_points
    (Q D : Set Ann) (hQ : Q.Finite) (hD : D.Finite)
    (hDrim : ∀ x ∈ D, depth 8 (x : ℝ × ℝ) = -1 ∨ depth 8 (x : ℝ × ℝ) = 1) :
    ∃ (a : Circle) (S : Ann ≃ₜ Ann), S.IsFinitePL ∧
      (∀ x : Ann, depth 8 (S x) = depth 8 x) ∧
      (∀ b z, S (annulusRimPoint b z) = annulusRimPoint b (z + a)) ∧
      Disjoint (S '' D) Q := by
  let P : Set Circle := ⋃ b : Bool, annulusRimPoint b ⁻¹' D
  have hP : P.Finite := Set.finite_iUnion (fun b =>
    hD.preimage (injective_planar_annulus_rim b).injOn)
  obtain ⟨a, S, hS, hd, hr, hav⟩ :=
    exists_planar_annulus_phase_avoiding_finite_contacts Q hQ P hP
  refine ⟨a, S, hS, hd, hr, Set.disjoint_left.mpr ?_⟩
  rintro _ ⟨x, hx, rfl⟩ hQx
  have hxrim : ∃ b, x ∈ range (annulusRimPoint b) := by
    rcases hDrim x hx with hn | hp
    · exact ⟨false, (range_annulusRimPoint false).symm ▸ hn⟩
    · exact ⟨true, (range_annulusRimPoint true).symm ▸ hp⟩
  obtain ⟨b, z, rfl⟩ := hxrim
  exact hav b z (Set.mem_iUnion.mpr ⟨b, hx⟩) hQx

end PoincareConjecture.M76
