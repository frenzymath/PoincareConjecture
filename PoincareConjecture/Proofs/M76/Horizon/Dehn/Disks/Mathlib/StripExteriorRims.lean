import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripExteriorDisks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.MiddleRimIntervals

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

theorem exists_strip_exterior_disks_with_rim_intervals
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S Q : Set E} (hS : IsFinitePLBallPair P2 S Q) (c : Bool → P2 → E)
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source S)
    (hcQ : ∀ i x, x ∈ source → (c i x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1))
    (hdisj : Disjoint (c false '' source) (c true '' source)) :
    ∃ (A M C L R : Set E) (s0 s1 : Bool) (u v : E),
      let a0 := c false (0, farArmParameter (!s0))
      let a1 := c false (1, farArmParameter (!s0))
      let l0 := c false (0, farArmParameter s0)
      let l1 := c false (1, farArmParameter s0)
      let r0 := c true (0, farArmParameter s1)
      let r1 := c true (1, farArmParameter s1)
      let c0 := c true (0, farArmParameter (!s1))
      let c1 := c true (1, farArmParameter (!s1))
      let WA := c false '' arm (farArmParameter (!s0))
      let WL := c false '' arm (farArmParameter s0)
      let WR := c true '' arm (farArmParameter s1)
      let WC := c true '' arm (farArmParameter (!s1))
      IsFinitePLBallPair P2 A ((A ∩ Q) ∪ WA) ∧
      IsFinitePLBallPair P2 M (((M ∩ Q) ∪ WL) ∪ WR) ∧
      IsFinitePLBallPair P2 C ((C ∩ Q) ∪ WC) ∧
      Disjoint A M ∧ Disjoint M C ∧ Disjoint A C ∧
      ((A ∪ M) ∪ C) ∪ ((c false '' source) ∪ (c true '' source)) = S ∧
      (c false '' source) ∩ A = WA ∧ (c false '' source) ∩ M = WL ∧
      (c true '' source) ∩ M = WR ∧ (c true '' source) ∩ C = WC ∧
      Disjoint A (c true '' source) ∧ Disjoint C (c false '' source) ∧
      IsFinitePLBallPair ℝ (A ∩ Q) {a0, a1} ∧
      IsFinitePLBallPair ℝ (C ∩ Q) {c0, c1} ∧
      ((u = r0 ∧ v = r1) ∨ (u = r1 ∧ v = r0)) ∧ u ≠ v ∧
      IsFinitePLBallPair ℝ L {l0, u} ∧ IsFinitePLBallPair ℝ R {v, l1} ∧
      Disjoint L R ∧ L ∪ R = M ∩ Q ∧
      L ∩ WL = {l0} ∧ R ∩ WL = {l1} ∧ L ∩ WR = {u} ∧ R ∩ WR = {v} := by
  obtain ⟨A, M, C, s0, s1, hA, hM, hC, hAM, hMC, hAC, hcover,
    h0A, h0M, h1M, h1C, hA1, hC0⟩ :=
    exists_strip_exterior_disks hS c hcPL hci hcS hcQ hdisj
  have hfar (s : Bool) : farArmParameter s ∈ Icc (-1 : ℝ) 1 := by
    cases s <;> norm_num [farArmParameter]
  obtain ⟨hWA, hane, _⟩ :=
    exists_embedded_strip_arm_parameter (c false) (hcPL false) (hci false)
      (farArmParameter (!s0)) (hfar (!s0))
  obtain ⟨hWL, hlne, _⟩ :=
    exists_embedded_strip_arm_parameter (c false) (hcPL false) (hci false)
      (farArmParameter s0) (hfar s0)
  obtain ⟨hWR, hrne, _⟩ :=
    exists_embedded_strip_arm_parameter (c true) (hcPL true) (hci true)
      (farArmParameter s1) (hfar s1)
  obtain ⟨hWC, hcne, _⟩ :=
    exists_embedded_strip_arm_parameter (c true) (hcPL true) (hci true)
      (farArmParameter (!s1)) (hfar (!s1))
  have hWAQ := embedded_strip_arm_inter_old_rim (c false) (hcQ false)
    (farArmParameter (!s0)) (hfar (!s0))
  have hWLQ := embedded_strip_arm_inter_old_rim (c false) (hcQ false)
    (farArmParameter s0) (hfar s0)
  have hWRQ := embedded_strip_arm_inter_old_rim (c true) (hcQ true)
    (farArmParameter s1) (hfar s1)
  have hWCQ := embedded_strip_arm_inter_old_rim (c true) (hcQ true)
    (farArmParameter (!s1)) (hfar (!s1))
  have hAL := outer_disk_old_rim_is_interval hA hWA hane hWAQ
  have hCL := outer_disk_old_rim_is_interval hC hWC hcne hWCQ
  have hWLWR := hdisj.mono (image_mono (arm_far_subset_source s0))
    (image_mono (arm_far_subset_source s1))
  obtain ⟨L, R, u, v, hpair, huv, hL, hR, hLR, hLRQ, hLW, hRW, hLZ, hRZ⟩ :=
    exists_middle_disk_old_rim_intervals hM hWL hWR hlne hrne hWLWR hWLQ hWRQ
  exact ⟨A, M, C, L, R, s0, s1, u, v, hA, hM, hC, hAM, hMC, hAC, hcover,
    h0A, h0M, h1M, h1C, hA1, hC0, hAL, hCL, pair_eq_pair_iff.mp hpair,
    huv, hL, hR, hLR, hLRQ, hLW, hRW, hLZ, hRZ⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
