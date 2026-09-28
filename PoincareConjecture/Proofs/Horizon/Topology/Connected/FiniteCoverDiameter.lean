import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open Set Function

namespace Poincare.Topology

theorem sub_le_card_mul_of_finite_cover
    {X ι : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Finite ι]
    {h : X → ℝ} (hh : Continuous h) (U : ι → Set X)
    (hcover : ∀ x, ∃ i, x ∈ U i) {D : ℝ} (hD : 0 ≤ D)
    (hosc : ∀ i, ∀ x ∈ U i, ∀ y ∈ U i, |h x - h y| ≤ D)
    (x y : X) : h y - h x ≤ Nat.card ι * D := by
  classical
  let N := Nat.card ι
  obtain ⟨i₀, _⟩ := hcover x
  let : Nonempty ι := ⟨i₀⟩
  have hN : 0 < N := Nat.card_pos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  by_contra! hlarge
  let r := (h y - h x) / N
  have hrD : D < r := by
    apply (lt_div_iff₀ hNr).mpr
    simpa only [mul_comm] using hlarge
  have hr : 0 < r := hD.trans_lt hrD
  have hNr_eq : (N : ℝ) * r = h y - h x := by dsimp only [r]; field_simp
  have hpoints (i : Fin (N + 1)) : ∃ z : X, h z = h x + (i.val : ℝ) * r := by
    have hi : (i.val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
    have himem : h x + (i.val : ℝ) * r ∈ Icc (h x) (h y) := by
      constructor
      · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hr.le)
      · nlinarith
    obtain ⟨z, _, hz⟩ := isPreconnected_univ.intermediate_value
      (mem_univ x) (mem_univ y) hh.continuousOn himem
    exact ⟨z, hz⟩
  choose z hz using hpoints
  choose index hindex using fun i => hcover (z i)
  have hne (i j : Fin (N + 1)) (hlt : i.val < j.val) : index i ≠ index j := by
    intro hij
    have hosc' := hosc (index j) (z i) (hij ▸ hindex i) (z j) (hindex j)
    rw [hz i, hz j] at hosc'
    have hstep : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hlt
    have hdiff : 0 ≤ h x + (j.val : ℝ) * r - (h x + (i.val : ℝ) * r) := by
      nlinarith
    rw [abs_sub_comm, abs_of_nonneg hdiff] at hosc'
    nlinarith
  have hinj : Injective index := by
    intro i j hij
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · exact (hne i j hlt hij).elim
    · exact Fin.ext heq
    · exact (hne j i hgt hij.symm).elim
  have hcard := Nat.card_le_card_of_injective index hinj
  rw [Nat.card_fin] at hcard
  omega

theorem dist_le_card_mul_of_image_ball_cover
    {X Y ι : Type*} [PseudoMetricSpace X] [PreconnectedSpace X]
    [PseudoMetricSpace Y] [Finite ι]
    (f : X → Y) (q : ι → Y) {r D : ℝ} (hD : 0 ≤ D)
    (hcover : ∀ x : X, ∃ i, dist (f x) (q i) < r)
    (hlocal : ∀ x y : X, dist (f x) (f y) < 2 * r → dist x y ≤ D)
    (x y : X) : dist x y ≤ Nat.card ι * D := by
  have hosc : ∀ i, ∀ z ∈ f ⁻¹' Metric.ball (q i) r,
      ∀ w ∈ f ⁻¹' Metric.ball (q i) r, |dist x z - dist x w| ≤ D := by
    intro i z hz w hw
    have hrev : |dist x z - dist x w| ≤ dist z w := by
      simpa only [dist_comm] using abs_dist_sub_le z w x
    apply hrev.trans
    apply hlocal
    have htri := dist_triangle (f z) (q i) (f w)
    rw [dist_comm (q i) (f w)] at htri
    exact htri.trans_lt (by simpa only [two_mul] using add_lt_add hz hw)
  have h := sub_le_card_mul_of_finite_cover (h := dist x)
    (continuous_const.dist continuous_id) (fun i => f ⁻¹' Metric.ball (q i) r)
    hcover hD hosc x y
  simpa only [dist_self, sub_zero] using h

end Poincare.Topology
