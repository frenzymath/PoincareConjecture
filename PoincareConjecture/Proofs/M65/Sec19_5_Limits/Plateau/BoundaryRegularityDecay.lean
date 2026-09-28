import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityIteration
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Normed











set_option autoImplicit false

open Set Metric MeasureTheory Filter
open scoped Topology

namespace PoincareConjecture.M65Boundary

local notation "E" => EuclideanSpace ℝ (Fin 2)

private theorem dyadic_annuli {R : ℝ} (hR : 0 < R) (x : E) :
    let r := fun n : ℕ => R * (1 / 2 : ℝ) ^ n
    let S := fun n : ℕ => closedBall x (r n) \ closedBall x (r (n + 1))
    (∀ n, 0 < r n ∧ r n ≤ R) ∧
      Pairwise (fun n m => Disjoint (S n) (S m)) ∧ (⋃ n, S n) = closedBall x R \ {x} := by
  classical
  dsimp only
  let q : ℝ := 1 / 2
  let r := fun n : ℕ => R * q ^ n
  let S := fun n : ℕ => closedBall x (r n) \ closedBall x (r (n + 1))
  change (∀ n, 0 < r n ∧ r n ≤ R) ∧
    Pairwise (fun n m => Disjoint (S n) (S m)) ∧ (⋃ n, S n) = closedBall x R \ {x}
  have hq : 0 < q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  have hr (n : ℕ) : 0 < r n := mul_pos hR (pow_pos hq n)
  have hmono : Antitone r := by
    intro n m hnm
    apply mul_le_mul_of_nonneg_left _ hR.le
    exact pow_le_pow_of_le_one hq.le hq1.le hnm
  have hrR (n : ℕ) : r n ≤ R := by simpa only [r, pow_zero, mul_one] using hmono (Nat.zero_le n)
  refine ⟨fun n => ⟨hr n, hrR n⟩, ?_, ?_⟩
  · intro n m hnm
    have hd (i j : ℕ) (hij : i < j) : Disjoint (S i) (S j) := by
      apply Set.disjoint_left.mpr
      intro z hz hz'
      exact hz.2 (closedBall_subset_closedBall (hmono (Nat.succ_le_of_lt hij)) hz'.1)
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · exact hd n m hlt
    · exact (hd m n hgt).symm
  · ext z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := mem_iUnion.mp hz
      refine ⟨closedBall_subset_closedBall (hrR n) hn.1, ?_⟩
      intro hz
      have hzx : z = x := Set.mem_singleton_iff.mp hz
      exact hn.2 (hzx ▸ mem_closedBall_self (hr (n + 1)).le)
    · intro hz
      have hdist : 0 < dist z x := dist_pos.mpr (by simpa using hz.2)
      have hratio : dist z x / R ≤ 1 := (div_le_one hR).mpr (mem_closedBall.mp hz.1)
      obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one (div_pos hdist hR) hratio hq hq1
      apply mem_iUnion.mpr
      refine ⟨n, mem_closedBall.mpr ?_, ?_⟩
      · have hh := (div_le_iff₀ hR).mp hn'
        simpa only [r, mul_comm] using hh
      · intro hball
        have hh := (lt_div_iff₀ hR).mp hn
        have hd := mem_closedBall.mp hball
        dsimp only [r] at hd
        nlinarith only [hh, hd]

private theorem dyadic_weight_scale {R α σ : ℝ} (hR : 0 < R) (n : ℕ) :
    (R * (1 / 2 : ℝ) ^ (n + 1)) ^ (-α) *
        (R * (1 / 2 : ℝ) ^ n) ^ σ =
      (R ^ (σ - α) * (1 / 2 : ℝ) ^ (-α)) *
        ((1 / 2 : ℝ) ^ (σ - α)) ^ n := by
  have hq : 0 < (1 / 2 : ℝ) := by norm_num
  rw [pow_succ, ← mul_assoc, Real.mul_rpow (mul_nonneg hR.le (pow_nonneg hq.le _)) hq.le,
    mul_right_comm, ← Real.rpow_add (mul_pos hR (pow_pos hq n))]
  rw [show -α + σ = σ - α by ring, Real.mul_rpow hR.le (pow_nonneg hq.le n)]
  have hp : ((1 / 2 : ℝ) ^ n) ^ (σ - α) = ((1 / 2 : ℝ) ^ (σ - α)) ^ n := by
    rw [← Real.rpow_natCast_mul hq.le, mul_comm (n : ℝ), Real.rpow_mul hq.le,
      Real.rpow_natCast]
  rw [hp]
  ring





theorem weighted_energy_of_disk_decay {R α σ C : ℝ}
    (hR : 0 < R) (hα : 0 < α) (hασ : α < σ) (hC : 0 ≤ C) :
    ∃ K ≥ 0, ∀ (x : E) (F : E → ℝ), Integrable F → (∀ z, 0 ≤ F z) →
      (∀ r : ℝ, 0 < r → r ≤ R → (∫ z in closedBall x r, F z) ≤ C * r ^ σ) →
      IntegrableOn (fun z => ‖z - x‖ ^ (-α) * F z) (closedBall x R) ∧
      (∫ z in closedBall x R, ‖z - x‖ ^ (-α) * F z) ≤ K := by
  classical
  let q : ℝ := (1 / 2 : ℝ) ^ (σ - α)
  let B := C * (R ^ (σ - α) * (1 / 2 : ℝ) ^ (-α))
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (sub_pos.mpr hασ)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsum : Summable (fun n : ℕ => B * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left B
  refine ⟨B * (1 - q)⁻¹, mul_nonneg hB (inv_nonneg.mpr (sub_pos.mpr hq1).le), ?_⟩
  intro x F hF hF0 hdecay
  let r := fun n : ℕ => R * (1 / 2 : ℝ) ^ n
  let S := fun n : ℕ => closedBall x (r n) \ closedBall x (r (n + 1))
  let G := fun z : E => ‖z - x‖ ^ (-α) * F z
  obtain ⟨hr, hdisjoint, hcover⟩ := dyadic_annuli hR x
  change (∀ n, 0 < r n ∧ r n ≤ R) at hr
  change Pairwise (fun n m => Disjoint (S n) (S m)) at hdisjoint
  change (⋃ n, S n) = closedBall x R \ {x} at hcover
  have hS (n : ℕ) : MeasurableSet (S n) :=
    isClosed_closedBall.measurableSet.diff isClosed_closedBall.measurableSet
  have hG0 (z : E) : 0 ≤ G z := mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hF0 z)
  have hmeas : AEStronglyMeasurable G volume :=
    (by fun_prop : Measurable (fun z : E => ‖z - x‖ ^ (-α))).aestronglyMeasurable.mul hF.1
  have hpoint (n : ℕ) (z : E) (hz : z ∈ S n) :
      G z ≤ (r (n + 1)) ^ (-α) * F z := by
    have hd : r (n + 1) < ‖z - x‖ := by
      simpa only [mem_closedBall, dist_eq_norm, not_le] using hz.2
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos (hr (n + 1)).1 hd.le (neg_nonpos.mpr hα.le)) (hF0 z)
  have hGi (n : ℕ) : IntegrableOn G (S n) := by
    apply ((hF.const_mul ((r (n + 1)) ^ (-α))).integrableOn).mono' hmeas.restrict
    filter_upwards [ae_restrict_mem (hS n)] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 z)]
    exact hpoint n z hz
  have hbound (n : ℕ) : (∫ z in S n, G z) ≤ B * q ^ n := by
    calc
      _ ≤ ∫ z in S n, (r (n + 1)) ^ (-α) * F z :=
        integral_mono_ae (hGi n) ((hF.const_mul _).integrableOn)
          (ae_restrict_of_forall_mem (hS n) (hpoint n))
      _ = (r (n + 1)) ^ (-α) * ∫ z in S n, F z := integral_const_mul _ _
      _ ≤ (r (n + 1)) ^ (-α) * ∫ z in closedBall x (r n), F z := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hr (n + 1)).1.le _)
        exact setIntegral_mono_set hF.integrableOn (ae_of_all _ hF0) sdiff_subset.eventuallyLE
      _ ≤ (r (n + 1)) ^ (-α) * (C * (r n) ^ σ) :=
        mul_le_mul_of_nonneg_left (hdecay _ (hr n).1 (hr n).2)
          (Real.rpow_nonneg (hr (n + 1)).1.le _)
      _ = C * ((r (n + 1)) ^ (-α) * (r n) ^ σ) := by ring
      _ = B * q ^ n := by rw [dyadic_weight_scale hR]; exact (mul_assoc _ _ _).symm
  have hnorm (n : ℕ) : (∫ z in S n, ‖G z‖) = ∫ z in S n, G z := by
    apply integral_congr_ae
    filter_upwards [] with z
    exact Real.norm_of_nonneg (hG0 z)
  have hsummable : Summable (fun n : ℕ => ∫ z in S n, G z) :=
    hsum.of_nonneg_of_le (fun _ => integral_nonneg hG0) hbound
  have hGiUnion : IntegrableOn G (⋃ n, S n) := by
    apply integrableOn_iUnion_of_summable_integral_norm hGi
    simpa only [hnorm] using hsummable
  have heq : (⋃ n, S n) =ᵐ[volume] closedBall x R := by
    rw [hcover]
    exact sdiff_null_ae_eq_self (measure_singleton x)
  have hball : IntegrableOn G (closedBall x R) :=
    (integrableOn_congr_set_ae heq).mp hGiUnion
  refine ⟨hball, ?_⟩
  calc
    (∫ z in closedBall x R, G z) = ∫ z in ⋃ n, S n, G z :=
      setIntegral_congr_set heq.symm
    _ = ∑' n : ℕ, ∫ z in S n, G z := integral_iUnion hS hdisjoint hGiUnion
    _ ≤ ∑' n : ℕ, B * q ^ n := hsummable.tsum_le_tsum hbound hsum
    _ = B * (1 - q)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]

end PoincareConjecture.M65Boundary
