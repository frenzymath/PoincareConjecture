import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.MonotoneHelly
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.LiftNormalization

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M64

theorem degreeOneLift_subsequence_ae (sigma : ℕ → M64PeriodicDegreeOneLift) :
    ∃ (k : ℕ → ℕ) (L : ℝ → ℝ), StrictMono k ∧ Monotone L ∧
      (∀ x, L (x + curvePeriod) = L x + curvePeriod) ∧
      L 0 ∈ Icc (0 : ℝ) curvePeriod ∧
      ∀ᵐ x ∂volume, Tendsto (fun j => (normalizedDegreeOneLift (sigma (k j))).map x)
        atTop (𝓝 (L x)) := by
  let f := fun j => (normalizedDegreeOneLift (sigma j)).map
  have hb (x : ℝ) : ∃ lo hi : ℝ, ∀ j, f j x ∈ Icc lo hi :=
    ⟨x - curvePeriod, x + 2 * curvePeriod,
      fun j => normalizedDegreeOneLift_bounds (sigma j) x⟩
  obtain ⟨k, L, hk, hL, heq, _hcont, hae⟩ :=
    monotone_sequence_subsequence_ae f
      (fun j => (normalizedDegreeOneLift (sigma j)).monotone) hb
  have hperiod : ∀ x, L (x + curvePeriod) = L x + curvePeriod := by
    intro x
    rw [heq, heq]
    exact liminf_period_shift (fun j => f (k j))
      (fun j => (normalizedDegreeOneLift (sigma (k j))).period_shift)
      (fun x => ⟨x - curvePeriod, x + 2 * curvePeriod,
        fun j => normalizedDegreeOneLift_bounds (sigma (k j)) x⟩) x
  have hbelow : IsBoundedUnder (· ≥ ·) atTop (fun j => f (k j) 0) :=
    isBoundedUnder_of ⟨0, fun j => (normalizedDegreeOneLift_zero (sigma (k j))).1⟩
  have habove : IsBoundedUnder (· ≤ ·) atTop (fun j => f (k j) 0) :=
    isBoundedUnder_of ⟨curvePeriod,
      fun j => (normalizedDegreeOneLift_zero (sigma (k j))).2.le⟩
  have hzero : L 0 ∈ Icc (0 : ℝ) curvePeriod := by
    rw [heq]
    exact ⟨le_liminf_of_le habove.isCobounded_ge
        (Eventually.of_forall fun j => (normalizedDegreeOneLift_zero (sigma (k j))).1),
      (liminf_le_limsup habove hbelow).trans
        (limsup_le_of_le hbelow.isCobounded_le
          (Eventually.of_forall fun j => (normalizedDegreeOneLift_zero (sigma (k j))).2.le))⟩
  exact ⟨k, L, hk, hL, hperiod, hzero, hae⟩

theorem degreeOneLift_pair_target_subsequence_ae
    {X : Type*} [TopologicalSpace X] (c0 c1 : ℝ → X)
    (hc0 : Continuous c0) (hc1 : Continuous c1)
    (hp0 : Function.Periodic c0 curvePeriod) (hp1 : Function.Periodic c1 curvePeriod)
    (sigma0 sigma1 : ℕ → M64PeriodicDegreeOneLift) :
    ∃ (k : ℕ → ℕ) (L0 L1 : ℝ → ℝ), StrictMono k ∧
      Monotone L0 ∧ Monotone L1 ∧
      (∀ x, L0 (x + curvePeriod) = L0 x + curvePeriod) ∧
      (∀ x, L1 (x + curvePeriod) = L1 x + curvePeriod) ∧
      L0 0 ∈ Icc (0 : ℝ) curvePeriod ∧ L1 0 ∈ Icc (0 : ℝ) curvePeriod ∧
      (∀ᵐ x ∂volume, Tendsto (fun j => c0 ((sigma0 (k j)).map x))
        atTop (𝓝 (c0 (L0 x)))) ∧
      ∀ᵐ x ∂volume, Tendsto (fun j => c1 ((sigma1 (k j)).map x))
        atTop (𝓝 (c1 (L1 x))) := by
  obtain ⟨k0, L0, hk0, hL0, hP0, h00, hlim0⟩ := degreeOneLift_subsequence_ae sigma0
  obtain ⟨k1, L1, hk1, hL1, hP1, h10, hlim1⟩ :=
    degreeOneLift_subsequence_ae (fun j => sigma1 (k0 j))
  refine ⟨k0 ∘ k1, L0, L1, hk0.comp hk1, hL0, hL1, hP0, hP1, h00, h10, ?_, ?_⟩
  · filter_upwards [hlim0] with x hx
    have h := (hc0.tendsto (L0 x)).comp (hx.comp hk1.tendsto_atTop)
    have heq (j : ℕ) : c0 ((normalizedDegreeOneLift (sigma0 (k0 (k1 j)))).map x) =
        c0 ((sigma0 (k0 (k1 j))).map x) :=
      congrFun (normalizedDegreeOneLift_trace hp0 (sigma0 (k0 (k1 j)))) x
    simpa only [Function.comp_def, heq] using h
  · filter_upwards [hlim1] with x hx
    have h := (hc1.tendsto (L1 x)).comp hx
    have heq (j : ℕ) : c1 ((normalizedDegreeOneLift (sigma1 (k0 (k1 j)))).map x) =
        c1 ((sigma1 (k0 (k1 j))).map x) :=
      congrFun (normalizedDegreeOneLift_trace hp1 (sigma1 (k0 (k1 j)))) x
    simpa only [Function.comp_def, heq] using h

end PoincareConjecture.M64
