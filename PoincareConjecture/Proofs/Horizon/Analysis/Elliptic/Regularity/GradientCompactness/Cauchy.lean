import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.LocalL2








noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal BigOperators
open Poincare.Analysis.Sobolev.Weak

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)



theorem cauchySeq_lipschitzPartialL2_of_weak_divergence
    {O U : Set E} (hO : IsOpen O) (hU : IsOpen U) (hUO : U ⊆ O)
    [IsFiniteMeasure (volume.restrict O)] [IsFiniteMeasure (volume.restrict U)]
    {u : ℕ → E → ℝ} {F : ℕ → Fin d → E → ℝ} {f : ℕ → E → ℝ}
    {A : ℕ → E → Fin d → Fin d → ℝ} {L : ℝ≥0} {c C D : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hu : ∀ k, LipschitzOnWith L (u k) O)
    (huc : UniformCauchySeqOn u atTop O) (hAc : UniformCauchySeqOn A atTop O)
    (hF : ∀ k i, MemLp (F k i) 2 (volume.restrict O))
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict O))
    (hfC : ∀ k x, x ∈ O → |f k x| ≤ C)
    (hFC : ∀ k i x, x ∈ O → |F k i x| ≤ C)
    (hell : ∀ k x, x ∈ O → ∀ w : Fin d → ℝ,
      c * ∑ i, (w i) ^ 2 ≤ ∑ i, ∑ j, A k x i j * w j * w i)
    (hFid : ∀ k x, x ∈ O → ∀ i, F k i x =
      -(∑ j, A k x i j * fderiv ℝ (u k) x (EuclideanSpace.single j 1)))
    (hle : ∀ k (ψ : E → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ O → (∀ x, 0 ≤ ψ x) →
      (∫ x in O, ∑ i, F k i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) ≤
        ∫ x in O, f k x * ψ x)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (hφU : ∀ x ∈ U, φ x = 1)
    (hdφ : ∀ i x, x ∈ O → |fderiv ℝ φ x (EuclideanSpace.single i 1)| ≤ D)
    (i : Fin d) :
    CauchySeq (fun k => lipschitzPartialL2 hU ((hu k).mono hUO) i) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let B := (4 * C * (1 + (d : ℝ) * D) + (d : ℝ) ^ 2 * (2 * (L : ℝ) ^ 2)) *
    volume.real O
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let η := c * ε ^ 2 / (B + 1)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηeq : η * (B + 1) = c * ε ^ 2 :=
    div_mul_cancel₀ _ (by positivity : B + 1 ≠ 0)
  have hsmall : η * B < c * ε ^ 2 := by nlinarith
  obtain ⟨Nu, hNu⟩ := Metric.uniformCauchySeqOn_iff.mp huc η hη
  obtain ⟨NA, hNA⟩ := Metric.uniformCauchySeqOn_iff.mp hAc η hη
  refine ⟨max Nu NA, fun m hm n hn => ?_⟩
  have hmU : Nu ≤ m := le_trans (le_max_left _ _) hm
  have hnU : Nu ≤ n := le_trans (le_max_left _ _) hn
  have hmA : NA ≤ m := le_trans (le_max_right _ _) hm
  have hnA : NA ≤ n := le_trans (le_max_right _ _) hn
  have herr : ∀ x ∈ O, |u m x - u n x| ≤ (⟨η, hη.le⟩ : ℝ≥0) := by
    intro x hx
    exact (Real.dist_eq _ _ ▸ hNu m hmU n hnU x hx).le
  have hcoeff : ∀ x ∈ O, ∀ j k, |A m x j k - A n x j k| ≤ η := by
    intro x hx j k
    rw [← Real.dist_eq]
    exact ((dist_le_pi_dist (A m x j) (A n x j) k).trans
      (dist_le_pi_dist (A m x) (A n x) j)).trans (hNA m hmA n hnA x hx).le
  have hp : MemLp φ ∞ (volume.restrict O) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict O
  have henergy := integral_partial_sq_le_flux_energy hO (hF m) (hF n) (hu m) (hu n)
    hp (fun x _ => hφ0 x) (fun x _ => hφ1 x) hη.le hcoeff (hell m) (hFid m) (hFid n)
  have hflux := weak_flux_comparison_energy_le_of_bound hO (hF m) (hF n) (hf m) (hf n)
    (hle m) (hle n) (hu m) (hu n) herr hφ hφc hφO hφ0 hφ1 hC hD
    (hfC m) (hfC n) (hFC m) (hFC n) hdφ
  let q := fun x => φ x * ∑ j,
    (fderiv ℝ (u m) x (EuclideanSpace.single j 1) -
      fderiv ℝ (u n) x (EuclideanSpace.single j 1)) ^ 2
  have hq : MemLp q ∞ (volume.restrict O) := by
    have hsum : MemLp (fun x => ∑ j,
        (fderiv ℝ (u m) x (EuclideanSpace.single j 1) -
          fderiv ℝ (u n) x (EuclideanSpace.single j 1)) ^ 2) ∞ (volume.restrict O) := by
      apply memLp_finsetSum
      intro j _
      have hd := (memLp_top_fderiv_apply_of_lipschitzOn hO (hu m)
        (EuclideanSpace.single j 1)).sub
        (memLp_top_fderiv_apply_of_lipschitzOn hO (hu n) (EuclideanSpace.single j 1))
      simpa only [pow_two, Pi.sub_apply] using hd.mul' (r := ∞) hd
    exact hsum.mul' hp
  have hnorm : ‖lipschitzPartialL2 hU ((hu m).mono hUO) i -
      lipschitzPartialL2 hU ((hu n).mono hUO) i‖ ^ 2 ≤ ∫ x in O, q x := by
    apply norm_toLp_sub_sq_le_integral hU.measurableSet hO.measurableSet hUO
      _ _ (hq.integrable le_top)
    · intro x _
      exact mul_nonneg (hφ0 x) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    · intro x hx
      dsimp only [q]
      rw [hφU x hx, one_mul]
      exact Finset.single_le_sum (f := fun j =>
        (fderiv ℝ (u m) x (EuclideanSpace.single j 1) -
          fderiv ℝ (u n) x (EuclideanSpace.single j 1)) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hsq : c * ‖lipschitzPartialL2 hU ((hu m).mono hUO) i -
      lipschitzPartialL2 hU ((hu n).mono hUO) i‖ ^ 2 ≤ η * B := by
    have hmul := mul_le_mul_of_nonneg_left hnorm hc.le
    change c * (∫ x in O, q x) ≤ _ at henergy
    have he := henergy.trans (add_le_add hflux le_rfl)
    change c * (∫ x in O, q x) ≤ 4 * η * C * (1 + (d : ℝ) * D) * volume.real O +
      (d : ℝ) ^ 2 * η * (2 * (L : ℝ) ^ 2) * volume.real O at he
    have halg : 4 * η * C * (1 + (d : ℝ) * D) * volume.real O +
        (d : ℝ) ^ 2 * η * (2 * (L : ℝ) ^ 2) * volume.real O = η * B := by
      dsimp only [B]
      ring
    rw [halg] at he
    exact hmul.trans he
  rw [dist_eq_norm]
  have hsq' := hsq.trans_lt hsmall
  have hsq'' := (mul_lt_mul_iff_right₀ hc).mp hsq'
  nlinarith only [hsq'', hε, norm_nonneg (lipschitzPartialL2 hU ((hu m).mono hUO) i -
    lipschitzPartialL2 hU ((hu n).mono hUO) i)]

end Poincare.Analysis.Elliptic
