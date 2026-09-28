import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.FluxComparison







noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal BigOperators

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}



theorem abs_partial_le_of_lipschitzOn
    {O : Set (EuclideanSpace ℝ (Fin d))} (hO : IsOpen O)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u O) {x} (hx : x ∈ O) (i : Fin d) :
    |fderiv ℝ u x (EuclideanSpace.single i 1)| ≤ L := by
  have h := (fderiv ℝ u x).le_opNorm (EuclideanSpace.single i 1)
  simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs] at h
  exact h.trans (norm_fderiv_le_of_lipschitzOn ℝ (hO.mem_nhds hx) hu)



theorem matrix_flux_coercivity
    {A B : Fin d → Fin d → ℝ} {a b : Fin d → ℝ} {c L δ : ℝ}
    (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hell : ∀ w : Fin d → ℝ,
      c * ∑ i, (w i) ^ 2 ≤ ∑ i, ∑ j, A i j * w j * w i)
    (ha : ∀ i, |a i| ≤ L) (hb : ∀ i, |b i| ≤ L)
    (hAB : ∀ i j, |A i j - B i j| ≤ δ) :
    c * ∑ i, (a i - b i) ^ 2 ≤
      (∑ i, ((∑ j, A i j * a j) - ∑ j, B i j * b j) * (a i - b i)) +
        (d : ℝ) ^ 2 * δ * (2 * L ^ 2) := by
  have hdiff (i) : |a i - b i| ≤ 2 * L :=
    (abs_sub (a i) (b i)).trans (by linarith [ha i, hb i])
  have hterm (i j) : -((A i j - B i j) * b j * (a i - b i)) ≤
      δ * (2 * L ^ 2) := by
    calc
      _ ≤ |(A i j - B i j) * b j * (a i - b i)| := neg_le_abs _
      _ = |A i j - B i j| * |b j| * |a i - b i| := by simp only [abs_mul]
      _ ≤ δ * L * (2 * L) :=
        mul_le_mul (mul_le_mul (hAB i j) (hb j) (abs_nonneg _) hδ)
          (hdiff i) (abs_nonneg _) (mul_nonneg hδ hL)
      _ = δ * (2 * L ^ 2) := by ring
  have hsum : -(∑ i, ∑ j, (A i j - B i j) * b j * (a i - b i)) ≤
      (d : ℝ) ^ 2 * δ * (2 * L ^ 2) := by
    calc
      _ = ∑ i, ∑ j, -((A i j - B i j) * b j * (a i - b i)) := by
        simp only [Finset.sum_neg_distrib]
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, δ * (2 * L ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = _ := by simp; ring
  have hid :
      (∑ i, ((∑ j, A i j * a j) - ∑ j, B i j * b j) * (a i - b i)) =
      (∑ i, ∑ j, A i j * (a j - b j) * (a i - b i)) +
      ∑ i, ∑ j, (A i j - B i j) * b j * (a i - b i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h := hell (fun i => a i - b i)
  linarith



theorem flux_comparison_remainder_le
    {F G p : Fin d → ℝ} {f g φ w z ε C D : ℝ}
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hf : |f| ≤ C) (hg : |g| ≤ C)
    (hF : ∀ i, |F i| ≤ C) (hG : ∀ i, |G i| ≤ C)
    (hp : ∀ i, |p i| ≤ D) (hφ : |φ| ≤ 1)
    (hw : |w| ≤ 2 * ε) (hz : |z| ≤ 2 * ε) :
    f * (φ * w) + g * (φ * z) - ∑ i, (w * F i + z * G i) * p i ≤
      4 * ε * C * (1 + (d : ℝ) * D) := by
  have hfirst : f * (φ * w) ≤ 2 * ε * C := by
    calc
      _ ≤ |f * (φ * w)| := le_abs_self _
      _ = |f| * (|φ| * |w|) := by simp only [abs_mul]
      _ ≤ C * (1 * (2 * ε)) := by gcongr
      _ = _ := by ring
  have hsecond : g * (φ * z) ≤ 2 * ε * C := by
    calc
      _ ≤ |g * (φ * z)| := le_abs_self _
      _ = |g| * (|φ| * |z|) := by simp only [abs_mul]
      _ ≤ C * (1 * (2 * ε)) := by gcongr
      _ = _ := by ring
  have hterm (i) : -((w * F i + z * G i) * p i) ≤ 4 * ε * C * D := by
    calc
      _ ≤ |(w * F i + z * G i) * p i| := neg_le_abs _
      _ = |w * F i + z * G i| * |p i| := abs_mul _ _
      _ ≤ (|w * F i| + |z * G i|) * |p i| :=
        mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)
      _ = (|w| * |F i| + |z| * |G i|) * |p i| := by simp only [abs_mul]
      _ ≤ ((2 * ε) * C + (2 * ε) * C) * D := by
        gcongr
        · exact hF i
        · exact hG i
        · exact hp i
      _ = _ := by ring
  have hsum : -(∑ i, (w * F i + z * G i) * p i) ≤
      (d : ℝ) * (4 * ε * C * D) := by
    calc
      _ = ∑ i, -((w * F i + z * G i) * p i) := by
        rw [Finset.sum_neg_distrib]
      _ ≤ ∑ _i : Fin d, 4 * ε * C * D := Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by simp
  nlinarith

end Poincare.Analysis.Elliptic
