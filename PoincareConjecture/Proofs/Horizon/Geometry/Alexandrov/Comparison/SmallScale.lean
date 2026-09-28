import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.ComparisonAngle
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent










set_option autoImplicit false

open Filter Topology

namespace Poincare.Alexandrov

private theorem tendsto_sinh_mul_div
    {ι : Type*} {l : Filter ι} {t a : ι → ℝ} {a₀ : ℝ}
    (ht : Tendsto t l (𝓝 0)) (htne : ∀ᶠ j in l, t j ≠ 0)
    (ha : Tendsto a l (𝓝 a₀)) :
    Tendsto (fun j => Real.sinh (t j * a j) / t j) l (𝓝 a₀) := by
  have hprod : Tendsto (fun j => t j * a j) l (𝓝 0) := by
    simpa only [zero_mul] using ht.mul ha
  have heq := (Real.isEquivalent_sinh.comp_tendsto hprod).div
    (Asymptotics.IsEquivalent.refl (u := t) (l := l))
  apply heq.symm.tendsto_nhds
  apply ha.congr'
  filter_upwards [htne] with j hj
  simp only [Pi.div_apply, Function.comp_apply, id_eq, mul_div_cancel_left₀ _ hj]

private theorem cosh_sub_one_eq_two_mul_sinh_half_sq (x : ℝ) :
    Real.cosh x - 1 = 2 * Real.sinh (x / 2) ^ 2 := by
  have hdouble := Real.cosh_two_mul (x / 2)
  rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at hdouble
  nlinarith only [hdouble, Real.cosh_sq_sub_sinh_sq (x / 2)]

private theorem tendsto_cosh_mul_sub_one_div_sq
    {ι : Type*} {l : Filter ι} {t a : ι → ℝ} {a₀ : ℝ}
    (ht : Tendsto t l (𝓝 0)) (htne : ∀ᶠ j in l, t j ≠ 0)
    (ha : Tendsto a l (𝓝 a₀)) :
    Tendsto (fun j => (Real.cosh (t j * a j) - 1) / t j ^ 2) l
      (𝓝 (a₀ ^ 2 / 2)) := by
  have h := (tendsto_sinh_mul_div ht htne (ha.div_const 2)).pow 2
  have htwo := h.const_mul 2
  convert htwo using 1
  · ext j
    rw [cosh_sub_one_eq_two_mul_sinh_half_sq]
    rw [show t j * a j / 2 = t j * (a j / 2) by ring]
    ring
  · congr 1
    ring



theorem tendsto_comparisonAngle_mul_of_tendsto_zero
    {ι : Type*} {l : Filter ι} {t a b d : ι → ℝ} {a₀ b₀ d₀ : ℝ}
    (ht : Tendsto t l (𝓝 0)) (htne : ∀ᶠ j in l, t j ≠ 0)
    (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀))
    (hd : Tendsto d l (𝓝 d₀)) (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) :
    Tendsto (fun j => comparisonAngle (t j * a j) (t j * b j) (t j * d j)) l
      (𝓝 (Real.arccos ((a₀ ^ 2 + b₀ ^ 2 - d₀ ^ 2) / (2 * a₀ * b₀)))) := by
  have hsina := tendsto_sinh_mul_div ht htne ha
  have hsinb := tendsto_sinh_mul_div ht htne hb
  have hca := tendsto_cosh_mul_sub_one_div_sq ht htne ha
  have hcb := tendsto_cosh_mul_sub_one_div_sq ht htne hb
  have hcd := tendsto_cosh_mul_sub_one_div_sq ht htne hd
  have hcosb : Tendsto (fun j => Real.cosh (t j * b j)) l (𝓝 1) := by
    simpa only [zero_mul, Real.cosh_zero, Function.comp_def] using
      Real.continuous_cosh.continuousAt.tendsto.comp (ht.mul hb)
  have hquot := (((hca.mul hcosb).add hcb).sub hcd).div (hsina.mul hsinb)
    (mul_ne_zero ha₀.ne' hb₀.ne')
  have hratio : Tendsto (fun j =>
      (Real.cosh (t j * a j) * Real.cosh (t j * b j) - Real.cosh (t j * d j)) /
        (Real.sinh (t j * a j) * Real.sinh (t j * b j))) l
      (𝓝 ((a₀ ^ 2 + b₀ ^ 2 - d₀ ^ 2) / (2 * a₀ * b₀))) := by
    have heq : (fun j =>
        (((Real.cosh (t j * a j) - 1) / t j ^ 2) * Real.cosh (t j * b j) +
          (Real.cosh (t j * b j) - 1) / t j ^ 2 -
          (Real.cosh (t j * d j) - 1) / t j ^ 2) /
            ((Real.sinh (t j * a j) / t j) * (Real.sinh (t j * b j) / t j))) =ᶠ[l]
        (fun j =>
          (Real.cosh (t j * a j) * Real.cosh (t j * b j) - Real.cosh (t j * d j)) /
            (Real.sinh (t j * a j) * Real.sinh (t j * b j))) := by
      filter_upwards [htne] with j hj
      field_simp
      ring
    convert hquot.congr' heq using 1
    congr 1
    ring
  exact Real.continuous_arccos.continuousAt.tendsto.comp hratio


theorem tendsto_comparisonAngle_mul_zero_right
    {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun t : ℝ => comparisonAngle (t * a) (t * b) (t * d)) (𝓝[>] 0)
      (𝓝 (Real.arccos ((a ^ 2 + b ^ 2 - d ^ 2) / (2 * a * b)))) := by
  apply tendsto_comparisonAngle_mul_of_tendsto_zero
    (tendsto_id.mono_left nhdsWithin_le_nhds) ?_
    tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds ha hb
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact ne_of_gt ht



theorem exists_pos_comparisonAngle_gt_of_euclidean_angle_ge
    {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ < θ') (hθ'pi : θ' < Real.pi) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R d : ℝ, 0 < R → R < R₀ →
      0 ≤ d → d ≤ 2 * R →
      θ' ≤ Real.arccos ((2 * R ^ 2 - d ^ 2) / (2 * R ^ 2)) →
      θ < comparisonAngle R R d := by
  let D := Real.sqrt (2 - 2 * Real.cos θ')
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hDsq : D ^ 2 = 2 - 2 * Real.cos θ' :=
    Real.sq_sqrt (by linarith [Real.cos_le_one θ'])
  have htheta : Real.arccos ((1 ^ 2 + 1 ^ 2 - D ^ 2) / (2 * 1 * 1)) = θ' := by
    rw [hDsq]
    convert Real.arccos_cos (hθ.trans hθθ').le hθ'pi.le using 1
    congr 1
    ring
  have hlimit := tendsto_comparisonAngle_mul_zero_right (d := D) zero_lt_one zero_lt_one
  rw [htheta] at hlimit
  simp only [mul_one] at hlimit
  obtain ⟨R₀, hR₀, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hlimit.eventually_const_lt hθθ')
  refine ⟨R₀, hR₀, ?_⟩
  intro R d hR hRR₀ hd hdR hangle
  have hden : 0 < 2 * R ^ 2 := by positivity
  have hratio_lower : -1 ≤ (2 * R ^ 2 - d ^ 2) / (2 * R ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hd, hdR, hR]
  have hratio_upper : (2 * R ^ 2 - d ^ 2) / (2 * R ^ 2) ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [sq_nonneg d]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (hθ.trans hθθ').le
    (Real.arccos_le_pi _) hangle
  rw [Real.cos_arccos hratio_lower hratio_upper] at hcos
  have hsqbound := (div_le_iff₀ hden).mp hcos
  have hchord : R * D ≤ d := by
    have hscaled := congrArg (fun x : ℝ => R ^ 2 * x) hDsq
    nlinarith only [hsqbound, hscaled, hd, mul_nonneg hR.le hD]
  have hcosh : Real.cosh (R * D) ≤ Real.cosh d := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg (mul_nonneg hR.le hD), abs_of_nonneg hd] using hchord
  have hmono : comparisonAngle R R (R * D) ≤ comparisonAngle R R d := by
    unfold comparisonAngle
    apply Real.arccos_le_arccos
    exact div_le_div_of_nonneg_right (sub_le_sub_left hcosh _)
      (mul_nonneg (Real.sinh_pos_iff.mpr hR).le (Real.sinh_pos_iff.mpr hR).le)
  exact (hsmall ⟨hR, hRR₀⟩).trans_le hmono

end Poincare.Alexandrov
