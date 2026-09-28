import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle BoundedContinuousFunction

noncomputable section

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace M60

def suAlphaPairMetric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) : (E × E) →L[ℝ] (E × E) →L[ℝ] ℝ :=
  B.bilinearComp (ContinuousLinearMap.fst ℝ E E) (ContinuousLinearMap.fst ℝ E E) +
    B.bilinearComp (ContinuousLinearMap.snd ℝ E E) (ContinuousLinearMap.snd ℝ E E)

theorem suAlphaPairMetric_coercive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hB : ∀ v, a * ‖v‖ ^ 2 ≤ B v v) (v : E × E) :
    a * ‖v‖ ^ 2 ≤ suAlphaPairMetric B v v := by
  change a * ‖v‖ ^ 2 ≤ B v.1 v.1 + B v.2 v.2
  have h1 := hB v.1
  have h2 := hB v.2
  rw [Prod.norm_def]
  rcases le_total ‖v.1‖ ‖v.2‖ with h | h
  · rw [max_eq_right h]
    linarith [mul_nonneg ha (sq_nonneg ‖v.1‖)]
  · rw [max_eq_left h]
    linarith [mul_nonneg ha (sq_nonneg ‖v.2‖)]

theorem suAlphaPairMetric_norm_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B A : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖suAlphaPairMetric B - suAlphaPairMetric A‖ ≤ 2 * ‖B - A‖ := by
  apply (suAlphaPairMetric B - suAlphaPairMetric A).opNorm_le_bound₂ (by positivity)
  intro v w
  have heq : (suAlphaPairMetric B - suAlphaPairMetric A) v w =
      (B - A) v.1 w.1 + (B - A) v.2 w.2 := by
    change (B v.1 w.1 + B v.2 w.2) - (A v.1 w.1 + A v.2 w.2) = _
    simp only [sub_apply]
    ring
  rw [heq]
  have h1 := ((B - A).le_opNorm₂ v.1 w.1).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (norm_fst_le v) (norm_nonneg (B - A)))
      (norm_fst_le w) (norm_nonneg w.1) (mul_nonneg (norm_nonneg (B - A)) (norm_nonneg v)))
  have h2 := ((B - A).le_opNorm₂ v.2 w.2).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (norm_snd_le v) (norm_nonneg (B - A)))
      (norm_snd_le w) (norm_nonneg w.2) (mul_nonneg (norm_nonneg (B - A)) (norm_nonneg v)))
  exact (norm_add_le _ _).trans (by linarith)

theorem suAlphaPairMetric_continuous {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Continuous (suAlphaPairMetric (E := E)) := by
  apply continuous_clm_apply.mpr
  intro v
  apply continuous_clm_apply.mpr
  intro w
  change Continuous (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v.1 w.1 + B v.2 w.2)
  exact ((continuous_id.clm_apply continuous_const).clm_apply continuous_const).add
    ((continuous_id.clm_apply continuous_const).clm_apply continuous_const)

theorem suAlphaPairMetric_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) : ‖suAlphaPairMetric B‖ ≤ 2 * ‖B‖ := by
  apply (suAlphaPairMetric B).opNorm_le_bound₂ (by positivity)
  intro v w
  change ‖B v.1 w.1 + B v.2 w.2‖ ≤ _
  have h1 := (B.le_opNorm₂ v.1 w.1).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (norm_fst_le v) (norm_nonneg B))
      (norm_fst_le w) (norm_nonneg w.1) (mul_nonneg (norm_nonneg B) (norm_nonneg v)))
  have h2 := (B.le_opNorm₂ v.2 w.2).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left (norm_snd_le v) (norm_nonneg B))
      (norm_snd_le w) (norm_nonneg w.2) (mul_nonneg (norm_nonneg B) (norm_nonneg v)))
  exact (norm_add_le _ _).trans (by linarith)

theorem suAlpha_midpoint_gap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v, 0 ≤ B v v)
    {c alpha : ℝ} (hc : 0 ≤ c) (ha : 1 ≤ alpha) (v w : E) :
    suRegularizedQuadratic B c alpha ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w) +
        (B (v - w) (v - w) / 4) ^ alpha ≤
      (suRegularizedQuadratic B c alpha v + suRegularizedQuadratic B c alpha w) / 2 := by
  let m := (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w
  have hid : c + B m m + B (v - w) (v - w) / 4 =
      (1 / 2 : ℝ) * (c + B v v) + (1 / 2 : ℝ) * (c + B w w) := by
    dsimp only [m]
    simp only [map_add, map_sub, map_smul, add_apply, sub_apply, smul_apply, smul_eq_mul]
    ring
  have hsplit := Real.add_rpow_le_rpow_add (add_nonneg hc (hB m))
    (div_nonneg (hB (v - w)) (by norm_num : 0 ≤ (4 : ℝ))) ha
  rw [hid] at hsplit
  have hconv := (convexOn_rpow ha).2 (add_nonneg hc (hB v))
    (add_nonneg hc (hB w)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  dsimp only [suRegularizedQuadratic]
  dsimp only [smul_eq_mul] at hconv
  exact hsplit.trans (by linarith)

theorem suAlpha_paired_blend_gap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v, 0 ≤ B v v)
    {c alpha t : ℝ} (hc : 0 ≤ c) (ha : 1 ≤ alpha)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) (v w : E) :
    suRegularizedQuadratic B c alpha ((1 - t) • v + t • w) +
        suRegularizedQuadratic B c alpha ((1 - t) • w + t • v) +
        4 * t * (B (v - w) (v - w) / 4) ^ alpha ≤
      suRegularizedQuadratic B c alpha v + suRegularizedQuadratic B c alpha w := by
  let m := (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w
  have hconv := suRegularizedQuadratic_convex B hB hc ha
  have hvm : (1 - 2 * t) • v + (2 * t) • m = (1 - t) • v + t • w := by
    dsimp only [m]
    module
  have hwm : (1 - 2 * t) • w + (2 * t) • m = (1 - t) • w + t • v := by
    dsimp only [m]
    module
  have h1 := hconv.2 (mem_univ v) (mem_univ m)
    (by linarith : 0 ≤ 1 - 2 * t) (by positivity : 0 ≤ 2 * t) (by ring)
  have h2 := hconv.2 (mem_univ w) (mem_univ m)
    (by linarith : 0 ≤ 1 - 2 * t) (by positivity : 0 ≤ 2 * t) (by ring)
  rw [hvm] at h1
  rw [hwm] at h2
  have hg := mul_le_mul_of_nonneg_left (suAlpha_midpoint_gap B hB hc ha v w)
    (show 0 ≤ 4 * t by positivity)
  dsimp only [smul_eq_mul] at h1 h2
  change _ + _ + _ ≤ _
  dsimp only [m] at h1 h2
  nlinarith

theorem suAlpha_scale_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v, 0 ≤ B v v)
    {c alpha t : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ alpha) (ht : 1 ≤ t) (v : E) :
    suRegularizedQuadratic B c alpha (t • v) ≤
      t ^ (2 * alpha) * suRegularizedQuadratic B c alpha v := by
  have ht0 : 0 ≤ t := by linarith
  have hquad : c + B (t • v) (t • v) ≤ t ^ 2 * (c + B v v) := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    nlinarith [mul_nonneg hc (show 0 ≤ t ^ 2 - 1 by nlinarith)]
  calc
    _ ≤ (t ^ 2 * (c + B v v)) ^ alpha :=
      Real.rpow_le_rpow (add_nonneg hc (hB _)) hquad ha
    _ = _ := by
      rw [Real.mul_rpow (sq_nonneg t) (add_nonneg hc (hB v)),
        ← Real.rpow_natCast, ← Real.rpow_mul ht0]
      rfl

theorem suAlpha_add_cutoff_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v, 0 ≤ B v v)
    {c alpha s : ℝ} (hc : 0 ≤ c) (ha : 1 ≤ alpha) (hs : 0 < s) (v w : E) :
    suRegularizedQuadratic B c alpha (v + w) ≤
      (1 + s) ^ (2 * alpha) * (suRegularizedQuadratic B c alpha v +
        s * suRegularizedQuadratic B c alpha (s⁻¹ • w)) := by
  have hsp : 0 < 1 + s := by linarith
  have heq : (1 + s) • ((1 / (1 + s)) • v +
      (s / (1 + s)) • (s⁻¹ • w)) = v + w := by
    simp only [smul_add, smul_smul]
    field_simp
    simp only [one_smul]
  have hcv := (suRegularizedQuadratic_convex B hB hc ha).2
    (mem_univ v) (mem_univ (s⁻¹ • w))
    (by positivity : 0 ≤ 1 / (1 + s)) (by positivity : 0 ≤ s / (1 + s))
    (by field_simp : 1 / (1 + s) + s / (1 + s) = 1)
  have hle1 : 1 / (1 + s) ≤ 1 := (div_le_one hsp).mpr (by linarith)
  have hles : s / (1 + s) ≤ s := by
    apply (div_le_iff₀ hsp).mpr
    nlinarith [sq_nonneg s]
  have hv0 : 0 ≤ suRegularizedQuadratic B c alpha v :=
    Real.rpow_nonneg (add_nonneg hc (hB v)) _
  have hw0 : 0 ≤ suRegularizedQuadratic B c alpha (s⁻¹ • w) :=
    Real.rpow_nonneg (add_nonneg hc (hB _)) _
  have hcv' : suRegularizedQuadratic B c alpha
      ((1 / (1 + s)) • v + (s / (1 + s)) • (s⁻¹ • w)) ≤
        suRegularizedQuadratic B c alpha v +
          s * suRegularizedQuadratic B c alpha (s⁻¹ • w) := by
    exact hcv.trans (add_le_add
      (by simpa only [smul_eq_mul, one_mul] using mul_le_mul_of_nonneg_right hle1 hv0)
      (mul_le_mul_of_nonneg_right hles hw0))
  rw [← heq]
  exact (suAlpha_scale_le B hB hc (by linarith) (by linarith) _).trans
    (mul_le_mul_of_nonneg_left hcv' (Real.rpow_nonneg hsp.le _))

theorem suAlpha_paired_replacement_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B A₁ A₂ C₁ C₂ : E →L[ℝ] E →L[ℝ] ℝ)
    {c alpha a d s t K : ℝ} (hc : 0 ≤ c) (ha : 1 ≤ alpha)
    (ha0 : 0 < a) (hd : 0 ≤ d) (hs : 0 < s) (ht : 0 ≤ t) (ht' : t ≤ 1 / 2)
    (hB : ∀ v, a * ‖v‖ ^ 2 ≤ B v v)
    (hA₁ : ∀ v, a * ‖v‖ ^ 2 ≤ A₁ v v)
    (hA₂ : ∀ v, a * ‖v‖ ^ 2 ≤ A₂ v v)
    (hC₁ : ∀ v, 0 ≤ C₁ v v) (hC₂ : ∀ v, 0 ≤ C₂ v v)
    (hdA₁ : ‖B - A₁‖ ≤ d) (hdA₂ : ‖B - A₂‖ ≤ d)
    (hdC₁ : ‖C₁ - B‖ ≤ d) (hdC₂ : ‖C₂ - B‖ ≤ d)
    (v w q : E) (hq : suRegularizedQuadratic B c alpha (s⁻¹ • q) ≤ K) :
    let T := (1 + d / a) ^ alpha
    let S := (1 + s) ^ (2 * alpha)
    suRegularizedQuadratic C₁ c alpha ((1 - t) • v + t • w + q) +
        suRegularizedQuadratic C₂ c alpha ((1 - t) • w + t • v - q) +
        T * S * (4 * t * (B (v - w) (v - w) / 4) ^ alpha) ≤
      T ^ 2 * S * (suRegularizedQuadratic A₁ c alpha v +
        suRegularizedQuadratic A₂ c alpha w) + 2 * T * S * s * K := by
  let T := (1 + d / a) ^ alpha
  let S := (1 + s) ^ (2 * alpha)
  have hT : 0 ≤ T := Real.rpow_nonneg (by positivity) _
  have hS : 0 ≤ S := Real.rpow_nonneg (by positivity) _
  have hBn (x : E) : 0 ≤ B x x := (mul_nonneg ha0.le (sq_nonneg _)).trans (hB x)
  have he1 := suAlpha_add_cutoff_error B hBn hc ha hs ((1 - t) • v + t • w) q
  have he2 := suAlpha_add_cutoff_error B hBn hc ha hs ((1 - t) • w + t • v) (-q)
  have hneg : suRegularizedQuadratic B c alpha (s⁻¹ • -q) =
      suRegularizedQuadratic B c alpha (s⁻¹ • q) := by
    simp only [smul_neg, suRegularizedQuadratic, map_neg, neg_apply, neg_neg]
  rw [hneg, ← sub_eq_add_neg] at he2
  have hc1 := suRegularizedQuadratic_metric_comparison C₁ B ha0 hdC₁ hc
    (show 0 ≤ alpha by linarith) hC₁ hB ((1 - t) • v + t • w + q)
  have hc2 := suRegularizedQuadratic_metric_comparison C₂ B ha0 hdC₂ hc
    (show 0 ≤ alpha by linarith) hC₂ hB ((1 - t) • w + t • v - q)
  have hh1 := hc1.trans (mul_le_mul_of_nonneg_left he1 hT)
  have hh2 := hc2.trans (mul_le_mul_of_nonneg_left he2 hT)
  have hg := mul_le_mul_of_nonneg_left (suAlpha_paired_blend_gap B hBn hc ha ht ht' v w)
    (mul_nonneg hT hS)
  have hbase1 := suRegularizedQuadratic_metric_comparison B A₁ ha0 hdA₁ hc
    (show 0 ≤ alpha by linarith) hBn hA₁ v
  have hbase2 := suRegularizedQuadratic_metric_comparison B A₂ ha0 hdA₂ hc
    (show 0 ≤ alpha by linarith) hBn hA₂ w
  have hbase := mul_le_mul_of_nonneg_left (add_le_add hbase1 hbase2) (mul_nonneg hT hS)
  have herr := mul_le_mul_of_nonneg_left hq (show 0 ≤ 2 * T * S * s by positivity)
  change _ ≤ _
  change _ ≤ T * (S * _) at hh1 hh2
  change _ ≤ T * S * (T * _ + T * _) at hbase
  nlinarith

theorem suAlpha_paired_weighted_power_gap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B A₁ A₂ C₁ C₂ : E →L[ℝ] E →L[ℝ] ℝ)
    {c alpha a d s t C D r L : ℝ} (hc : c ∈ Icc 0 1) (ha : 1 ≤ alpha)
    (ha0 : 0 < a) (hd : 0 ≤ d) (hs : 0 < s) (ht : t ∈ Icc 0 (1 / 2))
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hr : 1 ≤ r) (hL : r ≤ L)
    (hB : ∀ v, a * ‖v‖ ^ 2 ≤ B v v)
    (hA₁ : ∀ v, a * ‖v‖ ^ 2 ≤ A₁ v v)
    (hA₂ : ∀ v, a * ‖v‖ ^ 2 ≤ A₂ v v)
    (hC₁ : ∀ v, 0 ≤ C₁ v v) (hC₂ : ∀ v, 0 ≤ C₂ v v)
    (hdA₁ : ‖B - A₁‖ ≤ d) (hdA₂ : ‖B - A₂‖ ≤ d)
    (hdC₁ : ‖C₁ - B‖ ≤ d) (hdC₂ : ‖C₂ - B‖ ≤ d)
    (hBn : ‖B‖ ≤ C) (v w q : E) (hq : ‖q‖ ≤ s * D) :
    let T := (1 + d / a) ^ alpha
    let S := (1 + s) ^ (2 * alpha)
    r * suRegularizedQuadratic C₁ c alpha ((1 - t) • v + t • w + q) +
        r * suRegularizedQuadratic C₂ c alpha ((1 - t) • w + t • v - q) +
        (a / 4) ^ alpha * t * ‖v - w‖ ^ (2 * alpha) ≤
      T ^ 2 * S * (r * suRegularizedQuadratic A₁ c alpha v +
        r * suRegularizedQuadratic A₂ c alpha w) +
          2 * T * S * s * (1 + C * D ^ 2) ^ alpha * L := by
  let T := (1 + d / a) ^ alpha
  let S := (1 + s) ^ (2 * alpha)
  have hT : 1 ≤ T := Real.one_le_rpow
    (by have := div_nonneg hd ha0.le; linarith) (by linarith)
  have hS : 1 ≤ S := Real.one_le_rpow (by linarith) (by linarith)
  have hq' : ‖s⁻¹ • q‖ ≤ D := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
    calc
      _ ≤ s⁻¹ * (s * D) := mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr hs.le)
      _ = D := by rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  have hbq : B (s⁻¹ • q) (s⁻¹ • q) ≤ C * D ^ 2 := by
    calc
      _ ≤ ‖B (s⁻¹ • q) (s⁻¹ • q)‖ := le_abs_self _
      _ ≤ ‖B‖ * ‖s⁻¹ • q‖ * ‖s⁻¹ • q‖ := B.le_opNorm₂ _ _
      _ = ‖B‖ * ‖s⁻¹ • q‖ ^ 2 := by ring
      _ ≤ C * D ^ 2 := mul_le_mul hBn ((sq_le_sq₀ (norm_nonneg _) hD).mpr hq')
        (sq_nonneg _) hC
  have hqpow : suRegularizedQuadratic B c alpha (s⁻¹ • q) ≤ (1 + C * D ^ 2) ^ alpha :=
    Real.rpow_le_rpow (add_nonneg hc.1 ((mul_nonneg ha0.le (sq_nonneg _)).trans (hB _)))
      (by linarith [hc.2]) (by linarith)
  have hp : (a / 4) ^ alpha * ‖v - w‖ ^ (2 * alpha) ≤
      (B (v - w) (v - w) / 4) ^ alpha := by
    rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two,
      ← Real.mul_rpow (by positivity) (sq_nonneg _)]
    exact Real.rpow_le_rpow (by positivity) (by have := hB (v - w); nlinarith) (by linarith)
  have hTS : 1 ≤ T * S := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ T - 1) (by linarith : 0 ≤ S - 1)]
  have hfactor : 1 ≤ r * T * S * 4 := by
    have h := mul_le_mul_of_nonneg_right hr (by linarith : 0 ≤ T * S)
    nlinarith
  have hg : (a / 4) ^ alpha * t * ‖v - w‖ ^ (2 * alpha) ≤
      r * (T * S * (4 * t * (B (v - w) (v - w) / 4) ^ alpha)) := by
    have hn : 0 ≤ t * (B (v - w) (v - w) / 4) ^ alpha :=
      mul_nonneg ht.1 (Real.rpow_nonneg (by
        have := hB (v - w); have := mul_nonneg ha0.le (sq_nonneg ‖v - w‖); linarith) _)
    have h1 := mul_le_mul_of_nonneg_left hp ht.1
    have h2 := mul_le_mul_of_nonneg_right hfactor hn
    nlinarith
  have hbase := mul_le_mul_of_nonneg_left
    (suAlpha_paired_replacement_bound B A₁ A₂ C₁ C₂ hc.1 ha ha0 hd hs ht.1 ht.2
      hB hA₁ hA₂ hC₁ hC₂ hdA₁ hdA₂ hdC₁ hdC₂ v w q hqpow) (by linarith : 0 ≤ r)
  have herr := mul_le_mul_of_nonneg_right hL
    (show 0 ≤ 2 * T * S * s * (1 + C * D ^ 2) ^ alpha by positivity)
  change r * (_ + _ + T * S * _) ≤ r * (T ^ 2 * S * _ + _) at hbase
  change _ ≤ _
  nlinarith only [hbase, hg, herr]

open scoped ENNReal in

theorem suWeakLp_memLp_of_power_bound
    {X F : Type*} [MeasurableSpace X] {mu : Measure X}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p C : ℝ} (hp : 1 ≤ p) (hC : 0 ≤ C)
    {u : ℕ → Lp F 2 mu} {v : Lp F 2 mu}
    (hw : ∀ L : StrongDual ℝ (Lp F 2 mu),
      Tendsto (fun j => L (u j)) atTop (𝓝 (L v)))
    (hb : ∀ j, (∫⁻ x, ENNReal.ofReal (‖u j x‖ ^ p) ∂mu) ≤ ENNReal.ofReal C) :
    MemLp (fun x => v x) (ENNReal.ofReal p) mu ∧ (∫ x, ‖v x‖ ^ p ∂mu) ≤ C := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  have hp0 : 0 < p := by linarith
  have hcont : Continuous (fun a : F => ‖a‖ ^ p) :=
    (Real.continuous_rpow_const hp0.le).comp continuous_norm
  have hconv : ConvexOn ℝ univ (fun a : F => ‖a‖ ^ p) := by
    refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
    have hn : ‖s • a + t • b‖ ≤ s * ‖a‖ + t * ‖b‖ := by
      simpa only [norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
        using norm_add_le (s • a) (t • b)
    exact (Real.rpow_le_rpow (norm_nonneg _) hn hp0.le).trans
      ((convexOn_rpow hp).2 (norm_nonneg a) (norm_nonneg b) hs ht hst)
  have hbound : (∫⁻ x, ENNReal.ofReal (‖v x‖ ^ p) ∂mu) ≤ ENNReal.ofReal C :=
    suConvexIntegral_le_of_weak (fun (_ : X) (a : F) => ‖a‖ ^ p)
      (hcont.measurable.comp measurable_snd) (fun _ => hcont) (fun _ => hconv)
      hw (Eventually.of_forall hb)
  have hi : Integrable (fun x => ‖v x‖ ^ p) mu := by
    refine ⟨hcont.comp_aestronglyMeasurable (Lp.aestronglyMeasurable v), ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using
      hbound.trans_lt (ENNReal.ofReal_lt_top : ENNReal.ofReal C < ⊤)
  refine ⟨?_, ?_⟩
  · apply (integrable_norm_rpow_iff (Lp.aestronglyMeasurable v)
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hp0.le] using hi
  · apply (ENNReal.ofReal_le_ofReal_iff hC).mp
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg (v x)) _)]
    exact hbound

open scoped ENNReal in

theorem suStrongLp_of_subseq_weak_and_power_cauchy
    {X F : Type*} [MeasurableSpace X] {mu : Measure X}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ} (hp : 1 ≤ p) {u : ℕ → Lp F 2 mu} {v : Lp F 2 mu}
    {k : ℕ → ℕ} (hk : StrictMono k)
    (hw : ∀ L : StrongDual ℝ (Lp F 2 mu),
      Tendsto (fun j => L (u (k j))) atTop (𝓝 (L v)))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      (∫⁻ x, ENNReal.ofReal (‖(u j - u k) x‖ ^ p) ∂mu) ≤ ENNReal.ofReal ε) :
    Tendsto (fun j => eLpNorm (fun x => (u j - v) x) (ENNReal.ofReal p) mu)
      atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  let I : ℕ → ℝ≥0∞ := fun j => ∫⁻ x, ENNReal.ofReal (‖(u j - v) x‖ ^ p) ∂mu
  have hI : Tendsto I atTop (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    obtain ⟨r, hr0, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
    obtain ⟨N, hN⟩ := hcauchy r (ENNReal.ofReal_pos.mp hr)
    filter_upwards [eventually_ge_atTop N] with j hj
    have hweak (L : StrongDual ℝ (Lp F 2 mu)) :
        Tendsto (fun l => L (u j - u (k (l + N)))) atTop (𝓝 (L (u j - v))) := by
      simp only [map_sub]
      exact tendsto_const_nhds.sub ((hw L).comp (tendsto_add_atTop_nat N))
    obtain ⟨hmem, hbound⟩ := suWeakLp_memLp_of_power_bound hp hr0 hweak
      (fun l => hN j hj (k (l + N)) ((Nat.le_add_left _ _).trans (hk.id_le _)))
    have hint : Integrable (fun x => ‖(u j - v) x‖ ^ p) mu := by
      have h := (integrable_norm_rpow_iff hmem.1 (ENNReal.ofReal_pos.mpr hp0).ne'
        ENNReal.ofReal_ne_top).mpr hmem
      simpa only [ENNReal.toReal_ofReal hp0.le] using h
    change (∫⁻ x, ENNReal.ofReal (‖(u j - v) x‖ ^ p) ∂mu) ≤ ε
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg ((u j - v) x)) p)]
    exact (ENNReal.ofReal_le_ofReal hbound).trans hrε.le
  have hpow := hI.ennrpow_const (1 / p)
  have heq (j : ℕ) : eLpNorm (fun x => (u j - v) x) (ENNReal.ofReal p) mu = I j ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le]
    congr 1
    apply lintegral_congr
    intro x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
  simpa only [← heq, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)] using hpow

open scoped ENNReal in
theorem suStrongLp_of_weak_and_power_cauchy
    {X F : Type*} [MeasurableSpace X] {mu : Measure X}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ℝ} (hp : 1 ≤ p) {u : ℕ → Lp F 2 mu} {v : Lp F 2 mu}
    (hw : ∀ L : StrongDual ℝ (Lp F 2 mu),
      Tendsto (fun j => L (u j)) atTop (𝓝 (L v)))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      (∫⁻ x, ENNReal.ofReal (‖(u j - u k) x‖ ^ p) ∂mu) ≤ ENNReal.ofReal ε) :
    Tendsto (fun j => eLpNorm (fun x => (u j - v) x) (ENNReal.ofReal p) mu)
      atTop (𝓝 0) :=
  suStrongLp_of_subseq_weak_and_power_cauchy hp strictMono_id hw hcauchy

theorem suAlpha_pair_energy_gap
    (g : RiemannianMetric n M) (alpha : ℝ)
    (f₁ f₂ F₁ F₂ : UnitTwoSphere → M)
    (hf₁ : ContMDiff (𝓡 2) (𝓡 n) ∞ f₁) (hf₂ : ContMDiff (𝓡 2) (𝓡 n) ∞ f₂)
    (hF₁ : ContMDiff (𝓡 2) (𝓡 n) ∞ F₁) (hF₂ : ContMDiff (𝓡 2) (𝓡 n) ∞ F₂)
    (hn₁ : ¬ IsNullHomotopicSphere F₁) (hn₂ : ¬ IsNullHomotopicSphere F₂)
    (G : UnitTwoSphere → ℝ) (hG : Integrable G m60RoundSphereMetric.volumeMeasure)
    {Q r : ℝ}
    (hpoint : ∀ x, (1 + 2 * m60SphereIntrinsicEnergy g F₁ x) ^ alpha +
      (1 + 2 * m60SphereIntrinsicEnergy g F₂ x) ^ alpha + G x ≤
      Q * ((1 + 2 * m60SphereIntrinsicEnergy g f₁ x) ^ alpha +
        (1 + 2 * m60SphereIntrinsicEnergy g f₂ x) ^ alpha) + r) :
    (∫ x, G x ∂m60RoundSphereMetric.volumeMeasure) ≤
      Q * (m60SphereAlphaEnergy g alpha f₁ + m60SphereAlphaEnergy g alpha f₂) -
        2 * sInf (m60NonNullAlphaEnergyValues g alpha) + 4 * Real.pi * r := by
  have hfi₁ := m60SphereAlphaEnergy_integrable g alpha f₁ hf₁
  have hfi₂ := m60SphereAlphaEnergy_integrable g alpha f₂ hf₂
  have hFi₁ := m60SphereAlphaEnergy_integrable g alpha F₁ hF₁
  have hFi₂ := m60SphereAlphaEnergy_integrable g alpha F₂ hF₂
  have hi := integral_mono ((hFi₁.add hFi₂).add hG)
    (((hfi₁.add hfi₂).const_mul Q).add (integrable_const r)) hpoint
  have hleft := integral_add (hFi₁.add hFi₂) hG
  have hright := integral_add ((hfi₁.add hfi₂).const_mul Q) (integrable_const r)
  simp only [Pi.add_apply] at hi hleft hright
  rw [hleft, integral_add hFi₁ hFi₂, hright,
    integral_const_mul, integral_add hfi₁ hfi₂, integral_const,
    smul_eq_mul, m60RoundSphereMetric_volume_univ] at hi
  have hmin₁ := csInf_le (m60NonNullAlphaEnergyValues_bddBelow g alpha)
    (show m60SphereAlphaEnergy g alpha F₁ ∈ m60NonNullAlphaEnergyValues g alpha from
      ⟨F₁, hF₁, hn₁, rfl⟩)
  have hmin₂ := csInf_le (m60NonNullAlphaEnergyValues_bddBelow g alpha)
    (show m60SphereAlphaEnergy g alpha F₂ ∈ m60NonNullAlphaEnergyValues g alpha from
      ⟨F₂, hF₂, hn₂, rfl⟩)
  change m60SphereAlphaEnergy g alpha F₁ + m60SphereAlphaEnergy g alpha F₂ + _ ≤
    Q * (m60SphereAlphaEnergy g alpha f₁ + m60SphereAlphaEnergy g alpha f₂) +
      4 * Real.pi * r at hi
  linarith

end M60

end PoincareConjecture
