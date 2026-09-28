import PoincareConjecture.Proofs.M07.Topology.MetricSpace.Curves.CompactConvergence

open Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace Poincare.MetricCurves

variable {M : Type*} [MetricSpace M]

theorem exists_normalized_path
    {γ : ℝ → M} (hc : ContinuousOn γ (Icc 0 1))
    (hv : BoundedVariationOn γ (Icc 0 1)) :
    ∃ η : ℝ → M, η 0 = γ 0 ∧ η 1 = γ 1 ∧
      η '' Icc 0 1 = γ '' Icc 0 1 ∧
      LipschitzOnWith (eVariationOn γ (Icc 0 1)).toNNReal η (Icc 0 1) := by
  obtain ⟨η, h0, h1, himage, _, hlip⟩ :=
    exists_arcLength_representative (by norm_num : (0 : ℝ) ≤ 1) hc hv
  let L := (eVariationOn γ (Icc 0 1)).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hmul : MapsTo (fun t : ℝ => L * t) (Icc 0 1) (Icc 0 L) := by
    intro t ht
    exact ⟨mul_nonneg hL ht.1, by nlinarith [ht.2]⟩
  have hmul_image : (fun t : ℝ => L * t) '' Icc 0 1 = Icc 0 L := by
    simpa using (continuous_const.mul continuous_id).continuousOn.image_Icc_of_monotoneOn
      (by norm_num : (0 : ℝ) ≤ 1)
      (show MonotoneOn (fun t : ℝ => L * t) (Icc 0 1) from
        fun _ _ _ _ h => mul_le_mul_of_nonneg_left h hL)
  refine ⟨fun t => η (L * t), by simpa using h0, by simpa using h1, ?_, ?_⟩
  · change (η ∘ fun t => L * t) '' Icc 0 1 = _
    rw [image_comp, hmul_image]
    exact himage
  · apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    have h := hlip.dist_le_mul (L * s) (hmul hs) (L * t) (hmul ht)
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, ← mul_sub, abs_mul,
      abs_of_nonneg hL, ENNReal.coe_toNNReal_eq_toReal] using h

theorem eVariationOn_le_of_tendsto_bounds
    {σ : ℕ → ℝ → M} {γ : ℝ → M} {d : ℝ≥0∞} {l : ℕ → ℝ≥0∞}
    (hconv : TendstoUniformlyOn σ γ atTop (Icc 0 1))
    (hbound : ∀ n, eVariationOn (σ n) (Icc 0 1) ≤ l n)
    (hlength : Tendsto l atTop (𝓝 d)) : eVariationOn γ (Icc 0 1) ≤ d := by
  apply le_of_forall_lt_imp_le_of_dense
  intro v hv
  exact ge_of_tendsto hlength
    ((eVariationOn.lowerSemicontinuous_aux (fun _ ht => hconv.tendsto_at ht) hv).mono
      fun n hn => hn.le.trans (hbound n))

theorem eVariationOn_le_of_lipschitzOnWith
    {γ : ℝ → M} {C : ℝ≥0} (h : LipschitzOnWith C γ (Icc 0 1)) :
    eVariationOn γ (Icc 0 1) ≤ C := by
  have hcomp := h.comp_eVariationOn_le (mapsTo_id (Icc (0 : ℝ) 1))
  have hid : eVariationOn (id : ℝ → ℝ) (Icc 0 1) ≤ 1 := by
    simpa using (monotoneOn_id (s := Icc (0 : ℝ) 1)).eVariationOn_le
      (by norm_num : (0 : ℝ) ∈ Icc 0 1) (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  simpa only [Function.comp_id, mul_one] using hcomp.trans (mul_le_mul_right hid C)

theorem exists_compact_metric_minimizer
    {z y : M} {K : Set M} (hK : IsCompact K)
    {σ : ℕ → ℝ → M} {l : ℕ → ℝ≥0∞}
    (hc : ∀ n, ContinuousOn (σ n) (Icc 0 1))
    (hstart : ∀ n, σ n 0 = z) (hfinish : ∀ n, σ n 1 = y)
    (hconf : ∀ n, MapsTo (σ n) (Icc 0 1) K)
    (hbound : ∀ n, eVariationOn (σ n) (Icc 0 1) ≤ l n)
    (hlength : Tendsto l atTop (𝓝 (edist z y))) :
    ∃ η : ℝ → M,
      η 0 = z ∧ η (dist z y) = y ∧ MapsTo η (Icc 0 (dist z y)) K ∧
      HasUnitSpeedOn η (Icc 0 (dist z y)) ∧
      (∀ s ∈ Icc 0 (dist z y), ∀ t ∈ Icc 0 (dist z y),
        dist (η s) (η t) = |s - t|) := by
  have hd : edist z y ≠ ⊤ := edist_ne_top z y
  let B : ℝ≥0 := (edist z y).toNNReal + 1
  have hdB : edist z y < (B : ℝ≥0∞) := by
    rw [← ENNReal.coe_toNNReal hd]
    exact_mod_cast (lt_add_one (edist z y).toNNReal)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlength.eventually_lt_const hdB)
  have hfinite : ∀ n, l (N + n) ≠ ⊤ := fun n =>
    ne_top_of_lt (hN (N + n) (Nat.le_add_right N n))
  have hv : ∀ n, BoundedVariationOn (σ (N + n)) (Icc 0 1) := fun n =>
    ne_top_of_le_ne_top (hfinite n) (hbound (N + n))
  choose τ hτ0 hτ1 hτimage hτlip using
    (fun n => exists_normalized_path (hc (N + n)) (hv n))
  have hτconf : ∀ n, MapsTo (τ n) (Icc 0 1) K := by
    intro n t ht
    rcases (hτimage n).subset (mem_image_of_mem (τ n) ht) with ⟨s, hs, heq⟩
    exact heq ▸ hconf (N + n) hs
  have hcommon : ∀ n, LipschitzOnWith B (τ n) (Icc 0 1) := by
    intro n
    apply (hτlip n).weaken
    have h := ENNReal.toNNReal_mono ENNReal.coe_ne_top
      ((hbound (N + n)).trans (hN (N + n) (Nat.le_add_right N n)).le)
    simpa using h
  obtain ⟨φ, γ, hφ, hconv, hγlip, hγ0, hγ1, hγK⟩ :=
    exists_confined_uniform_limit hK hcommon
      (fun n => (hτ0 n).trans (hstart (N + n)))
      (fun n => (hτ1 n).trans (hfinish (N + n))) hτconf
  have hshift : StrictMono (fun n : ℕ => N + n) := fun _ _ h => Nat.add_lt_add_left h N
  have hvar : eVariationOn γ (Icc 0 1) ≤ edist z y :=
    eVariationOn_le_of_tendsto_bounds hconv
      (fun n => (eVariationOn_le_of_lipschitzOnWith (hτlip (φ n))).trans
        (ENNReal.coe_toNNReal_le_self.trans (hbound (N + φ n))))
      (hlength.comp (hshift.comp hφ).tendsto_atTop)
  have hmin : eVariationOn γ (Icc 0 1) = edist (γ 0) (γ 1) := by
    apply le_antisymm
    · simpa only [hγ0, hγ1] using hvar
    · exact eVariationOn.edist_le γ (by norm_num) (by norm_num)
  obtain ⟨η, hη0, hη1, hηimage, hunit, hdist⟩ :=
    exists_isometric_arcLength_representative (by norm_num : (0 : ℝ) ≤ 1)
      hγlip.continuousOn hmin
  simp only [hγ0, hγ1] at hη0 hη1 hηimage hunit hdist
  refine ⟨η, hη0, hη1, ?_, hunit, hdist⟩
  intro t ht
  rcases hηimage.subset (mem_image_of_mem η ht) with ⟨s, hs, heq⟩
  exact heq ▸ hγK hs

theorem exists_compact_metric_segment
    {z y : M} {K : Set M} (hK : IsCompact K)
    {σ : ℕ → ℝ → M} {l : ℕ → ℝ≥0∞}
    (hc : ∀ n, ContinuousOn (σ n) (Icc 0 1))
    (hstart : ∀ n, σ n 0 = z) (hfinish : ∀ n, σ n 1 = y)
    (hconf : ∀ n, MapsTo (σ n) (Icc 0 1) K)
    (hbound : ∀ n, eVariationOn (σ n) (Icc 0 1) ≤ l n)
    (hlength : Tendsto l atTop (𝓝 (edist z y))) :
    ∃ η : ℝ → M,
      η 0 = z ∧ η 1 = y ∧ MapsTo η (Icc 0 1) K ∧
      (∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
        dist (η s) (η t) = |s - t| * dist z y) := by
  obtain ⟨γ, h0, h1, hKγ, _, hdist⟩ :=
    exists_compact_metric_minimizer hK hc hstart hfinish hconf hbound hlength
  let L := dist z y
  refine ⟨fun t => γ (L * t), by simpa [h0], by simpa [h1], ?_, ?_⟩
  · intro t ht
    apply hKγ
    exact ⟨mul_nonneg dist_nonneg ht.1,
      by simpa [L] using mul_le_mul_of_nonneg_left ht.2 dist_nonneg⟩
  · intro s hs t ht
    have h := hdist (L * s) (by exact ⟨mul_nonneg dist_nonneg hs.1,
      by simpa [L] using mul_le_mul_of_nonneg_left hs.2 dist_nonneg⟩)
      (L * t) (by exact ⟨mul_nonneg dist_nonneg ht.1,
        by simpa [L] using mul_le_mul_of_nonneg_left ht.2 dist_nonneg⟩)
    rw [show |L * s - L * t| = L * |s - t| by
      rw [← mul_sub, abs_mul, abs_of_nonneg dist_nonneg]] at h
    simpa only [mul_comm] using h

end Poincare.MetricCurves
