import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Modulus.ZeroAreaForward

/-! Pointwise limits retain the annular forward bound through interval
comparison, with no uniform derivative neighborhood in the approximation.
Source: MT Lemma 19.15, pp. 447-449; separation-evolution derivation. -/

set_option autoImplicit false
set_option warningAsError true

open Set Filter
open scoped Topology

namespace PoincareMT

/-- Integrated continuous forward comparisons pass to a pointwise limit on the stated time
domain. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project
derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64AnnulusForwardDerivativeBound.exponential_comparison_of_pointwise_limit
    {I : Type*} {l : Filter I} [NeBot l] {f : I → ℝ → ℝ} {g k : ℝ → ℝ}
    {a b s t K : ℝ}
    (hdata : ∀ᶠ i in l, ContinuousOn (f i) (Icc a b) ∧
      (∀ x ∈ Icc a b, 0 ≤ f i x) ∧
      ∀ x ∈ Ioo a b, AnnulusForwardDerivativeBound (f i) (k x * f i x) x)
    (hlimit : ∀ x ∈ Icc a b, Tendsto (fun i ↦ f i x) l (𝓝 (g x)))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hK : ∀ x ∈ Ioo s t, k x ≤ K) :
    g t ≤ Real.exp (K * (t - s)) * g s := by
  apply le_of_tendsto_of_tendsto (hlimit t ht)
    (tendsto_const_nhds.mul (hlimit s hs))
  filter_upwards [hdata] with i hi
  apply m64AnnulusForwardDerivativeBound.exponential_of_on_Ioo
    (hi.1.mono (Icc_subset_Icc hs.1 ht.2)) ?_ t ⟨hst, le_rfl⟩
  intro x hx eta heta
  have hxab : x ∈ Ioo a b := ⟨hs.1.trans_lt hx.1, hx.2.trans_le ht.2⟩
  filter_upwards [hi.2.2 x hxab eta heta] with h hh
  exact hh.trans (add_le_add
    (mul_le_mul_of_nonneg_right (hK x hx) (hi.2.1 x (Ioo_subset_Icc_self hxab))) le_rfl)

/-- Local exponential comparisons recover the exact continuous rate. Source: Morgan--Tian
(2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64AnnulusForwardDerivativeBound.of_exponential_comparisons
    {g k : ℝ → ℝ} {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hgt : 0 ≤ g t) (hk : ContinuousAt k t)
    (hcomparison : ∀ s z : ℝ, s ∈ Icc a b → z ∈ Icc a b → s ≤ z →
      ∀ K : ℝ, (∀ x ∈ Ioo s z, k x ≤ K) →
        g z ≤ Real.exp (K * (z - s)) * g s) :
    AnnulusForwardDerivativeBound g (k t * g t) t := by
  intro eta heta
  let epsilon := eta / (g t + 1)
  let K := k t + epsilon
  have hden : 0 < g t + 1 := by linarith
  have hepsilon : 0 < epsilon := div_pos heta hden
  have hprod : epsilon * (g t + 1) = eta := div_mul_cancel₀ eta hden.ne'
  have hgap : K * g t < k t * g t + eta := by dsimp only [K]; nlinarith
  have hrate : ∀ᶠ x in 𝓝[>] t, k x < K :=
    nhdsWithin_le_nhds (hk (Iio_mem_nhds (lt_add_of_pos_right _ hepsilon)))
  obtain ⟨c, hc, hkc⟩ :=
    (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset ht.2).mp hrate
  have hd : HasDerivAt (fun h : ℝ ↦ Real.exp (K * h) * g t) (K * g t) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul K).exp.mul_const (g t))
  have hquot : Tendsto (fun h : ℝ ↦ (Real.exp (K * h) * g t - g t) / h)
      (𝓝[>] 0) (𝓝 (K * g t)) := by
    simpa only [zero_add, mul_zero, Real.exp_zero, one_mul, smul_eq_mul,
      ← div_eq_inv_mul] using hd.tendsto_slope_zero_right
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo 0 (c - t) :=
    Ioo_mem_nhdsGT (sub_pos.mpr hc.1)
  filter_upwards [hsmall, hquot.eventually (Iio_mem_nhds hgap)] with h hh hq
  have hfuture : t + h ∈ Icc a b := by constructor <;> linarith [ht.1, hc.2, hh.1, hh.2]
  have hbound := hcomparison t (t + h) (Ioo_subset_Icc_self ht) hfuture
    (by linarith [hh.1]) K (fun x hx ↦ (hkc ⟨hx.1, by linarith [hx.2, hh.2]⟩).le)
  rw [add_sub_cancel_left] at hbound
  exact (div_le_div_of_nonneg_right (sub_le_sub_right hbound (g t)) hh.1.le).trans hq.le

/-- The annular forward estimate survives pointwise approximation because the comparison is
passed to the limit before recovering the derivative. Source: Morgan--Tian (2007), Lemma
19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64AnnulusForwardDerivativeBound.of_pointwise_limit
    {I : Type*} {l : Filter I} [NeBot l] {f : I → ℝ → ℝ} {g k : ℝ → ℝ}
    {a b : ℝ} (hg : ContinuousOn g (Icc a b)) (hk : ContinuousOn k (Icc a b))
    (hdata : ∀ᶠ i in l, ContinuousOn (f i) (Icc a b) ∧
      (∀ x ∈ Icc a b, 0 ≤ f i x) ∧
      ∀ x ∈ Ioo a b, AnnulusForwardDerivativeBound (f i) (k x * f i x) x)
    (hlimit : ∀ x ∈ Icc a b, Tendsto (fun i ↦ f i x) l (𝓝 (g x))) :
    ∀ t ∈ Ico a b, AnnulusForwardDerivativeBound g (k t * g t) t := by
  apply m64AnnulusForwardDerivativeBound.on_Ico_of_on_Ioo hg (hk.mul hg)
  intro t ht
  apply m64AnnulusForwardDerivativeBound.of_exponential_comparisons ht
    (le_of_tendsto_of_tendsto tendsto_const_nhds (hlimit t (Ioo_subset_Icc_self ht))
      (hdata.mono (fun _ hi ↦ hi.2.1 t (Ioo_subset_Icc_self ht))))
    (hk.continuousAt (Icc_mem_nhds ht.1 ht.2))
  intro s z hs hz hsz K hK
  exact m64AnnulusForwardDerivativeBound.exponential_comparison_of_pointwise_limit
    hdata hlimit hs hz hsz hK

end PoincareMT
