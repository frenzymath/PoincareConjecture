import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusForwardEndpoint
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture

theorem m64AnnulusForwardDerivativeBound.max_positive
    {f : ℝ → ℝ} {t K epsilon : ℝ} (hepsilon : 0 < epsilon) (hK : 0 ≤ K)
    (hf : ContinuousAt f t)
    (hforward : 0 < f t → AnnulusForwardDerivativeBound f (K * f t) t) :
    AnnulusForwardDerivativeBound (fun x => max (f x) epsilon)
      (K * max (f t) epsilon) t := by
  by_cases hft : 0 < f t
  · intro eta heta
    filter_upwards [hforward hft eta heta, self_mem_nhdsWithin] with h hh hpos
    have hpos : 0 < h := hpos
    have hmax : 0 ≤ K * max (f t) epsilon :=
      mul_nonneg hK (hepsilon.le.trans (le_max_right _ _))
    have hmul : 0 ≤ (K * max (f t) epsilon + eta) * h :=
      mul_nonneg (by linarith) hpos.le
    have hcoefficient : K * f t ≤ K * max (f t) epsilon :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hK
    have hstep := (div_le_iff₀ hpos).mp hh
    have hfbound : f (t + h) ≤ max (f t) epsilon +
        (K * max (f t) epsilon + eta) * h := by
      nlinarith [le_max_left (f t) epsilon]
    have hepsbound : epsilon ≤ max (f t) epsilon +
        (K * max (f t) epsilon + eta) * h :=
      (le_max_right _ _).trans (le_add_of_nonneg_right hmul)
    apply (div_le_iff₀ hpos).mpr
    linarith [max_le hfbound hepsbound]
  · intro eta heta
    have hft_eps : f t < epsilon := (le_of_not_gt hft).trans_lt hepsilon
    have hsmall : ∀ᶠ z in 𝓝 t, f z < epsilon := hf (Iio_mem_nhds hft_eps)
    have hshift : Tendsto (fun h : ℝ => t + h) (𝓝[>] 0) (𝓝 t) := by
      simpa using (tendsto_const_nhds.add
        (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun h : ℝ => t + h) (𝓝[>] 0) (𝓝 (t + 0)))
    filter_upwards [hshift.eventually hsmall] with h hh
    rw [max_eq_right hh.le, max_eq_right hft_eps.le, sub_self, zero_div]
    exact (mul_nonneg hK hepsilon.le).trans (le_add_of_nonneg_right heta.le)

theorem m64AnnulusForwardDerivativeBound.exponential_of_on_Ioo
    {f : ℝ → ℝ} {a b K : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hforward : ∀ x ∈ Ioo a b, AnnulusForwardDerivativeBound f (K * f x) x) :
    ∀ x ∈ Icc a b, f x ≤ Real.exp (K * (x - a)) * f a := by
  have hall := m64AnnulusForwardDerivativeBound.on_Ico_of_on_Ioo hf
    (continuousOn_const.mul hf) hforward
  have hcomparison := le_gronwallBound_of_liminf_deriv_right_le
    (δ := f a) (K := K) (ε := 0) (f' := fun x => K * f x) hf
    (fun x hx R hR => by
      simpa only [slope_def_field, div_eq_mul_inv, mul_comm] using
        m64AnnulusForwardDerivativeBound.frequently_slope_lt (hall x hx) hR)
    le_rfl (fun _ _ => le_add_of_nonneg_right le_rfl)
  intro x hx
  simpa only [gronwallBound_ε0, mul_comm] using hcomparison x hx

theorem m64AnnulusForwardDerivativeBound.exponential_of_positive_on_Ioo
    {f : ℝ → ℝ} {a b K : ℝ} (hK : 0 ≤ K)
    (hf : ContinuousOn f (Icc a b)) (ha : 0 ≤ f a)
    (hforward : ∀ x ∈ Ioo a b, 0 < f x →
      AnnulusForwardDerivativeBound f (K * f x) x) :
    ∀ x ∈ Icc a b, f x ≤ Real.exp (K * (x - a)) * f a := by
  intro x hx
  have hcomparison (epsilon : ℝ) (hepsilon : 0 < epsilon) :
      f x ≤ Real.exp (K * (x - a)) * max (f a) epsilon := by
    have hcutoff := m64AnnulusForwardDerivativeBound.exponential_of_on_Ioo
      (continuous_max.comp_continuousOn (hf.prodMk continuousOn_const)) (fun t ht =>
        m64AnnulusForwardDerivativeBound.max_positive hepsilon hK
          (hf.continuousAt (Icc_mem_nhds ht.1 ht.2)) (hforward t ht)) x hx
    exact (le_max_left _ _).trans hcutoff
  have hlimit := ContinuousWithinAt.closure_le
    (show (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) by simp)
    (f := fun _ : ℝ => f x)
    (g := fun epsilon => Real.exp (K * (x - a)) * max (f a) epsilon)
    continuousWithinAt_const (by fun_prop) hcomparison
  simpa only [max_eq_left ha] using hlimit

theorem m64AnnulusForwardDerivativeBound.on_Ico_of_positive_on_Ioo
    {f k : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hk : ContinuousOn k (Icc a b))
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hforward : ∀ t ∈ Ioo a b, 0 < f t →
      AnnulusForwardDerivativeBound f (k t * f t) t) :
    ∀ t ∈ Ico a b, AnnulusForwardDerivativeBound f (k t * f t) t := by
  obtain ⟨K0, hK0⟩ := isCompact_Icc.bddAbove_image hk
  let K := max K0 0
  have hK : 0 ≤ K := le_max_right _ _
  have hupper (x : ℝ) (hx : x ∈ Icc a b) : k x ≤ K :=
    (hK0 ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  apply m64AnnulusForwardDerivativeBound.on_Ico_of_on_Ioo
    (q := fun t => k t * f t) hf (hk.mul hf)
  intro t ht
  by_cases hft : 0 < f t
  · exact hforward t ht hft
  · have hzero : f t = 0 := le_antisymm (le_of_not_gt hft)
      (hnonneg t (Ioo_subset_Icc_self ht))
    have hvanish (z : ℝ) (hz : z ∈ Icc t b) : f z = 0 := by
      have hcomparison :=
        m64AnnulusForwardDerivativeBound.exponential_of_positive_on_Ioo hK
          (hf.mono (Icc_subset_Icc ht.1.le le_rfl)) (by rw [hzero])
          (fun x hx hpositive => by
            intro eta heta
            filter_upwards [hforward x ⟨ht.1.trans hx.1, hx.2⟩ hpositive eta heta]
              with h hh
            exact hh.trans (add_le_add
              (mul_le_mul_of_nonneg_right
                (hupper x ⟨ht.1.le.trans hx.1.le, hx.2.le⟩) hpositive.le) le_rfl)) z hz
      rw [hzero, mul_zero] at hcomparison
      exact le_antisymm hcomparison
        (hnonneg z ⟨ht.1.le.trans hz.1, hz.2⟩)
    intro eta heta
    have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo 0 (b - t) :=
      Ioo_mem_nhdsGT (sub_pos.mpr ht.2)
    filter_upwards [hsmall] with h hh
    rw [hvanish (t + h) (by constructor <;> linarith [hh.1, hh.2]),
      hzero, sub_self, zero_div, mul_zero, zero_add]
    exact heta.le

end PoincareConjecture
