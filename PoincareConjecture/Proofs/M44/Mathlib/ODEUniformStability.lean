import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

theorem dist_le_gronwall_of_vectorField_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : E → E} {U : Set E} {K : ℝ≥0} (hG : LipschitzOnWith K G U)
    {γ η : ℝ → E} {T δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hγ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt γ (F (γ t)) t)
    (hη : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt η (G (η t)) t)
    (hγU : MapsTo γ (Icc (0 : ℝ) T) U)
    (hηU : MapsTo η (Icc (0 : ℝ) T) U)
    (herror : ∀ z ∈ U, dist (F z) (G z) ≤ ε)
    (hinitial : dist (γ 0) (η 0) ≤ δ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    dist (γ t) (η t) ≤ gronwallBound δ K ε T := by
  have h := dist_le_of_approx_trajectories_ODE_of_mem
    (v := fun _ => G) (s := fun _ => U) (εf := ε) (εg := 0)
    (fun _ _ => hG)
    (fun s hs => (hγ s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hγ s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun s hs => herror _ (hγU (Ico_subset_Icc_self hs)))
    (fun _ hs => hγU (Ico_subset_Icc_self hs))
    (fun s hs => (hη s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hη s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun _ _ => by simp)
    (fun _ hs => hηU (Ico_subset_Icc_self hs)) hinitial t ht
  simp only [add_zero, sub_zero] at h
  exact h.trans ((gronwallBound_mono hδ hε K.coe_nonneg) ht.2)

theorem tendsto_gronwallBound_errors_zero
    {ι : Type*} {l : Filter ι} {δ ε : ι → ℝ} {K T : ℝ}
    (hδ : Tendsto δ l (𝓝 0)) (hε : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i => gronwallBound (δ i) K (ε i) T) l (𝓝 0) := by
  by_cases hK : K = 0
  · simp only [hK, gronwallBound_K0]
    simpa using hδ.add (hε.mul_const T)
  · simp only [gronwallBound_of_K_ne_0 hK]
    simpa using (hδ.mul_const (Real.exp (K * T))).add
      ((hε.div_const K).mul_const (Real.exp (K * T) - 1))

theorem tendstoUniformlyOn_ode_of_vectorField_error
    {E P ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ι} {F : ι → E → E} {G : E → E} {U : Set E}
    {K : ℝ≥0} (hG : LipschitzOnWith K G U)
    {γ : ι → P → ℝ → E} {η : P → ℝ → E} {V : Set P} {T : ℝ}
    {δ ε : ι → ℝ} (hδpos : ∀ i, 0 ≤ δ i) (hεpos : ∀ i, 0 ≤ ε i)
    (hδ : Tendsto δ l (𝓝 0)) (hε : Tendsto ε l (𝓝 0))
    (hγ : ∀ i p, p ∈ V → ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (γ i p) (F i (γ i p t)) t)
    (hη : ∀ p, p ∈ V → ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (η p) (G (η p t)) t)
    (hγU : ∀ i p, p ∈ V → MapsTo (γ i p) (Icc (0 : ℝ) T) U)
    (hηU : ∀ p, p ∈ V → MapsTo (η p) (Icc (0 : ℝ) T) U)
    (herror : ∀ i z, z ∈ U → dist (F i z) (G z) ≤ ε i)
    (hinitial : ∀ i p, p ∈ V → dist (γ i p 0) (η p 0) ≤ δ i) :
    TendstoUniformlyOn (fun i (z : P × ℝ) => γ i z.1 z.2)
      (fun z => η z.1 z.2) l (V ×ˢ Icc (0 : ℝ) T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro a ha
  have hbound := tendsto_gronwallBound_errors_zero (K := (K : ℝ)) (T := T) hδ hε
  filter_upwards [hbound.eventually (gt_mem_nhds ha)] with i hi
  intro z hz
  simpa only [dist_comm] using
    (dist_le_gronwall_of_vectorField_error hG (hδpos i) (hεpos i)
    (hγ i z.1 hz.1) (hη z.1 hz.1) (hγU i z.1 hz.1) (hηU z.1 hz.1)
    (herror i) (hinitial i z.1 hz.1) hz.2).trans_lt hi
