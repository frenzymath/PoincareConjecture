import PoincareConjecture.Proofs.M34.Mathlib.ClosedIntervalDerivativeBounds
import Mathlib.Topology.UniformSpace.Cauchy

set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

theorem lipschitzOnWith_of_interior_deriv_bound_Ico
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b C : ℝ} (hC : 0 ≤ C)
    (hf : ContinuousOn f (Ico a b))
    (hd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hb : ∀ t ∈ Ioo a b, ‖deriv f t‖ ≤ C) :
    LipschitzOnWith ⟨C, hC⟩ f (Ico a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  let u := (max s t + b) / 2
  have hsu : s ≤ u := by dsimp [u]; linarith [le_max_left s t, max_lt hs.2 ht.2]
  have htu : t ≤ u := by dsimp [u]; linarith [le_max_right s t, max_lt hs.2 ht.2]
  have hub : u < b := by dsimp [u]; linarith [max_lt hs.2 ht.2]
  have hau : a < u := by
    dsimp [u]
    linarith [hs.1, le_max_left s t, max_lt hs.2 ht.2]
  have hsub : Icc a u ⊆ Ico a b := fun _ hv => ⟨hv.1, hv.2.trans_lt hub⟩
  have hsub' : Ioo a u ⊆ Ioo a b := fun _ hv => ⟨hv.1, hv.2.trans hub⟩
  change dist (f s) (f t) ≤ C * dist s t
  simpa only [dist_eq_norm, Real.norm_eq_abs] using
    norm_sub_le_of_interior_deriv_bound_Icc hau hC (hf.mono hsub)
      (fun v hv => hd v (hsub' hv)) (fun v hv => hb v (hsub' hv))
      ⟨ht.1, htu⟩ ⟨hs.1, hsu⟩

theorem LipschitzOnWith.exists_terminal_limit
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℝ → E} {a b : ℝ} {C : ℝ≥0} (hab : a < b)
    (hf : LipschitzOnWith C f (Ico a b)) :
    ∃ z : E, Tendsto f (𝓝[<] b) (𝓝 z) ∧
      ∀ t ∈ Ico a b, ‖f t - z‖ ≤ C * (b - t) := by
  have hc : Cauchy (𝓝[<] b) := cauchy_nhds.mono nhdsWithin_le_nhds
  obtain ⟨z, hz⟩ := cauchy_map_iff_exists_tendsto.mp
    (hc.map_of_le hf.uniformContinuousOn (le_principal_iff.mpr (Ico_mem_nhdsLT hab)))
  refine ⟨z, hz, ?_⟩
  intro t ht
  have hl : Tendsto (fun s => ‖f t - f s‖) (𝓝[<] b) (𝓝 ‖f t - z‖) :=
    (tendsto_const_nhds.sub hz).norm
  have hr : Tendsto (fun s : ℝ => (C : ℝ) * |t - s|)
      (𝓝[<] b) (𝓝 ((C : ℝ) * |t - b|)) :=
    tendsto_const_nhds.mul
      (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds)).abs
  have h := le_of_tendsto_of_tendsto hl hr (show ∀ᶠ s in 𝓝[<] b,
      ‖f t - f s‖ ≤ (C : ℝ) * |t - s| from by
    filter_upwards [Ico_mem_nhdsLT hab] with s hs
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hf.dist_le_mul t ht s hs)
  simpa only [abs_of_neg (sub_neg.mpr ht.2), neg_sub] using h

theorem tendstoUniformlyOn_of_terminal_norm_bound
    {X E : Type*} [NormedAddCommGroup E]
    {f : ℝ → X → E} {g : X → E} {a b C : ℝ} {K : Set X}
    (hab : a < b)
    (hbound : ∀ t ∈ Ico a b, ∀ x ∈ K, ‖f t x - g x‖ ≤ C * (b - t)) :
    TendstoUniformlyOn f g (𝓝[<] b) K := by
  have hsmall : Tendsto (fun t : ℝ => C * (b - t)) (𝓝[<] b) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => C * (b - t)) b := by fun_prop
    simpa only [sub_self, mul_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Ico_mem_nhdsLT hab, hsmall.eventually (gt_mem_nhds hε)] with t ht hεt
  intro x hx
  rw [dist_comm, dist_eq_norm]
  exact (hbound t ht x hx).trans_lt hεt
