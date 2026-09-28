import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Cauchy
import PoincareConjecture.Proofs.M07.Analysis.ODE.LocalFlow.Smooth

namespace Poincare.ODE

open Set Metric Filter
open scoped Topology NNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_lipschitzOnWith_of_compact_trajectory
    {F : E → E} {S : Set E} (hS : IsCompact S) (hF : ContinuousOn F S)
    {a b : ℝ} {γ : ℝ → E}
    (hmem : ∀ t ∈ Ioo a b, γ t ∈ S)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (F (γ t)) t) :
    ∃ K : ℝ≥0, LipschitzOnWith K γ (Ioo a b) := by
  obtain ⟨K, hK, hbound⟩ :=
    (hS.image_of_continuousOn hF).isBounded.exists_pos_norm_le
  refine ⟨⟨K, hK.le⟩, (convex_Ioo a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (hγ t ht).hasDerivWithinAt) ?_⟩
  intro t ht
  exact_mod_cast hbound (F (γ t)) (mem_image_of_mem F (hmem t ht))

theorem exists_endpoint_of_compact_trajectory
    {F : E → E} {S : Set E} (hS : IsCompact S) (hF : ContinuousOn F S)
    {a b : ℝ} (hab : a < b) {γ : ℝ → E}
    (hmem : ∀ t ∈ Ioo a b, γ t ∈ S)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (F (γ t)) t) :
    ∃ z ∈ S, Tendsto γ (𝓝[<] b) (𝓝 z) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_of_compact_trajectory hS hF hmem hγ
  have hinterval : 𝓝[<] b ≤ 𝓟 (Ioo a b) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact inf_le_right
  have hc : Cauchy (𝓝[<] b) := cauchy_nhds.mono nhdsWithin_le_nhds
  apply hS.isComplete (map γ (𝓝[<] b)) (hc.map_of_le hK.uniformContinuousOn hinterval)
  rw [le_principal_iff, mem_map]
  exact mem_of_superset (le_principal_iff.mp hinterval) hmem

theorem exists_continuation_of_compact_trajectory [FiniteDimensional ℝ E]
    {U S : Set E} (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    {F : E → E} (hF : ContDiffOn ℝ ∞ F U)
    {a b : ℝ} (hab : a < b) {γ : ℝ → E}
    (hmem : ∀ t ∈ Ioo a b, γ t ∈ S)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (F (γ t)) t) :
    ∃ δ > 0, ∃ η : ℝ → E,
      EqOn η γ (Ioo a b) ∧ η b ∈ S ∧
      (∀ t ∈ Ioo a (b + δ), η t ∈ U) ∧
      (∀ t ∈ Ioo a (b + δ), HasDerivAt η (F (η t)) t) := by
  obtain ⟨z, hz, hlim⟩ := exists_endpoint_of_compact_trajectory hS
    (hF.continuousOn.mono hSU) hab hmem hγ
  obtain ⟨V, δ, Φ, _, hzV, _, hδ, _, hinit, hmaps, hflow⟩ :=
    LocalFlow.exists_smooth_localFlow hU hF (hSU hz)
  let β : ℝ → E := fun t => Φ (z, t - b)
  have hβb : β b = z := by simpa [β] using hinit z hzV
  have hβ : ∀ t ∈ Ioo (b - δ) (b + δ), HasDerivAt β (F (β t)) t := by
    intro t ht
    have htδ : t - b ∈ Ioo (-δ) δ := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa [β, Function.comp_def] using
      (hflow z hzV (t - b) htδ).scomp t ((hasDerivAt_id t).sub_const b)
  let η : ℝ → E := fun t => if t < b then γ t else β t
  have hηb : η b = z := by simp [η, hβb]
  have hηeq : EqOn η γ (Ioo a b) := fun t ht => if_pos ht.2
  have hηleft : ∀ t ∈ Ioo a b, HasDerivAt η (F (η t)) t := by
    intro t ht
    have heq : η =ᶠ[𝓝 t] γ := by
      filter_upwards [isOpen_Iio.mem_nhds ht.2] with s hs
      exact if_pos hs
    rw [hηeq ht]
    exact (hγ t ht).congr_of_eventuallyEq heq
  have hηright : ∀ t ∈ Ioo b (b + δ), HasDerivAt η (F (η t)) t := by
    intro t ht
    have heq : η =ᶠ[𝓝 t] β := by
      filter_upwards [isOpen_Ioi.mem_nhds ht.1] with s hs
      exact if_neg (not_lt.mpr hs.le)
    rw [show η t = β t from if_neg (not_lt.mpr ht.1.le)]
    exact (hβ t ⟨by linarith [ht.1], ht.2⟩).congr_of_eventuallyEq heq
  have hηlim : Tendsto η (𝓝[<] b) (𝓝 z) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (if_pos ht).symm
  have hIoo : Ioo a b ∈ 𝓝[<] b := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact self_mem_nhdsWithin
  have hleft : HasDerivWithinAt η (F z) (Iic b) b := by
    apply hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hηleft t ht).differentiableAt.differentiableWithinAt)
    · change Tendsto η (𝓝[Ioo a b] b) (𝓝 (η b))
      rw [hηb, nhdsWithin_Ioo_eq_nhdsLT hab]
      exact hηlim
    · exact hIoo
    · have hFz := hF.continuousOn.continuousAt (hU.mem_nhds (hSU hz))
      apply (hFz.tendsto.comp hηlim).congr'
      filter_upwards [hIoo] with t ht
      exact (hηleft t ht).deriv.symm
  have hright : HasDerivWithinAt η (F z) (Ici b) b := by
    have hb := (hβ b ⟨by linarith, by linarith⟩).hasDerivWithinAt (s := Ici b)
    rw [hβb] at hb
    apply hb.congr
    · intro t ht
      exact if_neg (not_lt.mpr ht)
    · exact if_neg (lt_irrefl b)
  have hjoin : HasDerivAt η (F (η b)) b := by
    rw [hηb]
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hleft.union hright
  refine ⟨δ, hδ, η, hηeq, by simpa only [hηb] using hz, ?_, ?_⟩
  · intro t ht
    by_cases htb : t < b
    · rw [hηeq ⟨ht.1, htb⟩]
      exact hSU (hmem t ⟨ht.1, htb⟩)
    · change (if t < b then γ t else β t) ∈ U
      rw [if_neg htb]
      exact hmaps z hzV (t - b) ⟨by linarith, by linarith [ht.2]⟩
  · intro t ht
    rcases lt_trichotomy t b with htb | rfl | hbt
    · exact hηleft t ⟨ht.1, htb⟩
    · exact hjoin
    · exact hηright t ⟨hbt, ht.2⟩

end Poincare.ODE
