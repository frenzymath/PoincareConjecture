import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem closedODE_eventuallyEqWithin {a b t₀ : ℝ} (hab : a < b)
    {U : Set E} (hU : IsOpen U) (V : ℝ × E → E)
    (hV : ContDiffOn ℝ ∞ V (Icc a b ×ˢ U))
    {f g : ℝ → E} (ht₀ : t₀ ∈ Icc a b) (hf₀ : f t₀ ∈ U)
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (V (t, f t)) (Icc a b) t)
    (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (V (t, g t)) (Icc a b) t)
    (heq : f t₀ = g t₀) : f =ᶠ[𝓝[Icc a b] t₀] g := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU (f t₀) hf₀
  let S := Icc a b ×ˢ ball (f t₀) r
  have hS : Convex ℝ S := (convex_Icc a b).prod (convex_ball _ _)
  have hSdiff : UniqueDiffOn ℝ S := (uniqueDiffOn_Icc hab).prod isOpen_ball.uniqueDiffOn
  have hVS : ContDiffOn ℝ ∞ V S := hV.mono (prod_mono Subset.rfl hball)
  have h₀S : (t₀, f t₀) ∈ S := ⟨ht₀, mem_ball_self hr⟩
  obtain ⟨K, Q, hQ, hLip⟩ := hS.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt
    (eventually_nhdsWithin_of_forall (fun z hz =>
      ((hVS z hz).differentiableWithinAt (by simp)).hasFDerivWithinAt))
    ((hVS.fderivWithin hSdiff (m := ∞) (by simp)).continuousOn _ h₀S)
  have hslice (t : ℝ) : LipschitzOnWith K (fun z => V (t, z)) {z | (t, z) ∈ Q} := by
    intro z hz w hw
    simpa only [Prod.edist_eq, edist_self,
      max_eq_right (show 0 ≤ edist z w from bot_le)] using hLip hz hw
  obtain ⟨ε, hε, hQsub⟩ := Metric.mem_nhdsWithin_iff.mp hQ
  have hfc : ContinuousOn f (Icc a b) := HasDerivWithinAt.continuousOn hf
  have hgc : ContinuousOn g (Icc a b) := HasDerivWithinAt.continuousOn hg
  have hfQ : ∀ᶠ t in 𝓝[Icc a b] t₀, (t, f t) ∈ Q := by
    filter_upwards [self_mem_nhdsWithin,
      (continuousWithinAt_id.prodMk (hfc t₀ ht₀)).preimage_mem_nhdsWithin
        (ball_mem_nhds (t₀, f t₀) hε),
      (hfc t₀ ht₀).preimage_mem_nhdsWithin (ball_mem_nhds (f t₀) hr)] with t ht htf hfr
    exact hQsub ⟨htf, ht, hfr⟩
  have hgQ : ∀ᶠ t in 𝓝[Icc a b] t₀, (t, g t) ∈ Q := by
    have hp : ball (t₀, f t₀) ε ∈ 𝓝 (t₀, g t₀) := by
      rw [← heq]
      exact ball_mem_nhds _ hε
    have hb : ball (f t₀) r ∈ 𝓝 (g t₀) := by
      rw [← heq]
      exact ball_mem_nhds _ hr
    filter_upwards [self_mem_nhdsWithin,
      (continuousWithinAt_id.prodMk (hgc t₀ ht₀)).preimage_mem_nhdsWithin hp,
      (hgc t₀ ht₀).preimage_mem_nhdsWithin hb] with t ht htg hgr
    exact hQsub ⟨htg, ht, hgr⟩
  obtain ⟨δ, hδ, hdata⟩ := Metric.mem_nhdsWithin_iff.mp (hfQ.and hgQ)
  rw [Real.ball_eq_Ioo] at hdata
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [Metric.ball_mem_nhds t₀ hδ] with t ht htI
  rw [Real.ball_eq_Ioo] at ht
  by_cases horder : t₀ ≤ t
  · have hsegment : Icc t₀ t ⊆ Ioo (t₀ - δ) (t₀ + δ) ∩ Icc a b := by
      intro r hr
      exact ⟨⟨by linarith [hr.1], hr.2.trans_lt ht.2⟩,
        ht₀.1.trans hr.1, hr.2.trans htI.2⟩
    have hsub : Icc t₀ t ⊆ Icc a b := fun r hr => (hsegment hr).2
    exact ODE_solution_unique_of_mem_Icc_right (fun r _ => hslice r)
      (hfc.mono hsub)
      (fun r hr => (hf r (hsub (Ico_subset_Icc_self hr))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht₀.1.trans hr.1, hr.2.trans_le htI.2⟩))
      (fun r hr => (hdata (hsegment (Ico_subset_Icc_self hr))).1)
      (hgc.mono hsub)
      (fun r hr => (hg r (hsub (Ico_subset_Icc_self hr))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht₀.1.trans hr.1, hr.2.trans_le htI.2⟩))
      (fun r hr => (hdata (hsegment (Ico_subset_Icc_self hr))).2) heq ⟨horder, le_rfl⟩
  · have hle : t ≤ t₀ := (lt_of_not_ge horder).le
    have hsegment : Icc t t₀ ⊆ Ioo (t₀ - δ) (t₀ + δ) ∩ Icc a b := by
      intro r hr
      exact ⟨⟨ht.1.trans_le hr.1, by linarith [hr.2]⟩,
        htI.1.trans hr.1, hr.2.trans ht₀.2⟩
    have hsub : Icc t t₀ ⊆ Icc a b := fun r hr => (hsegment hr).2
    exact ODE_solution_unique_of_mem_Icc_left (fun r _ => hslice r)
      (hfc.mono hsub)
      (fun r hr => (hf r (hsub (Ioc_subset_Icc_self hr))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨htI.1.trans_lt hr.1, hr.2.trans ht₀.2⟩))
      (fun r hr => (hdata (hsegment (Ioc_subset_Icc_self hr))).1)
      (hgc.mono hsub)
      (fun r hr => (hg r (hsub (Ioc_subset_Icc_self hr))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨htI.1.trans_lt hr.1, hr.2.trans ht₀.2⟩))
      (fun r hr => (hdata (hsegment (Ioc_subset_Icc_self hr))).2) heq ⟨le_rfl, hle⟩

theorem closedODE_interval_solution_unique {a b t₀ : ℝ} (hab : a < b)
    {U : Set E} (hU : IsOpen U) (V : ℝ × E → E)
    (hV : ContDiffOn ℝ ∞ V (Icc a b ×ˢ U))
    {f g : ℝ → E} (hsrc : MapsTo f (Icc a b) U)
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (V (t, f t)) (Icc a b) t)
    (hg : ∀ t ∈ Icc a b, HasDerivWithinAt g (V (t, g t)) (Icc a b) t)
    (ht₀ : t₀ ∈ Icc a b) (heq : f t₀ = g t₀) : EqOn f g (Icc a b) := by
  let : PreconnectedSpace (Icc a b) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let A : Set (Icc a b) := {t | f t = g t}
  have hfc : ContinuousOn f (Icc a b) := HasDerivWithinAt.continuousOn hf
  have hgc : ContinuousOn g (Icc a b) := HasDerivWithinAt.continuousOn hg
  have hclosed : IsClosed A := isClosed_eq hfc.domRestrict hgc.domRestrict
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hlocal := closedODE_eventuallyEqWithin hab hU V hV t.property
      (hsrc t.property) hf hg ht
    exact (eventually_nhds_subtype_iff (Icc a b) t (fun r => f r = g r)).mpr hlocal
  have hAll : A = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨t₀, ht₀⟩, heq⟩
  intro t ht
  have hm : (⟨t, ht⟩ : Icc a b) ∈ A := by rw [hAll]; trivial
  exact hm

end PoincareConjecture.M14
