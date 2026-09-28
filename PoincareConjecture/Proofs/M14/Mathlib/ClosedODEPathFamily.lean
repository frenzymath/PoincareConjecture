import PoincareConjecture.Proofs.M14.Mathlib.ClosedODEParameterSmooth
import PoincareConjecture.Proofs.M14.Mathlib.ClosedODELocalExistence
import PoincareConjecture.Proofs.M14.Mathlib.ClosedStateExtension
import PoincareConjecture.Proofs.M14.Mathlib.ContinuousPathFamily











set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]





theorem closedODE_exists_smooth_path_family {a b : ℝ} (hab : a < b) (t₀ : Icc a b)
    {U : Set E} (hU : IsOpen U) (f : ℝ × E → E)
    (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ U)) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ c d : ℝ, ∃ t₁ : Icc c d,
      c < d ∧ a ≤ c ∧ d ≤ b ∧ t₁.val = t₀.val ∧ Icc c d ∈ 𝓝[Icc a b] t₀.val ∧
      ∃ ρ > (0 : ℝ), ∃ Φ : E → C(Icc c d, E),
        ContDiffOn ℝ ∞ Φ (ball x₀ ρ) ∧ ∀ x ∈ ball x₀ ρ,
          Φ x t₁ = x ∧ (∀ s : Icc c d, Φ x s ∈ U) ∧
          ContDiffOn ℝ ∞
            (fun s => Φ x (projIcc c d (t₁.property.1.trans t₁.property.2) s)) (Icc c d) ∧
          ∀ s : Icc c d, HasDerivWithinAt
            (fun r => Φ x (projIcc c d (t₁.property.1.trans t₁.property.2) r))
            (f (s.val, Φ x s)) (Icc c d) s.val := by
  obtain ⟨R, hR, g, hRU, hg, hgf⟩ := exists_closedTime_state_extension hU f hf hx₀
  have hD := M08.spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hab) isOpen_univ g hg
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod (isCompact_closedBall x₀ R)).exists_bound_of_continuousOn
    (hD.continuousOn.mono (prod_mono Subset.rfl (subset_univ _)))
  let η := 1 / (4 * (|K| + 1))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηK : (2 * η) * |K| < 1 := by
    calc
      (2 * η) * |K| = (2 * |K|) / (4 * (|K| + 1)) := by dsimp only [η]; ring
      _ < 1 := (div_lt_iff₀ (by positivity : 0 < 4 * (|K| + 1))).mpr
        (by nlinarith [abs_nonneg K])
  let c₀ := max a (t₀.val - η)
  let d₀ := min b (t₀.val + η)
  have hc₀d₀ : c₀ < d₀ := max_lt (lt_min hab (by linarith [t₀.property.1]))
    (lt_min (by linarith [t₀.property.2]) (by linarith))
  have ht₀ : t₀.val ∈ Icc c₀ d₀ :=
    ⟨max_le t₀.property.1 (by linarith), le_min t₀.property.2 (by linarith)⟩
  have hsub₀ : Icc c₀ d₀ ⊆ Icc a b := Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hballU : ball x₀ R ⊆ U := ball_subset_closedBall.trans hRU
  obtain ⟨δ, hδ, ρ, hρ, hcd, α, hα, hsol⟩ := closedODE_exists_local_family hc₀d₀
    isOpen_ball f (hf.mono (prod_mono hsub₀ hballU)) ht₀ (mem_ball_self hR)
  let c := max c₀ (t₀.val - δ)
  let d := min d₀ (t₀.val + δ)
  have ht₁ : c ≤ t₀.val ∧ t₀.val ≤ d :=
    ⟨max_le ht₀.1 (by linarith), le_min ht₀.2 (by linarith)⟩
  let t₁ : Icc c d := ⟨t₀.val, ht₁⟩
  have hc₀c : c₀ ≤ c := le_max_left _ _
  have hdd₀ : d ≤ d₀ := min_le_left _ _
  have hac : a ≤ c := (le_max_left _ _).trans hc₀c
  have hdb : d ≤ b := hdd₀.trans (min_le_left _ _)
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hac hdb
  have hlen : d - c ≤ 2 * η := by
    have hc : t₀.val - η ≤ c₀ := le_max_right _ _
    have hd : d₀ ≤ t₀.val + η := min_le_right _ _
    linarith
  have hnear : Icc c d ∈ 𝓝[Icc a b] t₀.val := by
    have hε := lt_min hη hδ
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (Ioo_mem_nhds (show t₀.val - min η δ < t₀.val by linarith)
        (show t₀.val < t₀.val + min η δ by linarith))] with t ht htε
    refine ⟨max_le (max_le ht.1 ?_) ?_, le_min (le_min ht.2 ?_) ?_⟩ <;>
      linarith [min_le_left η δ, min_le_right η δ, htε.1, htε.2]
  have hfamily : ContinuousOn (fun z : E × Icc c d => α (z.1, z.2.val))
      (ball x₀ ρ ×ˢ univ) :=
    hα.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun z hz => ⟨ball_subset_closedBall hz.1, z.2.property⟩)
  obtain ⟨Φ, hΦ, hΦeq⟩ := exists_continuousOn_pathFamily _ hfamily
    (ContinuousMap.const (Icc c d) x₀)
  have hdata (x : E) (hx : x ∈ ball x₀ ρ) :
      Φ x t₁ = x ∧ (∀ s : Icc c d, Φ x s ∈ ball x₀ R) ∧
      ContDiffOn ℝ ∞
        (fun s => Φ x (projIcc c d (ht₁.1.trans ht₁.2) s)) (Icc c d) ∧
      ∀ s : Icc c d, HasDerivWithinAt
        (fun r => Φ x (projIcc c d (ht₁.1.trans ht₁.2) r))
        (f (s.val, Φ x s)) (Icc c d) s.val := by
    obtain ⟨hi, hmap, hsm, hd⟩ := hsol x (ball_subset_closedBall hx)
    have heq : EqOn (fun s => Φ x (projIcc c d (ht₁.1.trans ht₁.2) s))
        (fun s => α (x, s)) (Icc c d) := by
      intro s hs
      change Φ x (projIcc c d (ht₁.1.trans ht₁.2) s) = α (x, s)
      rw [projIcc_of_mem (ht₁.1.trans ht₁.2) hs]
      exact hΦeq x hx ⟨s, hs⟩
    refine ⟨(hΦeq x hx t₁).trans hi, ?_, hsm.congr heq, ?_⟩
    · intro s
      rw [hΦeq x hx s]
      exact hmap s.property
    · intro s
      have h := hd s.val s.property
      rw [← hΦeq x hx s] at h
      exact h.congr_of_mem heq s.property
  have hg' : ContDiffOn ℝ ∞ g (Icc c d ×ˢ univ) := hg.mono (prod_mono hsub Subset.rfl)
  refine ⟨c, d, t₁, hcd, hac, hdb, rfl, hnear, ρ, hρ, Φ, ?_, ?_⟩
  · apply isOpen_ball.contDiffOn_iff.mpr
    intro x hx
    have hnorm : ‖closedTimePostcomp (M08.spatialWithinFDeriv (Icc c d) univ g)
        (M08.spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hcd) isOpen_univ g hg').continuousOn
          (Φ x)‖ ≤ |K| := by
      apply (ContinuousMap.norm_le _ (abs_nonneg K)).2
      intro s
      change ‖M08.spatialWithinFDeriv (Icc c d) univ g (s.val, Φ x s)‖ ≤ |K|
      rw [spatialWithinFDeriv_subset_time isOpen_univ g hg hsub s.property (mem_univ _)]
      exact (hK (s.val, Φ x s) ⟨hsub s.property,
        ball_subset_closedBall ((hdata x hx).2.1 s)⟩).trans (le_abs_self K)
    apply closedODEFamily_contDiffAt hcd t₁ g hg' Φ
      (hΦ.continuousAt (isOpen_ball.mem_nhds hx))
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hdata y hy).1
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      intro s
      rw [hgf ⟨hsub s.property, ball_subset_closedBall ((hdata y hy).2.1 s)⟩]
      exact (hdata y hy).2.2.2 s
    · exact (mul_le_mul hlen hnorm (norm_nonneg _) (by positivity)).trans_lt hηK
  · intro x hx
    exact ⟨(hdata x hx).1, fun s => hballU ((hdata x hx).2.1 s), (hdata x hx).2.2⟩

end PoincareConjecture.M14
