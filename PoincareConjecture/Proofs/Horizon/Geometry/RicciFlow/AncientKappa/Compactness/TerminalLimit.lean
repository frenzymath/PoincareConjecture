import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.TerminalJets
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Lipschitz













set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.AncientCompactness

variable {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]



theorem cauchySeq_terminal_of_time_lipschitz
    {f : ℕ → ℝ → Y} {g : ℝ → Y} {L : ℝ} (hL : 0 ≤ L)
    (hconv : ∀ t < 0, Tendsto (fun k => f k t) atTop (𝓝 (g t)))
    (hLip : ∀ᶠ k in atTop, ∀ s ∈ Icc (-1) 0, ∀ t ∈ Icc (-1) 0,
      dist (f k s) (f k t) ≤ L * |s - t|) :
    CauchySeq (fun k => f k 0) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let δ : ℝ := min (1 / 2) (ε / (4 * (L + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδone : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδsmall : 2 * L * δ < ε / 2 := by
    have hd := (le_div_iff₀ (by positivity : 0 < 4 * (L + 1))).mp
      (show δ ≤ ε / (4 * (L + 1)) from min_le_right _ _)
    nlinarith
  have hclose := (Metric.tendsto_nhds.mp (hconv (-δ) (by linarith)))
    (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hLip.and hclose)
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hs : -δ ∈ Icc (-1) 0 := ⟨by linarith, by linarith⟩
  have hz : (0 : ℝ) ∈ Icc (-1) 0 := by norm_num
  have hm0 : dist (f m 0) (f m (-δ)) ≤ L * δ := by
    simpa only [zero_sub, neg_neg, abs_of_pos hδ] using (hN m hm).1 0 hz (-δ) hs
  have hn0 : dist (f n (-δ)) (f n 0) ≤ L * δ := by
    simpa only [sub_zero, abs_neg, abs_of_pos hδ] using (hN n hn).1 (-δ) hs 0 hz
  have hmc := (hN m hm).2
  have hnc := (hN n hn).2
  have h₁ := dist_triangle (f m 0) (f m (-δ)) (f n 0)
  have h₂ := dist_triangle (f m (-δ)) (g (-δ)) (f n 0)
  have h₃ := dist_triangle (g (-δ)) (f n (-δ)) (f n 0)
  rw [dist_comm (g (-δ)) (f n (-δ))] at h₃
  linarith



theorem exists_terminal_limit_of_time_lipschitz [CompleteSpace Y]
    {f : ℕ → ℝ × X → Y} {g : ℝ × X → Y} {U : Set X}
    (hconv : ∀ K : Set (ℝ × X), IsCompact K → K ⊆ Iio 0 ×ˢ U →
      TendstoUniformlyOn f g atTop K)
    (htime : ∀ V : Set X, IsCompact V → V ⊆ U →
      ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ k in atTop,
        ∀ x ∈ V, ∀ s ∈ Icc (-1) 0, ∀ t ∈ Icc (-1) 0,
          dist (f k (s, x)) (f k (t, x)) ≤ L * |s - t|) :
    ∃ G : ℝ × X → Y, EqOn G g (Iio 0 ×ˢ U) ∧
      (∀ x ∈ U, ContinuousOn (fun t : ℝ => G (t, x)) (Icc (-1) 0)) ∧
      ∀ K : Set (ℝ × X), IsCompact K → K ⊆ Iic 0 ×ˢ U →
        TendstoUniformlyOn f G atTop K := by
  classical
  have hinterior (x : X) (hx : x ∈ U) (t : ℝ) (ht : t < 0) :
      Tendsto (fun k => f k (t, x)) atTop (𝓝 (g (t, x))) :=
    (hconv {(t, x)} isCompact_singleton
      (singleton_subset_iff.mpr ⟨ht, hx⟩)).tendsto_at (mem_singleton _)
  have hboundary (x : X) (hx : x ∈ U) :
      ∃ y : Y, Tendsto (fun k => f k (0, x)) atTop (𝓝 y) := by
    obtain ⟨L, hL, hLip⟩ := htime {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    apply cauchySeq_tendsto_of_complete
    apply cauchySeq_terminal_of_time_lipschitz hL (hinterior x hx)
    exact hLip.mono fun k hk => hk x (mem_singleton _)
  let boundary (x : X) : Y := if hx : x ∈ U then (hboundary x hx).choose else g (0, x)
  let G : ℝ × X → Y := fun z => if z.1 < 0 then g z else boundary z.2
  have heq : EqOn G g (Iio 0 ×ˢ U) := fun z hz => if_pos hz.1
  have hpoint (x : X) (hx : x ∈ U) (t : ℝ) (ht : t ≤ 0) :
      Tendsto (fun k => f k (t, x)) atTop (𝓝 (G (t, x))) := by
    rcases ht.lt_or_eq with ht | rfl
    · simpa only [G, if_pos ht] using hinterior x hx t ht
    · simpa only [G, lt_self_iff_false, if_false, boundary, dif_pos hx] using
        (hboundary x hx).choose_spec
  have hcontinuous (x : X) (hx : x ∈ U) :
      ContinuousOn (fun t : ℝ => G (t, x)) (Icc (-1) 0) := by
    obtain ⟨L, hL, hLip⟩ := htime {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    apply (show LipschitzOnWith ⟨L, hL⟩ (fun t : ℝ => G (t, x)) (Icc (-1) 0) from ?_).continuousOn
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [Real.dist_eq]
    apply le_of_tendsto ((hpoint x hx s hs.2).dist (hpoint x hx t ht.2))
    exact hLip.mono fun k hk => hk x (mem_singleton _) s hs t ht
  refine ⟨G, heq, hcontinuous, ?_⟩
  intro K hK hKU
  apply tendstoUniformlyOn_past_of_time_lipschitz (U := U) ?_ hcontinuous htime hK hKU
  intro A hA hAU
  exact (hconv A hA hAU).congr_right (fun z hz => (heq (hAU hz)).symm)

end PoincareConjecture.AncientCompactness
