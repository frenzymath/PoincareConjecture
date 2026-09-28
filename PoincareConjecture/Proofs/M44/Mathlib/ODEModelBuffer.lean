import PoincareConjecture.Proofs.M44.Mathlib.ODEUniformStability
import PoincareConjecture.Proofs.M44.Mathlib.FirstExit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension










set_option autoImplicit false

open Set Filter Metric
open scoped Topology NNReal ContDiff



theorem ode_mapsTo_ball_and_dist_le_of_model_buffer
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : E → E} {K : ℝ≥0} {R r T delta epsilon : ℝ}
    (hG : LipschitzOnWith K G (closedBall 0 R))
    (hdelta : 0 ≤ delta) (hepsilon : 0 ≤ epsilon)
    {γ η : ℝ → E}
    (hγ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt γ (F (γ t)) t)
    (hη : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt η (G (η t)) t)
    (hηnorm : ∀ t ∈ Icc (0 : ℝ) T, ‖η t‖ ≤ r)
    (hrR : r < R) (hstart : ‖γ 0‖ < R)
    (herror : ∀ z ∈ closedBall 0 R, dist (F z) (G z) ≤ epsilon)
    (hinitial : dist (γ 0) (η 0) ≤ delta)
    (hmargin : r + gronwallBound delta K epsilon T < R) :
    MapsTo γ (Icc (0 : ℝ) T) (ball 0 R) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        dist (γ t) (η t) ≤ gronwallBound delta K epsilon T := by
  have hηU : MapsTo η (Icc (0 : ℝ) T) (closedBall 0 R) := by
    intro t ht
    simpa only [mem_closedBall, dist_zero_right] using (hηnorm t ht).trans hrR.le
  have hγU : MapsTo γ (Icc (0 : ℝ) T) (ball 0 R) := by
    intro t ht
    by_contra hout
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc le_rfl ht.2
    have hcont : ContinuousOn γ (Icc (0 : ℝ) t) :=
      fun s hs => (hγ s (hsub hs)).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hfront, _, hprior⟩ := hcont.exists_first_frontier_time ht.1 isOpen_ball
      (by simpa only [mem_ball, dist_zero_right] using hstart) hout
    have hcT : c ∈ Icc (0 : ℝ) T := ⟨hc.1.le, hc.2.trans ht.2⟩
    have hsubc : Icc (0 : ℝ) c ⊆ Icc (0 : ℝ) T := Icc_subset_Icc le_rfl hcT.2
    have hprior' : MapsTo γ (Icc (0 : ℝ) c) (closedBall 0 R) :=
      fun s hs => closure_ball_subset_closedBall (hprior hs)
    have hdist := dist_le_gronwall_of_vectorField_error hG hdelta hepsilon
      (fun s hs => hγ s (hsubc hs)) (fun s hs => hη s (hsubc hs))
      hprior' (fun s hs => hηU (hsubc hs)) herror hinitial
      (show c ∈ Icc (0 : ℝ) c from ⟨hc.1.le, le_rfl⟩)
    have hdistT := hdist.trans ((gronwallBound_mono hdelta hepsilon K.coe_nonneg) hcT.2)
    have hnorm : ‖γ c‖ < R := by
      have htri : ‖γ c‖ ≤ dist (γ c) (η c) + ‖η c‖ := by
        simpa only [dist_eq_norm] using norm_le_norm_sub_add (γ c) (η c)
      linarith [hηnorm c hcT]
    have hnot : γ c ∉ ball 0 R := by
      rw [frontier, isOpen_ball.interior_eq] at hfront
      exact hfront.2
    exact hnot (by simpa only [mem_ball, dist_zero_right] using hnorm)
  refine ⟨hγU, ?_⟩
  intro t ht
  exact dist_le_gronwall_of_vectorField_error hG hdelta hepsilon hγ hη
    (fun s hs => ball_subset_closedBall (hγU hs)) hηU herror hinitial ht




theorem tendstoUniformlyOn_ode_of_model_buffer
    {E P ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ι} {F : ι → E → E} {G : E → E} {K : ℝ≥0} {R r T : ℝ}
    (hT : 0 ≤ T) (hrR : r < R) (hG : LipschitzOnWith K G (closedBall 0 R))
    {γ : ι → P → ℝ → E} {η : P → ℝ → E} {V : Set P}
    (hγ : ∀ᶠ i in l, ∀ p ∈ V, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (γ i p) (F i (γ i p t)) t)
    (hη : ∀ p ∈ V, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (η p) (G (η p t)) t)
    (hηnorm : ∀ p ∈ V, ∀ t ∈ Icc (0 : ℝ) T, ‖η p t‖ ≤ r)
    (hfield : TendstoUniformlyOn F G l (closedBall 0 R))
    (hinitial : TendstoUniformlyOn (fun i p => γ i p 0) (fun p => η p 0) l V) :
    TendstoUniformlyOn (fun i (z : P × ℝ) => γ i z.1 z.2)
      (fun z => η z.1 z.2) l (V ×ˢ Icc (0 : ℝ) T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  let d (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb := tendsto_gronwallBound_errors_zero (K := (K : ℝ)) (T := T) hd hd
  obtain ⟨n, hn, hn'⟩ := ((hb.eventually (gt_mem_nhds
    (lt_min hepsilon (sub_pos.mpr hrR)))).and
      (hd.eventually (gt_mem_nhds (sub_pos.mpr hrR)))).exists
  have hdpos : 0 < d n := by dsimp [d]; positivity
  have hnε : gronwallBound (d n) K (d n) T < epsilon := hn.trans_le (min_le_left _ _)
  have hnR : r + gronwallBound (d n) K (d n) T < R := by
    have h := hn.trans_le (min_le_right _ _)
    linarith
  filter_upwards [hγ, Metric.tendstoUniformlyOn_iff.mp hfield (d n) hdpos,
    Metric.tendstoUniformlyOn_iff.mp hinitial (d n) hdpos] with i hi hif hii
  intro z hz
  have hin : dist (γ i z.1 0) (η z.1 0) ≤ d n := by
    simpa only [dist_comm] using (hii z.1 hz.1).le
  have hstart : ‖γ i z.1 0‖ < R := by
    have htri : ‖γ i z.1 0‖ ≤ dist (γ i z.1 0) (η z.1 0) + ‖η z.1 0‖ := by
      simpa only [dist_eq_norm] using norm_le_norm_sub_add (γ i z.1 0) (η z.1 0)
    have hm := hηnorm z.1 hz.1 0 ⟨le_rfl, hT⟩
    linarith
  have h := ode_mapsTo_ball_and_dist_le_of_model_buffer hG hdpos.le hdpos.le
    (hi z.1 hz.1) (hη z.1 hz.1) (hηnorm z.1 hz.1) hrR hstart
    (fun y hy => by simpa only [dist_comm] using (hif y hy).le) hin hnR
  simpa only [dist_comm] using (h.2 z.2 hz.2).trans_lt hnε




theorem tendstoUniformlyOn_ode_of_compact_model
    {E P ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace P]
    {l : Filter ι} {F : ι → E → E} {G : E → E} {T : ℝ}
    (hT : 0 ≤ T) (hG : ContDiff ℝ 1 G)
    {γ : ι → P → ℝ → E} {η : P → ℝ → E} {K : Set P}
    (hK : IsCompact K)
    (hηcont : ContinuousOn (fun z : P × ℝ => η z.1 z.2) (K ×ˢ Icc (0 : ℝ) T))
    (hγ : ∀ᶠ i in l, ∀ p ∈ K, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (γ i p) (F i (γ i p t)) t)
    (hη : ∀ p ∈ K, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (η p) (G (η p t)) t)
    (hfield : ∀ R : ℝ, TendstoUniformlyOn F G l (closedBall 0 R))
    (hinitial : TendstoUniformlyOn (fun i p => γ i p 0) (fun p => η p 0) l K) :
    TendstoUniformlyOn (fun i (z : P × ℝ) => γ i z.1 z.2)
      (fun z => η z.1 z.2) l (K ×ˢ Icc (0 : ℝ) T) := by
  obtain ⟨r, hr⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hηcont
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) (r + 1)).exists_bound_of_continuousOn
    ((hG.fderiv_right (m := 0) (by simp)).continuous.continuousOn)
  have hLip : LipschitzOnWith ⟨max C 0, le_max_right _ _⟩ G (closedBall 0 (r + 1)) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => hG.differentiable one_ne_zero x) ?_ (convex_closedBall _ _)
    intro x hx
    exact (hC x hx).trans (le_max_left _ _)
  exact tendstoUniformlyOn_ode_of_model_buffer hT (lt_add_one r) hLip hγ hη
    (fun p hp t ht => hr (p, t) ⟨hp, ht⟩) (hfield (r + 1)) hinitial
