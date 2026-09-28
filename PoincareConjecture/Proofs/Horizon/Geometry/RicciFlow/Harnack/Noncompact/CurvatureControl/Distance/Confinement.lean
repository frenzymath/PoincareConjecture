import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.FiniteCalabi
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.FiniteContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.RicciFlow

private theorem le_terminal_add_of_upper_support
    {f : ℝ → ℝ} {a b C R : ℝ} (hC : 0 ≤ C)
    (hf : ContinuousOn f (Icc a b)) (hgap : f b + C * (b - a) < R)
    (hsupport : ∀ t ∈ Ioc a b, f t < R →
      ∃ (ρ : ℝ → ℝ) (d : ℝ), ρ t = f t ∧
        (∀ s ∈ Icc a t, f s ≤ ρ s) ∧ HasDerivAt ρ d t ∧ -C ≤ d) :
    ∀ s ∈ Icc a b, f s ≤ f b + C * (b - s) := by
  intro s hs
  have hrate (c : ℝ) (hc : C < c) (hcap : f b + c * (b - a) < R) :
      f s ≤ f b + c * (b - s) := by
    by_contra hnot
    have hlt := lt_of_not_ge hnot
    let F : ℝ → ℝ := fun t => f t + c * t
    have hcont : ContinuousOn F (Icc s b) :=
      (hf.mono (Icc_subset_Icc_left hs.1)).add
        (continuousOn_const.mul continuousOn_id)
    obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr hs.2) hcont
    have htb := hmin (show b ∈ Icc s b from ⟨hs.2, le_rfl⟩)
    change f t + c * t ≤ f b + c * b at htb
    have hst : s < t := lt_of_le_of_ne ht.1 (by
      intro heq
      subst t
      nlinarith)
    have hft : f t < R := by
      have hca := mul_le_mul_of_nonneg_left (hs.1.trans ht.1) (hC.trans hc.le)
      nlinarith
    obtain ⟨ρ, d, heq, hupper, hd, hdC⟩ :=
      hsupport t ⟨hs.1.trans_lt hst, ht.2⟩ hft
    have hlocal : IsLocalMinOn (fun r => ρ r + c * r) (Icc s t) t := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hminr := hmin (show r ∈ Icc s b from ⟨hr.1, hr.2.trans ht.2⟩)
      have hρr := hupper r ⟨hs.1.trans hr.1, hr.2⟩
      change f t + c * t ≤ f r + c * r at hminr
      rw [heq]
      linarith
    have hcone : s - t ∈ posTangentConeAt (Icc s t) t :=
      sub_mem_posTangentConeAt_of_segment_subset
        ((convex_Icc s t).segment_subset ⟨hst.le, le_rfl⟩ ⟨le_rfl, hst.le⟩)
    have hder := hlocal.hasFDerivWithinAt_nonneg
      (hd.add ((hasDerivAt_id t).const_mul c)).hasDerivWithinAt.hasFDerivWithinAt hcone
    change (s - t) * (d + c * 1) ≥ 0 at hder
    nlinarith [mul_neg_of_neg_of_pos (sub_neg.mpr hst)
      (show 0 < d + c by linarith)]
  have hlim : Tendsto (fun c : ℝ => f b + c * (b - s)) (𝓝[>] C)
      (𝓝 (f b + C * (b - s))) :=
    (by fun_prop : Continuous (fun c : ℝ => f b + c * (b - s))).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  have hnear : ∀ᶠ c : ℝ in 𝓝 C, f b + c * (b - a) < R :=
    (by fun_prop : Continuous (fun c : ℝ => f b + c * (b - a))).continuousAt.eventually_lt_const hgap
  filter_upwards [self_mem_nhdsWithin, hnear.filter_mono nhdsWithin_le_nhds] with c hc hcap
  exact hrate c hc hcap

theorem terminal_closedBall_distance_bound
    {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) M J)
    {a b r r₀ Λ scale : ℝ} (hm : 0 < m) (hab : a ≤ b)
    (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hRic : ∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 (m + 1)) x,
      0 ≤ (F.connection t).ricci x v v)
    (p : M) (hΛ : 0 ≤ Λ) (hscale : 0 < scale) (hr₀ : 0 ≤ r₀)
    (hupper : ∀ t ∈ Icc a b, ∀ x ∈ (F.metric t).ball p r,
      ∀ v : TangentSpace (𝓡 (m + 1)) x,
        (F.connection t).ricci x v v ≤ Λ * (F.metric t).inner x v v)
    (hgap : r₀ + (4 * ((m + 1 : ℕ) : ℝ) * scale + 8 * Λ / scale) * (b - a) < r) :
    ∀ s ∈ Icc a b, ∀ x : M, (F.metric b).edist p x ≤ ENNReal.ofReal r₀ →
      ((F.metric s).edist p x).toReal ≤
        r₀ + (4 * ((m + 1 : ℕ) : ℝ) * scale + 8 * Λ / scale) * (b - s) ∧
      x ∈ (F.metric s).ball p r := by
  let C := 4 * ((m + 1 : ℕ) : ℝ) * scale + 8 * Λ / scale
  have hCnonneg : 0 ≤ C := by dsimp only [C]; positivity
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  intro s hs x hx
  have hxb : (F.metric b).edist p x ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
  have hfinite (t : ℝ) (ht : t ∈ Icc a b) : (F.metric t).edist p x ≠ ⊤ :=
    edist_ne_top_of_terminal_of_ricci_nonneg hC F hab hJ (hcomplete b hb)
      hRic p x hxb ht
  have hterminal : ((F.metric b).edist p x).toReal ≤ r₀ := by
    simpa only [ENNReal.toReal_ofReal hr₀] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hx
  have hr : 0 < r := lt_of_le_of_lt
    (add_nonneg hr₀ (mul_nonneg hCnonneg (sub_nonneg.mpr hab))) hgap
  have hbound : ((F.metric s).edist p x).toReal ≤
      ((F.metric b).edist p x).toReal + C * (b - s) := by
    by_cases hpx : p = x
    · subst x
      have hself (t : ℝ) : (F.metric t).edist p p = 0 := by
        let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
          ⟨(F.metric t).toRiemannianMetric⟩
        simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
      simp only [hself, ENNReal.toReal_zero, zero_add]
      exact mul_nonneg hCnonneg (sub_nonneg.mpr hs.2)
    apply le_terminal_add_of_upper_support (R := r) hCnonneg
      (f := fun t => ((F.metric t).edist p x).toReal) ?_ ?_ ?_ s hs
    · intro t ht
      exact (continuousWithinAt_toReal_edist_of_ricci_nonneg_of_finite hC F hJ
        (hcomplete b hb) hRic p (p := (t, x)) ht (hfinite a ha)).comp
          (f := fun q : ℝ => (q, x))
          (continuousWithinAt_id.prodMk continuousWithinAt_const)
          (fun q hq => ⟨hq, mem_univ _⟩)
    · dsimp only [C] at ⊢
      linarith
    · intro t ht hdist
      have ht' : t ∈ Icc a b := Ioc_subset_Icc_self ht
      have hxball : x ∈ (F.metric t).ball p r := by
        change (F.metric t).edist p x < ENNReal.ofReal r
        rw [← ENNReal.ofReal_toReal (hfinite t ht')]
        exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr hdist
      obtain ⟨U, ρ, _, hxU, _, heq, hmajor, _, _, hd, hlower⟩ :=
        F.exists_distance_spacetime_upper_support_of_finite (hJ ht') hm
          (hcomplete t ht') (hRic t ht') hΛ hscale p x hxball hpx (hupper t ht')
      exact ⟨fun q => ρ q x, _, heq, fun q _ => hmajor q x hxU, hd.hasDerivAt, hlower⟩
  have hbound' : ((F.metric s).edist p x).toReal ≤ r₀ + C * (b - s) := by
    linarith
  refine ⟨hbound', ?_⟩
  have hrad : r₀ + C * (b - s) < r := by
    have h := mul_le_mul_of_nonneg_left (sub_le_sub_left hs.1 b) hCnonneg
    change r₀ + C * (b - a) < r at hgap
    linarith
  change (F.metric s).edist p x < ENNReal.ofReal r
  rw [← ENNReal.ofReal_toReal (hfinite s hs)]
  exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr (hbound'.trans_lt hrad)

end PoincareConjecture.RicciFlow
