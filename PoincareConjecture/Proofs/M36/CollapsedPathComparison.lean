import PoincareConjecture.Proofs.M36.MetricComparison
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open scoped Manifold ContDiff ENNReal Topology

universe u v

namespace PoincareConjecture.M36

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y] [T3Space Y]

theorem edist_le_pathELength_of_avoiding_tip (g : RiemannianMetric 3 X)
    (h : RiemannianMetric 3 Y) (gamma : ℝ → X) (z : ℝ → Y) (tip : Y)
    {a b : ℝ} (hab : a ≤ b) (hz : ContinuousOn z (Set.Icc a b))
    (hsegment : ∀ c d : ℝ, a ≤ c → c ≤ d → d ≤ b →
      (∀ t ∈ Set.Icc c d, z t ≠ tip) →
      h.edist (z c) (z d) ≤ g.pathELength gamma c d) :
    h.edist (z a) (z b) ≤ g.pathELength gamma a b := by
  let Z : Set ℝ := Set.Icc a b ∩ z ⁻¹' {tip}
  by_cases hZ : Z.Nonempty
  · have hcompact : IsCompact Z := isCompact_Icc.of_isClosed_subset
      (hz.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) Set.inter_subset_left
    obtain ⟨c, hc, hmin⟩ := hcompact.exists_isLeast hZ
    obtain ⟨d, hd, hmax⟩ := hcompact.exists_isGreatest hZ
    have hac : a ≤ c := hc.1.1
    have hcb : c ≤ b := hc.1.2
    have had : a ≤ d := hd.1.1
    have hdb : d ≤ b := hd.1.2
    have hcd : c ≤ d := hmin hd
    have hctip : z c = tip := hc.2
    have hdtip : z d = tip := hd.2
    have hprefix : h.edist (z a) tip ≤ g.pathELength gamma a c := by
      by_cases hacEq : a = c
      · rw [hacEq, hctip, metric_edist_self]
        exact bot_le
      have hbound : ∀ t ∈ Set.Ico a c,
          h.edist (z a) (z t) ≤ g.pathELength gamma a c := by
        intro t ht
        have havoid : ∀ s ∈ Set.Icc a t, z s ≠ tip := by
          intro s hs heq
          have hcs : c ≤ s := hmin ⟨⟨hs.1, hs.2.trans (ht.2.le.trans hcb)⟩, heq⟩
          exact (not_lt_of_ge hcs) (hs.2.trans_lt ht.2)
        exact (hsegment a t le_rfl ht.1 (ht.2.le.trans hcb) havoid).trans
          (metric_pathELength_mono g gamma le_rfl ht.2.le)
      have hcont : ContinuousOn (fun t => h.edist (z a) (z t)) (Set.Icc a c) :=
        (metric_edist_continuous h).comp_continuousOn
          (continuousOn_const.prodMk (hz.mono (Set.Icc_subset_Icc le_rfl hcb)))
      have hlim := le_on_closure hbound
        (by simpa only [closure_Ico hacEq] using hcont) continuousOn_const
        (x := c) (by rw [closure_Ico hacEq]; exact ⟨hac, le_rfl⟩)
      simpa only [hctip] using hlim
    have hsuffix : h.edist tip (z b) ≤ g.pathELength gamma d b := by
      by_cases hdbEq : d = b
      · rw [← hdbEq, hdtip, metric_edist_self]
        exact bot_le
      have hbound : ∀ t ∈ Set.Ioc d b,
          h.edist (z t) (z b) ≤ g.pathELength gamma d b := by
        intro t ht
        have havoid : ∀ s ∈ Set.Icc t b, z s ≠ tip := by
          intro s hs heq
          have hsd : s ≤ d := hmax ⟨⟨had.trans (ht.1.le.trans hs.1), hs.2⟩, heq⟩
          exact (not_lt_of_ge hsd) (ht.1.trans_le hs.1)
        exact (hsegment t b (had.trans ht.1.le) ht.2 le_rfl havoid).trans
          (metric_pathELength_mono g gamma ht.1.le le_rfl)
      have hcont : ContinuousOn (fun t => h.edist (z t) (z b)) (Set.Icc d b) :=
        (metric_edist_continuous h).comp_continuousOn
          ((hz.mono (Set.Icc_subset_Icc had le_rfl)).prodMk continuousOn_const)
      have hlim := le_on_closure hbound
        (by simpa only [closure_Ioc hdbEq] using hcont) continuousOn_const
        (x := d) (by rw [closure_Ioc hdbEq]; exact ⟨le_rfl, hdb⟩)
      simpa only [hdtip] using hlim
    calc
      h.edist (z a) (z b) ≤ h.edist (z a) tip + h.edist tip (z b) :=
        metric_edist_triangle h _ _ _
      _ ≤ g.pathELength gamma a c + g.pathELength gamma d b := add_le_add hprefix hsuffix
      _ ≤ g.pathELength gamma a d + g.pathELength gamma d b :=
        add_le_add (metric_pathELength_mono g gamma le_rfl hcd) le_rfl
      _ = g.pathELength gamma a b := metric_pathELength_add g gamma had hdb
  · apply hsegment a b le_rfl hab le_rfl
    intro t ht heq
    exact hZ ⟨t, ht, heq⟩

theorem edist_comp_le_pathELength_off_tip (g : RiemannianMetric 3 X)
    (h : RiemannianMetric 3 Y) {f : X → Y} {U : Set X} (tip : Y)
    (hf : ContinuousOn f U)
    (hsmooth : ∀ x ∈ U, f x ≠ tip → ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hmetric : ∀ x ∈ U, f x ≠ tip → ∀ v : TangentSpace (𝓡 3) x,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
        g.inner x v v)
    {gamma : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Set.Icc a b))
    (hU : gamma '' Set.Icc a b ⊆ U) :
    h.edist (f (gamma a)) (f (gamma b)) ≤ g.pathELength gamma a b := by
  apply edist_le_pathELength_of_avoiding_tip g h gamma (f ∘ gamma) tip hab
    (hf.comp hgamma.continuousOn (Set.mapsTo_iff_image_subset.mpr hU))
  intro c d hac hcd hdb havoid
  let V : Set X := U ∩ {x | f x ≠ tip}
  apply edist_comp_le_pathELength_of_pullback_bound g h
    (U := V) (fun x hx => hsmooth x hx.1 hx.2) (fun x hx => hmetric x hx.1 hx.2)
    hcd (hgamma.mono (Set.Icc_subset_Icc hac hdb))
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨hU ⟨t, ⟨hac.trans ht.1, ht.2.trans hdb⟩, rfl⟩, havoid t ht⟩

theorem edist_le_intrinsicEDist_off_tip (g : RiemannianMetric 3 X)
    (h : RiemannianMetric 3 Y) {f : X → Y} {U : Set X} (tip : Y)
    (hf : ContinuousOn f U)
    (hsmooth : ∀ x ∈ U, f x ≠ tip → ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hmetric : ∀ x ∈ U, f x ≠ tip → ∀ v : TangentSpace (𝓡 3) x,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
        g.inner x v v) (x y : X) :
    h.edist (f x) (f y) ≤ intrinsicEDist g U x y := by
  apply le_sInf
  rintro L ⟨gamma, hgamma, hzero, hone, hU, rfl⟩
  have hle := edist_comp_le_pathELength_off_tip g h tip hf hsmooth hmetric zero_le_one hgamma hU
  simpa only [hzero, hone] using hle

end PoincareConjecture.M36
