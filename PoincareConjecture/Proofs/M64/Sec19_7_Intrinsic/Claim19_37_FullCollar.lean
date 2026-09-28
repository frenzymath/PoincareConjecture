import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalPeriodicity














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

private theorem glue_periodic_arc_collars
    {u : ℝ × ℝ → AnnulusCoordinates}
    (hperiod : ∀ t ∈ Icc (0 : ℝ) 1,
      Function.Periodic (fun a => u (a, t)) rampPeriod)
    (hcollar : ∀ a b : ℝ, b - a < rampPeriod →
      ∃ r : ℝ, 0 < r ∧ InjOn u (Icc a b ×ˢ Icc (-r) r)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      InjOn u (Ico 0 rampPeriod ×ˢ Icc 0 r) := by
  have hT : 0 < rampPeriod := by unfold rampPeriod; positivity
  obtain ⟨r₀, hr₀, hi₀⟩ := hcollar 0 (3 * rampPeriod / 4) (by linarith)
  obtain ⟨r₁, hr₁, hi₁⟩ := hcollar (rampPeriod / 4) rampPeriod (by linarith)
  obtain ⟨r₂, hr₂, hi₂⟩ := hcollar (-rampPeriod / 4) (rampPeriod / 2) (by linarith)
  let r := min r₀ (min r₁ (min r₂ 1))
  have hr : 0 < r := lt_min hr₀ (lt_min hr₁ (lt_min hr₂ zero_lt_one))
  have hr0 : r ≤ r₀ := min_le_left _ _
  have hr1 : r ≤ r₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hr2 : r ≤ r₂ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrone : r ≤ 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have ht0 {t : ℝ} (ht : t ∈ Icc 0 r) : t ∈ Icc (-r₀) r₀ :=
    ⟨by linarith [ht.1], ht.2.trans hr0⟩
  have ht1 {t : ℝ} (ht : t ∈ Icc 0 r) : t ∈ Icc (-r₁) r₁ :=
    ⟨by linarith [ht.1], ht.2.trans hr1⟩
  have ht2 {t : ℝ} (ht : t ∈ Icc 0 r) : t ∈ Icc (-r₂) r₂ :=
    ⟨by linarith [ht.1], ht.2.trans hr2⟩
  have hordered : ∀ x ∈ Ico 0 rampPeriod, ∀ y ∈ Ico 0 rampPeriod,
      x ≤ y → ∀ t ∈ Icc 0 r, ∀ s ∈ Icc 0 r,
      u (x, t) = u (y, s) → (x, t) = (y, s) := by
    intro x hx y hy hxy t ht s hs heq
    by_cases hy0 : y ≤ 3 * rampPeriod / 4
    · exact hi₀ ⟨⟨hx.1, hxy.trans hy0⟩, ht0 ht⟩
        ⟨⟨hy.1, hy0⟩, ht0 hs⟩ heq
    by_cases hx1 : rampPeriod / 4 ≤ x
    · exact hi₁ ⟨⟨hx1, hx.2.le⟩, ht1 ht⟩
        ⟨⟨hx1.trans hxy, hy.2.le⟩, ht1 hs⟩ heq
    have hwrap : u (y, s) = u (y - rampPeriod, s) := by
      simpa only [sub_add_cancel] using
        hperiod s ⟨hs.1, hs.2.trans hrone⟩ (y - rampPeriod)
    have hcollide := hi₂
      (show (x, t) ∈ Icc (-rampPeriod / 4) (rampPeriod / 2) ×ˢ Icc (-r₂) r₂ from
        ⟨⟨by linarith [hx.1], by linarith⟩, ht2 ht⟩)
      (show (y - rampPeriod, s) ∈
          Icc (-rampPeriod / 4) (rampPeriod / 2) ×ˢ Icc (-r₂) r₂ from
        ⟨⟨by linarith, by linarith [hy.2]⟩, ht2 hs⟩)
      (heq.trans hwrap)
    have hxwrap := congrArg Prod.fst hcollide
    linarith [hx.1, hy.2]
  refine ⟨r, hr, hrone, ?_⟩
  rintro ⟨x, t⟩ ⟨hx, ht⟩ ⟨y, s⟩ ⟨hy, hs⟩ heq
  rcases le_total x y with hxy | hyx
  · exact hordered x hx y hy hxy t ht s hs heq
  · exact (hordered y hy x hx hyx s hs t ht heq.symm).symm




theorem m64Intrinsic_exists_embedded_full_normal_collar (N : IntrinsicAnnulus) :
    ∃ (G : RiemannianMetric 2 AnnulusCoordinates)
      (normal : ℝ → AnnulusCoordinates) (u : ℝ × ℝ → AnnulusCoordinates),
      (∀ p ∈ standardAnnulusDomain,
        G.euclideanCoefficients =ᶠ[𝓝 p] N.metric.euclideanCoefficients) ∧
      ContDiff ℝ ∞ normal ∧ ContDiff ℝ ∞ u ∧
      (∀ a, N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a) (normal a) = 1 ∧
        N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a)
          (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) a) = 0 ∧
        0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (normal a)) ∧
      (∀ a, u (a, 0) = intrinsicAnnulusBoundary 1 a) ∧
      (∀ a, HasDerivAt (fun t => u (a, t)) (normal a) 0) ∧
      (∀ a, G.IsGeodesicOn (fun t => u (a, t)) (Icc (0 : ℝ) 1)) ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
        InjOn u (Ico 0 rampPeriod ×ˢ Icc 0 r) := by
  obtain ⟨G, normal, u, hG, hn, hu, hnormal, hboundary, hvelocity, hgeo, hcollar⟩ :=
    m64Intrinsic_exists_embedded_normal_arc_collars N
  refine ⟨G, normal, u, hG, hn, hu, hnormal, hboundary, hvelocity, hgeo, ?_⟩
  apply glue_periodic_arc_collars _ hcollar
  intro t ht
  exact m64Intrinsic_normal_map_periodic G (m64Intrinsic_inward_normal_periodic N hnormal)
    hboundary hvelocity hgeo ht

end PoincareConjecture
