import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Regular.Neighborhoods

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}

theorem m67_width_right_continuous
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65)
    (s : Set.Icc (0 : ℝ) T) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t : Set.Icc (0 : ℝ) T,
        s.1 ≤ t.1 → t.1 < s.1 + delta →
          |X.width t - X.width s| < epsilon := by
  by_cases hs : s.1 < T
  · obtain ⟨b, hsb, hb, hJ⟩ := m67_exists_right_regular_interval P s hs
    obtain ⟨J⟩ := X.regular_piece s.2.1 hsb hb hJ
    let s' : Set.Icc s.1 b := ⟨s.1, le_rfl, hsb.le⟩
    obtain ⟨delta, hd, hclose⟩ :=
      Metric.continuousAt_iff.mp (J.conclusion.continuous_at s') epsilon hepsilon
    refine ⟨min delta (b - s.1), lt_min hd (sub_pos.mpr hsb), ?_⟩
    intro t hst ht
    have htb : t.1 ≤ b := by
      have := min_le_right delta (b - s.1)
      linarith
    let t' : Set.Icc s.1 b := ⟨t.1, hst, htb⟩
    have hdist : dist t' s' < delta := by
      change dist t.1 s.1 < delta
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hst)]
      have := min_le_left delta (b - s.1)
      linarith
    have hwidth := hclose hdist
    have hs_eq : J.interval s' = s := Subtype.ext (J.interval_time s')
    have ht_eq : J.interval t' = t := Subtype.ext (J.interval_time t')
    rw [← J.width_agreement t', ← J.width_agreement s', ht_eq, hs_eq,
      Real.dist_eq] at hwidth
    exact hwidth
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t hst _ht
    have hts : t = s := Subtype.ext (by linarith [t.2.2])
    simpa [hts] using hepsilon

theorem m67_width_continuous_at_regular
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65)
    (s : Set.Icc (0 : ℝ) T)
    (hs : s.1 ∉ (↑P.surgery_times : Set ℝ)) : ContinuousAt X.width s := by
  apply Metric.continuousAt_iff.mpr
  intro epsilon hepsilon
  by_cases hT : 0 < T
  · obtain ⟨a, b, ha, hab, hb, hsab, hJ, rho, hrho, hnear⟩ :=
      m67_exists_regular_neighborhood P hT s hs
    obtain ⟨J⟩ := X.regular_piece ha hab hb hJ
    let s' : Set.Icc a b := ⟨s.1, hsab⟩
    obtain ⟨delta, hd, hclose⟩ :=
      Metric.continuousAt_iff.mp (J.conclusion.continuous_at s') epsilon hepsilon
    refine ⟨min delta rho, lt_min hd hrho, ?_⟩
    intro t ht
    have hdist : |t.1 - s.1| < min delta rho := by
      simpa only [Subtype.dist_eq, Real.dist_eq] using ht
    let t' : Set.Icc a b := ⟨t.1, hnear t (hdist.trans_le (min_le_right _ _))⟩
    have ht's' : dist t' s' < delta := by
      change dist t.1 s.1 < delta
      rw [Real.dist_eq]
      exact hdist.trans_le (min_le_left _ _)
    have hwidth := hclose ht's'
    have hs_eq : J.interval s' = s := Subtype.ext (J.interval_time s')
    have ht_eq : J.interval t' = t := Subtype.ext (J.interval_time t')
    rwa [← J.width_agreement t', ← J.width_agreement s', ht_eq, hs_eq] at hwidth
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t _ht
    have hts : t = s := Subtype.ext (by linarith [t.2.1, t.2.2, s.2.1, s.2.2])
    simpa [hts] using hepsilon

end PoincareConjecture
