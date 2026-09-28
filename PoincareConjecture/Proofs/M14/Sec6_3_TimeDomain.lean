import PoincareConjecture.Proofs.M14.Sec6_3_InitialValueContinuation
import PoincareConjecture.Proofs.M14.Sec6_3_InitialDomain
import PoincareConjecture.Proofs.M14.Sec6_3_MaximalCoherence

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem initialValueDomain_time_mem_nhdsWithin
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ initialValueDomain G T x) :
    {t | (Z, t) ∈ initialValueDomain G T x} ∈
      𝓝[{t | 0 ≤ t ∧ T - t ^ 2 ∈ I.domain}] s := by
  rcases eq_or_lt_of_le (initialValueDomain_nonneg hs) with hs₀ | hs₀
  · subst s
    obtain ⟨U, hU, hZU, hsub⟩ := initialValueDomain_zero_relative_open hM04 hM12 hbase Z
    have hnear : {r : ℝ | (Z, r) ∈ U} ∈ 𝓝 0 :=
      (hU.preimage (continuous_const.prodMk continuous_id)).mem_nhds hZU
    filter_upwards [mem_nhdsWithin_of_mem_nhds hnear, self_mem_nhdsWithin] with r hr htime
    exact hsub ⟨hr, htime⟩
  · obtain ⟨y, ⟨P⟩⟩ := (initialValueDomain_positive_iff hs₀).mp hs
    obtain ⟨r, hsr, hnear, z, Q, _⟩ :=
      exists_initialValuePath_extension_neighborhood hM04 hM12 P
    rw [Real.sqrt_sq hs₀.le] at hsr hnear
    filter_upwards [hnear] with t ht
    exact initialValueDomain_prefix (Or.inr ⟨hs₀.trans_le hsr, z, ⟨Q⟩⟩) ht.1 ht.2

theorem initialValueCurve_time_contMDiffOn
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) (Z : G.Horizontal x) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (initialValueCurve G T x Z)
      {s | (Z, s) ∈ initialValueDomain G T x} := by
  have hreal {r : ℝ} (hr : 0 < r) {y : G.Point}
      (P : M14SquareRootInitialValuePath G T (r ^ 2) x y Z) :
      ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (initialValueCurve G T x Z) (Icc 0 r) := by
    have hC : M14SqrtParameterInterval 0 (r ^ 2) = Icc 0 r := by
      rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hr.le]
    have h := (P.square_path.smooth.mono P.square_path.interval_subset).congr
      (initialValueCurve_eqOn_square hM04 hM12 P)
    rwa [hC] at h
  intro s hs
  rcases eq_or_lt_of_le (initialValueDomain_nonneg hs) with hs₀ | hs₀
  · subst s
    by_cases hpos : ∃ r : ℝ, 0 < r ∧ (Z, r) ∈ initialValueDomain G T x
    · obtain ⟨r, hr, hsurv⟩ := hpos
      obtain ⟨y, ⟨P⟩⟩ := (initialValueDomain_positive_iff hr).mp hsurv
      have hnear : Icc 0 r ∈ 𝓝[{t | (Z, t) ∈ initialValueDomain G T x}] 0 := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)] with t ht htr
        exact ⟨initialValueDomain_nonneg ht, htr.le⟩
      exact ((hreal hr P) 0 ⟨le_rfl, hr.le⟩).mono_of_mem_nhdsWithin hnear
    · have heq : EqOn (initialValueCurve G T x Z) (fun _ => x)
          {t | (Z, t) ∈ initialValueDomain G T x} := by
        intro t ht
        have ht₀ : t = 0 := le_antisymm
          (le_of_not_gt (fun h => hpos ⟨t, h, ht⟩)) (initialValueDomain_nonneg ht)
        rw [ht₀, initialValueCurve_zero]
      exact (contMDiffOn_const (c := x)).congr heq 0 hs
  · obtain ⟨y, ⟨P⟩⟩ := (initialValueDomain_positive_iff hs₀).mp hs
    obtain ⟨r, hsr, hnear, _, Q, _⟩ :=
      exists_initialValuePath_extension_neighborhood hM04 hM12 P
    rw [Real.sqrt_sq hs₀.le] at hsr hnear
    have hwithin : Icc 0 r ∈ 𝓝[{t | (Z, t) ∈ initialValueDomain G T x}] s :=
      nhdsWithin_mono s (fun _ ht => initialValueDomain_admissible hbase ht) hnear
    exact ((hreal (hs₀.trans_le hsr) Q) s ⟨hs₀.le, hsr⟩).mono_of_mem_nhdsWithin hwithin

end PoincareConjecture.M14
