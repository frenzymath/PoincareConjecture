import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RicciTimeGluing
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_SpatialJets

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M45

open SpacetimeBounds

theorem ricciCoefficients_timeJoin {n : ℕ} {a T b : ℝ}
    (hTb : T < b) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) {f g : ℝ × EuclideanSpace ℝ (Fin n) → MetricCoefficient n}
    (hf : ContDiffOn ℝ ∞ f (Ioc a T ×ˢ U))
    (hg : ContDiffOn ℝ ∞ g (Icc T b ×ˢ U))
    (hjoin : ∀ x ∈ U, f (T, x) = g (T, x))
    (hfinv : ∀ p ∈ Ioc a T ×ˢ U, (f p).IsInvertible)
    (hginv : ∀ p ∈ Icc T b ×ˢ U, (g p).IsInvertible)
    (hfeq : ∀ t ∈ Ioo a T, ∀ x ∈ U,
      HasDerivAt (fun s => f (s, x))
        (ricciFlowOperator n (metricTwoJet (fun y => f (t, y)) x)) t)
    (hgeq : ∀ t ∈ Ioo T b, ∀ x ∈ U,
      HasDerivAt (fun s => g (s, x))
        (ricciFlowOperator n (metricTwoJet (fun y => g (t, y)) x)) t) :
    ContDiffOn ℝ ∞ (fun p => if p.1 < T then f p else g p) (Ioo a b ×ˢ U) := by
  let B : ℝ × EuclideanSpace ℝ (Fin n) → MetricCoefficient n :=
    fun p => if p.1 < T then f p else g p
  have hsmooth : ContDiffOn ℝ ∞ B ((Ioo a b \ {T}) ×ˢ U) := by
    intro p hp
    have hne : p.1 ≠ T := by simpa only [mem_singleton_iff] using hp.1.2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := (hf.mono (prod_mono Ioo_subset_Ioc_self Subset.rfl)).contDiffAt
        ((isOpen_Ioo.prod hU).mem_nhds ⟨⟨hp.1.1.1, hlt⟩, hp.2⟩)
      have heq : B =ᶠ[𝓝 p] f := by
        filter_upwards [(continuous_fst.isOpen_preimage _ isOpen_Iio).mem_nhds hlt] with q hq
        exact if_pos hq
      exact (h.congr_of_eventuallyEq heq).contDiffWithinAt
    · have h := (hg.mono (prod_mono Ioo_subset_Icc_self Subset.rfl)).contDiffAt
        ((isOpen_Ioo.prod hU).mem_nhds ⟨⟨hgt, hp.1.1.2⟩, hp.2⟩)
      have heq : B =ᶠ[𝓝 p] g := by
        filter_upwards [(continuous_fst.isOpen_preimage _ isOpen_Ioi).mem_nhds hgt] with q hq
        exact if_neg (not_lt_of_gt hq)
      exact (h.congr_of_eventuallyEq heq).contDiffWithinAt
  have hspace (t : ℝ) (ht : t ∈ Ioo a b) : ContDiffOn ℝ ∞ (fun x => B (t, x)) U := by
    by_cases h : t < T
    · simpa only [B, if_pos h, Function.comp_def, id_eq] using hf.comp
        (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => ⟨⟨ht.1, h.le⟩, hx⟩)
    · simpa only [B, if_neg h, Function.comp_def, id_eq] using hg.comp
        (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => ⟨⟨le_of_not_gt h, ht.2.le⟩, hx⟩)
  have hjets (m : ℕ) : ContinuousOn
      (fun p => iteratedFDeriv ℝ m (fun x => B (p.1, x)) p.2) (Ioo a b ×ˢ U) :=
    (timeJoin_spatialJets hTb hU hf hg hjoin m).mono (prod_mono Ioo_subset_Ioc_self Subset.rfl)
  have hinv (p : ℝ × EuclideanSpace ℝ (Fin n)) (hp : p ∈ Ioo a b ×ˢ U) :
      (B p).IsInvertible := by
    by_cases h : p.1 < T
    · simpa only [B, if_pos h] using hfinv p ⟨⟨hp.1.1, h.le⟩, hp.2⟩
    · simpa only [B, if_neg h] using hginv p ⟨⟨le_of_not_gt h, hp.1.2.le⟩, hp.2⟩
  apply M44.contDiffOn_ricci_coefficients_off_finite isOpen_Ioo hU (finite_singleton T)
    hsmooth hspace hjets hinv
  intro t ht hnot x hx
  have hne : t ≠ T := by simpa only [mem_singleton_iff] using hnot
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have heq : (fun s => B (s, x)) =ᶠ[𝓝 t] (fun s => f (s, x)) := by
      filter_upwards [Iio_mem_nhds hlt] with s hs
      exact if_pos hs
    simpa only [B, if_pos hlt] using
      (hfeq t ⟨ht.1, hlt⟩ x hx).congr_of_eventuallyEq heq
  · have heq : (fun s => B (s, x)) =ᶠ[𝓝 t] (fun s => g (s, x)) := by
      filter_upwards [Ioi_mem_nhds hgt] with s hs
      exact if_neg (not_lt_of_gt hs)
    simpa only [B, if_neg (not_lt_of_gt hgt)] using
      (hgeq t ⟨hgt, ht.2⟩ x hx).congr_of_eventuallyEq heq

end PoincareConjecture.M45
