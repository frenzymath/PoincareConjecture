import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Basic

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace Poincare.Analysis.Calculus

theorem tendstoUniformlyOn_iteratedFDerivWithin_of_interior_and_terminal
    {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ι} {I : Set ℝ} (hI : IsOpen I)
    {U : Set X} (hU : IsOpen U) {τ : ℝ} (hτ : 0 < τ)
    {f : ι → ℝ × X → E} {g ginterior gterminal : ℝ × X → E}
    (hinteriorEq : EqOn g ginterior ((I ∩ Iio 0) ×ˢ U))
    (hterminalEq : EqOn g gterminal (Icc (-τ) 0 ×ˢ U))
    (m : ℕ)
    (hinterior : ∀ K : Set (ℝ × X), IsCompact K →
      K ⊆ (I ∩ Iio 0) ×ˢ U → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (f k))
        (iteratedFDeriv ℝ m ginterior) l K)
    (hterminal : ∀ K : Set (ℝ × X), IsCompact K →
      K ⊆ Icc (-τ) 0 ×ˢ U → TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ m (f k) (Icc (-τ) 0 ×ˢ U))
        (iteratedFDerivWithin ℝ m gterminal (Icc (-τ) 0 ×ˢ U)) l K)
    {K : Set (ℝ × X)} (hK : IsCompact K)
    (hKJ : K ⊆ (I ∩ Iic 0) ×ˢ U) :
    TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m (f k) ((I ∩ Iic 0) ×ˢ U))
      (iteratedFDerivWithin ℝ m g ((I ∩ Iic 0) ×ˢ U)) l K := by
  let V := (I ∩ Iio 0) ×ˢ U
  let C := Icc (-τ) 0 ×ˢ U
  let Q := (I ∩ Iic 0) ×ˢ U
  let a : ℝ := -τ / 2
  let Kminus := K ∩ {z : ℝ × X | z.1 ≤ a}
  let Kplus := K ∩ {z : ℝ × X | a ≤ z.1}
  have ha0 : a < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr hτ) zero_lt_two
  have hτa : -τ < a := by
    dsimp only [a]
    rw [neg_div]
    exact neg_lt_neg (half_lt_self hτ)
  have hKm : IsCompact Kminus := hK.inter_right (isClosed_le continuous_fst continuous_const)
  have hKp : IsCompact Kplus := hK.inter_right (isClosed_le continuous_const continuous_fst)
  have hKmV : Kminus ⊆ V := fun z hz =>
    ⟨⟨(hKJ hz.1).1.1, hz.2.trans_lt ha0⟩, (hKJ hz.1).2⟩
  have hKpC : Kplus ⊆ C := fun z hz =>
    ⟨⟨(hτa.trans_le hz.2).le, (hKJ hz.1).1.2⟩, (hKJ hz.1).2⟩
  have hV : IsOpen V := (hI.inter isOpen_Iio).prod hU
  have hVQ : V ⊆ Q := fun z hz =>
    ⟨⟨hz.1.1, (show z.1 < (0 : ℝ) from hz.1.2).le⟩, hz.2⟩
  have hminusJet (h : ℝ × X → E) (z : ℝ × X) (hz : z ∈ Kminus) :
      iteratedFDerivWithin ℝ m h Q z = iteratedFDeriv ℝ m h z := by
    rw [← iteratedFDerivWithin_univ]
    exact iteratedFDerivWithin_congr_set
      (Filter.eventuallyEq_univ.mpr (mem_of_superset (hV.mem_nhds (hKmV hz)) hVQ)) m
  have hminusLimit (z : ℝ × X) (hz : z ∈ Kminus) :
      iteratedFDerivWithin ℝ m g Q z = iteratedFDeriv ℝ m ginterior z := by
    rw [hminusJet g z hz]
    have hnear : g =ᶠ[𝓝 z] ginterior := by
      filter_upwards [hV.mem_nhds (hKmV hz)] with y hy
      exact hinteriorEq hy
    exact (hnear.iteratedFDeriv ℝ m).self_of_nhds
  have hminus : TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m (f k) Q)
      (iteratedFDerivWithin ℝ m g Q) l Kminus := by
    apply ((hinterior Kminus hKm hKmV).congr ?_).congr_right ?_
    · exact Eventually.of_forall fun k z hz => (hminusJet (f k) z hz).symm
    · exact fun z hz => (hminusLimit z hz).symm
  have hterminalJet (h : ℝ × X → E) (z : ℝ × X) (hz : z ∈ Kplus) :
      iteratedFDerivWithin ℝ m h C z = iteratedFDerivWithin ℝ m h Q z := by
    apply iteratedFDerivWithin_congr_set _ m
    have hnear : (I ∩ Ioi (-τ)) ×ˢ (univ : Set X) ∈ 𝓝 z :=
      ((hI.inter isOpen_Ioi).prod isOpen_univ).mem_nhds
        ⟨⟨(hKJ hz.1).1.1, hτa.trans_le hz.2⟩, mem_univ _⟩
    filter_upwards [hnear] with w hw
    apply propext
    change ((-τ ≤ w.1 ∧ w.1 ≤ 0) ∧ w.2 ∈ U) ↔
      ((w.1 ∈ I ∧ w.1 ≤ 0) ∧ w.2 ∈ U)
    exact ⟨fun h => ⟨⟨hw.1.1, h.1.2⟩, h.2⟩,
      fun h => ⟨⟨hw.1.2.le, h.1.2⟩, h.2⟩⟩
  have hplus : TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m (f k) Q)
      (iteratedFDerivWithin ℝ m g Q) l Kplus := by
    apply ((hterminal Kplus hKp hKpC).congr ?_).congr_right ?_
    · exact Eventually.of_forall fun k z hz => hterminalJet (f k) z hz
    · intro z hz
      exact (iteratedFDerivWithin_congr hterminalEq (hKpC hz) m).symm.trans
        (hterminalJet g z hz)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hminus) ε hε,
    (Metric.tendstoUniformlyOn_iff.mp hplus) ε hε] with k hkm hkp z hz
  by_cases hza : z.1 ≤ a
  · exact hkm z ⟨hz, hza⟩
  · exact hkp z ⟨hz, (lt_of_not_ge hza).le⟩

end Poincare.Analysis.Calculus
