import PoincareConjecture.Proofs.M34.Mathlib.ParameterSpatialDerivatives
import Mathlib.Topology.Piecewise

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

theorem continuousOn_time_ite
    {E V : Type*} [TopologicalSpace E] [TopologicalSpace V]
    {f g : ℝ × E → V} {a b c : ℝ}
    (hf : ContinuousOn f (Ioc a c ×ˢ univ))
    (hg : ContinuousOn g (Ico c b ×ˢ univ))
    (hfg : ∀ x, f (c, x) = g (c, x)) :
    ContinuousOn (fun p : ℝ × E => if p.1 < c then f p else g p) (Ioo a b ×ˢ univ) := by
  apply ContinuousOn.if
  · intro p hp
    have heq : p.1 = c := frontier_lt_subset_eq continuous_fst continuous_const hp.2
    simpa only [← heq] using hfg p.2
  · apply hf.mono
    intro p hp
    have hle : p.1 ≤ c := closure_lt_subset_le continuous_fst continuous_const hp.2
    exact ⟨⟨hp.1.1.1, hle⟩, hp.1.2⟩
  · apply hg.mono
    intro p hp
    have hle : c ≤ p.1 := by
      have hclosed : IsClosed {q : ℝ × E | ¬q.1 < c} := by
        simpa only [not_lt] using isClosed_le continuous_const continuous_fst
      have hp' := hp.2
      rw [hclosed.closure_eq] at hp'
      exact not_lt.mp hp'
    exact ⟨⟨hle, hp.1.1.2⟩, hp.1.2⟩

theorem iteratedFDeriv_time_ite
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f g : ℝ × E → V) (c : ℝ) (j : ℕ) (p : ℝ × E) :
    iteratedFDeriv ℝ j (fun x => if p.1 < c then f (p.1, x) else g (p.1, x)) p.2 =
      if p.1 < c then iteratedFDeriv ℝ j (fun x => f (p.1, x)) p.2
      else iteratedFDeriv ℝ j (fun x => g (p.1, x)) p.2 := by
  by_cases ht : p.1 < c <;> simp only [ht, if_true, if_false]

theorem continuousOn_spatialJet_time_ite
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : ℝ × E → V} {a b c : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioc a c ×ˢ univ))
    (hg : ContDiffOn ℝ ∞ g (Ico c b ×ˢ univ))
    (hfg : ∀ x, f (c, x) = g (c, x)) (j : ℕ) :
    ContinuousOn
      (fun p : ℝ × E => iteratedFDeriv ℝ j
        (fun x => if p.1 < c then f (p.1, x) else g (p.1, x)) p.2)
      (Ioo a b ×ˢ univ) := by
  have h := continuousOn_time_ite
    (hf.iteratedFDeriv_snd_of_isOpen isOpen_univ j).continuousOn
    (hg.iteratedFDeriv_snd_of_isOpen isOpen_univ j).continuousOn
    (fun x => congrArg (fun u => iteratedFDeriv ℝ j u x) (funext hfg))
  apply h.congr
  intro p _hp
  exact iteratedFDeriv_time_ite f g c j p

theorem contDiffOn_time_ite_off_time
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : ℝ × E → V} {a b c : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioc a c ×ˢ univ))
    (hg : ContDiffOn ℝ ∞ g (Ico c b ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => if p.1 < c then f p else g p)
      ((Ioo a b \ {c}) ×ˢ univ) := by
  intro p hp
  by_cases ht : p.1 < c
  · have hreg := (hf.mono (prod_mono Ioo_subset_Ioc_self (Subset.refl univ))).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨hp.1.1.1, ht⟩, hp.2⟩)
    apply ContDiffAt.contDiffWithinAt
    apply hreg.congr_of_eventuallyEq
    filter_upwards [(isOpen_Iio.preimage continuous_fst).mem_nhds ht] with q hq
    exact if_pos hq
  · have hgt : c < p.1 := lt_of_le_of_ne (not_lt.mp ht) (Ne.symm hp.1.2)
    have hreg := (hg.mono (prod_mono Ioo_subset_Ico_self (Subset.refl univ))).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨hgt, hp.1.1.2⟩, hp.2⟩)
    apply ContDiffAt.contDiffWithinAt
    apply hreg.congr_of_eventuallyEq
    filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hgt] with q hq
    exact if_neg (not_lt.mpr hq.le)
