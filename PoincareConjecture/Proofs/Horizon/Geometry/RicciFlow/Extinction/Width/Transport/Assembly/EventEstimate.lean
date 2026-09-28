import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Assembly.Estimates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.EventBasedWidth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Chronology.Preterminal




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
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    (Syst : M59IdentificationSystem.{u})
    (X : M67ChangingWidthPath D W P K C H B A Syst.quotient hM61 hM65)
    (hwidth : M61WidthTheory.{u} Syst.quotient)
    (hcomparison : M67EventComparisonBounds D.flow (Set.Icc 0 T))
    (hwidth_eq : ∀ (s : Set.Icc (0 : ℝ) T)
      (hs : s.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice s.1).carrier)
      (hd : D.flow.parameters.delta s.1 < repairedComparisonDeltaBound D.flow.local_constants)
      (hh : D.flow.parameters.h s.1 < repairedComparisonHeightBound D.flow.local_constants)
      (eta : ℝ) (heta : 0 < eta) (t : Set.Icc (0 : ℝ) T)
      (hnear : s.1 - (X.event_transport s hs hpost hd hh eta heta).delta < t.1)
      (hbefore : t.1 < s.1)
      (hafter : (D.flow.event s.1 hs).tMinus < t.1)
      (hJ : Disjoint D.flow.surgery_times (Set.Ioc (D.flow.event s.1 hs).tMinus t.1)),
      let E := (X.event_transport s hs hpost hd hh eta heta).transport
        t hnear hbefore hafter hJ
      m61BasedClassWidth Syst.quotient E.pre.metric (P.component t).basepoint E.pre.alpha =
          X.width t ∧
        m61BasedClassWidth Syst.quotient E.post.metric
          (H.event_input s hs hpost).child.basepoint E.post.alpha = X.width s)

include hwidth hcomparison hwidth_eq



theorem m67_event_factor_bounds
    (s : Set.Icc (0 : ℝ) T) (hs : s.1 ∈ (↑P.surgery_times : Set ℝ))
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t : Set.Icc (0 : ℝ) T, s.1 - delta < t.1 → t.1 < s.1 →
        X.width s ≤ (1 + eta) ^ 2 * X.width t := by
  have hsFlow : s.1 ∈ D.flow.surgery_times := by
    rw [P.surgery_times_eq] at hs
    exact hs.1
  let hpost : Nonempty (D.flow.slice s.1).carrier :=
    ⟨(P.component s).inclusion (P.component s).basepoint⟩
  obtain ⟨hd, hh⟩ := hcomparison s.1 s.2 hsFlow
  let family := X.event_transport s hsFlow hpost hd hh eta heta
  let before := (D.flow.event s.1 hsFlow).tMinus
  have hbefore : before < s.1 := (D.flow.event s.1 hsFlow).tMinus_lt
  let delta := min family.delta (s.1 - before)
  have hdelta : 0 < delta := lt_min family.delta_pos (sub_pos.mpr hbefore)
  refine ⟨delta, hdelta, ?_⟩
  intro t hnear hlt
  have hnear' : s.1 - family.delta < t.1 := by
    have h := min_le_left family.delta (s.1 - before)
    dsimp only [delta] at hnear
    linarith
  have hafter : before < t.1 := by
    have h := min_le_right family.delta (s.1 - before)
    dsimp only [delta] at hnear
    linarith
  have hfree := m67_event_preterminal_surgery_free D.flow hsFlow
  have hJ : Disjoint D.flow.surgery_times (Set.Ioc before t.1) := by
    apply hfree.mono_right
    intro u hu
    exact ⟨hu.1, hu.2.trans_lt hlt⟩
  let E := family.transport t hnear' hlt hafter hJ
  have hbound := m67_event_based_width_transport_of_event B A Syst heta E hwidth
  obtain ⟨hpre, hpost'⟩ := hwidth_eq s hsFlow hpost hd hh eta heta t hnear' hlt hafter hJ
  change m61BasedClassWidth Syst.quotient E.pre.metric (P.component t).basepoint
    E.pre.alpha = X.width t at hpre
  change m61BasedClassWidth Syst.quotient E.post.metric
    (H.event_input s hsFlow hpost).child.basepoint E.post.alpha = X.width s at hpost'
  rwa [hpre, hpost'] at hbound



theorem m67_conclusion_of_event_width_calibration : M67Conclusion X :=
  m67_conclusion_of_event_factor_bounds X hwidth
    (m67_event_factor_bounds Syst X hwidth hcomparison hwidth_eq)

end PoincareConjecture
