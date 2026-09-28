import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingNearby
import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingBuffer
import PoincareConjecture.Proofs.M47.BlowupControlsSourceRestriction











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47




theorem exists_source_standard_evolving_neck_canonical_neighborhood
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    {theta v gamma epsilon : ℝ} (C : ℝ) (htheta : theta < 1)
    (hv : v ∈ Icc 0 theta) {z : StandardCapSpace}
    (N : StandardEvolvingNeck standard.atlas standard.flow v gamma z
      (Ioc (-(1 + gamma)) 0))
    (hge : gamma < epsilon) (hepsilon : epsilon < 1 / 2) :
    ∃ A0 eta0 delta : ℝ, ∃ V : Set StandardCapSpace,
      0 < A0 ∧ 0 < eta0 ∧ 0 < delta ∧ IsOpen V ∧ z ∈ V ∧
      ∀ A : ℝ, A0 ≤ A →
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ model : MaximalStandardCapFlow F.standard_initial,
        HEq model standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (_comparison : SurgeryCapFamilyComparison F model A eta e initial.chart)
        (_hh : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J),
        s ≤ theta → Icc 0 s ⊆ J → |s - v| < delta → ∀ z' ∈ V,
          SurgeryCanonicalControl F (t + s / ((F.parameters.h t)⁻¹ ^ 2))
            (e.forward s hs (initial.chart z')) epsilon C := by
  obtain ⟨A0, hA0, E, he, hD, hcenter, hmap, hsource⟩ :=
    exists_standard_evolving_neck_initial_buffer N hge hepsilon
  have hgeE : gamma ≤ E.epsilon := he.symm ▸ hge.le
  obtain ⟨eta0, delta, V, heta0, hdelta, hV, hzV, _hVsource, transfer⟩ :=
    exists_actualCap_nearby_evolving_neck standard htheta hA0 hv N E hgeE
      hmap hD hcenter hsource
  refine ⟨A0, eta0, delta, V, hA0, heta0, hdelta, hV, hzV, ?_⟩
  intro A hA F hInitial model hmodel t hT hn i J U e initial eta heta hetaSmall
    comparison hh s hs hst hJ hnear z' hz'
  obtain ⟨small, _esmall, _comparisonSmall, hchart, _hinverse⟩ :=
    restrict_cap_family_comparison i e initial comparison hA0 hA
  have hball : F.standard_initial.metric.ball 0 A0 ⊆
      F.standard_initial.metric.ball 0 A := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal hA)
  have himage : initial.chart '' F.standard_initial.metric.ball 0 A0 ⊆ U := by
    rw [← comparison.choose_spec.2.2.2.1]
    exact image_mono hball
  let esmall := e.restrict Subset.rfl e.interval_connected himage
  have comparisonSmall : SurgeryCapFamilyComparison F model A0 eta esmall small.chart := by
    obtain ⟨bound, hbound, hlifetime, hinterval, _himage, hjets⟩ := comparison
    refine ⟨bound, hbound, hlifetime, hinterval, ?_, ?_⟩
    · rw [hchart]
    · intro u hu x hx
      rw [hchart]
      exact hjets u hu x (hball hx)
  obtain ⟨N', hN'⟩ := transfer F hInitial model hmodel t hT hn i J
    (initial.chart '' F.standard_initial.metric.ball 0 A0)
    esmall small eta heta hetaSmall comparisonSmall hh s hs hst hJ hnear z' hz'
  have hpoint : N'.neck.center = e.forward s hs (initial.chart z') := by
    simpa only [hchart, esmall, SurgeryFlowCylinder.restrict_forward] using hN'
  have hcanonical : SurgeryCanonicalControl F (t + s / ((F.parameters.h t)⁻¹ ^ 2))
      (e.forward s hs (initial.chart z')) E.epsilon C :=
    SurgeryCanonicalControl.neck N' hpoint
  simpa only [he] using hcanonical

end PoincareConjecture.M47
