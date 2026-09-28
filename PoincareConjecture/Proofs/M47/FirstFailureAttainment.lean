import PoincareConjecture.Proofs.M47.FirstFailureCompact









set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M47



theorem firstFailure_attained_of_closed_failure
    (hC : RicciFlowCurvatureTheory.{u})
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F} {T0 r : ℝ}
    (hT0 : 0 ≤ T0) (hold : SurgeryCanonicalOn F (Ico 0 T0) r)
    (hfail : ¬ SurgeryCanonicalOn F (surgeryObservationInterval O) r)
    (hclosed : ∀ (t b : ℝ) (htb : t < b) (hJ : Icc t b ⊆ F.time_domain)
      (hfree : Disjoint F.surgery_times (Ioc t b)), t ∈ Ico T0 O.H → b < O.H →
      let S := F.regular_slabs t b htb hJ hfree
      IsClosed {z : Icc t b × (F.slice t).carrier |
        r⁻¹ ^ 2 ≤ (F.connection z.1.val).scalarCurvature (S.identify z.1 z.2) ∧
        ¬ SurgeryCanonicalControl F z.1.val (S.identify z.1 z.2)
          F.parameters.epsilon F.parameters.C}) :
    ∃ t ∈ Ico T0 O.H, t = sInf (canonicalFailureTimes F O r) ∧
      SurgeryCanonicalOn F (Ico 0 t) r ∧
      ∃ x : (F.slice t).carrier,
        r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x ∧
        ¬ SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C := by
  obtain ⟨t, ht, hpast, b, htb, hJ, hfree, hbH, x, _hscalar,
    times, points, _hanti, htimes, hpoints, hbad⟩ :=
    exists_canonicalFailureSlabLimit hC hT0 hold hfail
  let S := F.regular_slabs t b htb hJ hfree
  let t0 : Icc t b := ⟨t, le_rfl, htb.le⟩
  have htime : Tendsto times atTop (𝓝 t0) := tendsto_subtype_rng.mpr htimes
  have hpair : Tendsto (fun n => (times n, points n)) atTop (𝓝 (t0, x)) :=
    htime.prodMk_nhds hpoints
  have hlimit := (hclosed t b htb hJ hfree ht hbH).mem_of_tendsto
    hpair (Eventually.of_forall hbad)
  have hlimit' : r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x ∧
      ¬ SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C := by
    change r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature (S.identify t0 x) ∧
      ¬ SurgeryCanonicalControl F t (S.identify t0 x)
        F.parameters.epsilon F.parameters.C at hlimit
    simpa only [t0, S.initial_identify] using hlimit
  have htbad : t ∈ canonicalFailureTimes F O r :=
    ⟨⟨hT0.trans ht.1, ht.2⟩, x, hlimit'⟩
  have hbound : ∀ s ∈ canonicalFailureTimes F O r, t ≤ s :=
    canonicalFailureTimes_lower_bound hpast
  have hinf : t = sInf (canonicalFailureTimes F O r) :=
    le_antisymm (le_csInf ⟨t, htbad⟩ hbound) (csInf_le ⟨t, hbound⟩ htbad)
  exact ⟨t, ht, hinf, hpast, x, hlimit'⟩

end PoincareConjecture.Proofs.M47
