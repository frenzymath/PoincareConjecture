import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Branch








set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem RepairedPreterminalSlab.start_nonempty
    {F : SurgeryFlowData.{u}} {T : ℝ} (A : RepairedPreterminalSlab F T) :
    Nonempty (F.slice A.start).carrier := by
  obtain ⟨t, ht, x, hx⟩ := A.curvature_unbounded 0 A.start A.start_lt
  exact ⟨x⟩


theorem RepairedContinuationInput.slices_nonempty
    {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)
    (t : ℝ) (ht : t ∈ F.time_domain) : Nonempty (F.slice t).carrier := by
  classical
  have htT : t < T := (I.time_domain_eq ▸ ht).2
  rcases le_total I.last_slab.start t with hst | hts
  · obtain ⟨x⟩ := I.last_slab.start_nonempty
    exact ⟨I.last_slab.identify ⟨t, hst, htT⟩ x⟩
  · by_contra hempty
    let : IsEmpty (F.slice t).carrier := not_nonempty_iff.mp hempty
    let := F.extinction_permanent t I.last_slab.start ht I.last_slab.start_mem hts
      (inferInstance : IsEmpty (F.slice t).carrier)
    obtain ⟨x⟩ := I.last_slab.start_nonempty
    exact isEmptyElim x

end PoincareConjecture
