import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RetainedChart











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46



theorem low_scalar_subset_retained_interior
    (F : SurgeryFlowData.{u}) {t L : ℝ} (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier]
    (hcap : ∀ i : Fin (F.event t hT).cap_count,
      ∀ y ∈ ((F.event t hT).caps i).carrier,
        L < (F.connection t).scalarCurvature y) :
    {y | (F.connection t).scalarCurvature y ≤ L} ⊆
      interior (F.event t hT).retained_post := by
  let event := F.event t hT
  let U : Set (F.slice t).carrier := (⋃ i, (event.caps i).carrier)ᶜ
  have hU : IsOpen U :=
    (isClosed_iUnion_of_finite (fun i => (event.caps i).carrier_compact.isClosed)).isOpen_compl
  have hret : U ⊆ event.retained_post := by
    intro y hy
    have hcover : y ∈ event.retained_post ∪ ⋃ i, (event.caps i).carrier := by
      rw [event.post_cover]
      exact mem_univ _
    exact hcover.resolve_right hy
  intro y hy
  apply interior_maximal hret hU
  intro hmem
  obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
  exact not_lt_of_ge hy (hcap i y hi)




theorem low_scalar_inverse_retained
    (F : SurgeryFlowData.{u}) {t L : ℝ} (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier]
    (hcap : ∀ i : Fin (F.event t hT).cap_count,
      ∀ y ∈ ((F.event t hT).caps i).carrier,
        L < (F.connection t).scalarCurvature y)
    {y : (F.slice t).carrier} (hy : (F.connection t).scalarCurvature y ≤ L) :
    (F.event t hT).retention.inverse y ∈ interior (F.event t hT).retained_pre ∧
      (F.event t hT).retention.map ((F.event t hT).retention.inverse y) = y := by
  have hret := low_scalar_subset_retained_interior F hT hcap hy
  let chart := M44.regionEquivalenceInteriorChart (F.event t hT).retention
  exact ⟨chart.map_target hret, chart.right_inv hret⟩

end PoincareConjecture.Proofs.M46
