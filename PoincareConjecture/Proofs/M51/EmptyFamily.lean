import PoincareConjecture.Proofs.M51.EmptyTail

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51Empty

variable (F : SurgeryFlowData.{u}) (a : ℝ)

noncomputable def slice (t : ℝ) : GeneralizedSliceCarrier.{u} :=
  F.slice (min t a)

noncomputable def metric (t : ℝ) : RiemannianMetric 3 (slice F a t).carrier :=
  F.metric (min t a)

noncomputable def connection (t : ℝ) : LeviCivitaData (metric F a t) :=
  F.connection (min t a)

theorem representative_mem (ha : a ∈ F.time_domain) {t : ℝ} (ht : 0 ≤ t) :
    min t a ∈ F.time_domain :=
  F.time_domain_interval.out F.zero_mem ha
    ⟨le_min ht (F.time_domain_nonnegative ha), min_le_right _ _⟩

theorem empty_after [IsEmpty (F.slice a).carrier] {t : ℝ} (ht : a ≤ t) :
    IsEmpty (slice F a t).carrier := by
  simpa only [slice, min_eq_right ht] using (inferInstance : IsEmpty (F.slice a).carrier)

theorem time_lt_of_nonempty [IsEmpty (F.slice a).carrier] {t : ℝ}
    [Nonempty (slice F a t).carrier] : t < a := by
  by_contra h
  let := empty_after F a (le_of_not_gt h)
  obtain ⟨x⟩ := (inferInstance : Nonempty (slice F a t).carrier)
  exact isEmptyElim x

theorem empty_forward (ha : a ∈ F.time_domain) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (he : IsEmpty (slice F a s).carrier) :
    IsEmpty (slice F a t).carrier :=
  F.extinction_permanent (min s a) (min t a)
    (representative_mem F a ha hs) (representative_mem F a ha (hs.trans hst))
    (min_le_min_right _ hst) he

theorem crossing_empty (ha : a ∈ F.time_domain) [IsEmpty (F.slice a).carrier]
    {p q : ℝ} (hp : 0 ≤ p) (haq : a < q)
    (hfree : Disjoint F.surgery_times (Ioc p q)) :
    IsEmpty (slice F a p).carrier := by
  by_cases hpa : p < a
  · have hJ : Icc p a ⊆ F.time_domain := fun t ht =>
      F.time_domain_interval.out F.zero_mem ha ⟨hp.trans ht.1, ht.2⟩
    let S := F.regular_slabs p a hpa hJ
      (hfree.mono_right (show Ioc p a ⊆ Ioc p q from
        fun _ ht => ⟨ht.1, ht.2.trans haq.le⟩))
    have he : IsEmpty (F.slice p).carrier :=
      ⟨fun x => isEmptyElim (S.identify ⟨a, hpa.le, le_rfl⟩ x)⟩
    simpa only [slice, min_eq_left hpa.le] using he
  · exact empty_after F a (le_of_not_gt hpa)

noncomputable def emptyFlow (A : GeneralizedSliceCarrier.{u}) [IsEmpty A.carrier]
    (g : RiemannianMetric 3 A.carrier) (C : LeviCivitaData g)
    {p q : ℝ} (hpq : p < q) : RicciFlow 3 A.carrier (Icc p q) where
  metric := fun _ => g
  connection := fun _ => C
  interval := ordConnected_Icc
  nontrivial := ⟨p, ⟨le_rfl, hpq.le⟩, q, ⟨hpq.le, le_rfl⟩, hpq.ne⟩
  smooth := by
    intro x _
    exact isEmptyElim x.2
  equation := by
    intro t ht x
    exact isEmptyElim x

end PoincareConjecture.M51Empty
