import PoincareConjecture.Proofs.M51.EmptyFamily









set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M51Empty

variable (F : SurgeryFlowData.{u}) {a : ℝ} (ha : a ∈ F.time_domain)
    [IsEmpty (F.slice a).carrier]

include ha in
theorem maximality (p q : ℝ) (hp : 0 ≤ p)
    (hstart : p = 0 ∨ p ∈ F.surgery_times) (hpq : p < q)
    (hfree : Disjoint F.surgery_times (Ioo p q))
    [Nonempty (slice F a p).carrier]
    (hend : q ∈ F.surgery_times ∨ q ∉ Ici 0) :
    ∀ L s : ℝ, s < q → ∃ t ∈ Ioo (max p s) q,
      ∃ x : (slice F a t).carrier, L < (connection F a t).curvatureTensorNorm x := by
  have hq : q ∈ F.surgery_times := hend.resolve_right
    (fun h => h (hp.trans hpq.le))
  have hqa := F.surgeryTime_le_empty ha hq
  have hpa : p ≤ a := hpq.le.trans hqa
  have hpD : p ∈ F.time_domain :=
    F.time_domain_interval.out F.zero_mem ha ⟨hp, hpa⟩
  have hOld : Ico p q ⊆ F.time_domain := fun t ht =>
    F.time_domain_interval.out F.zero_mem ha ⟨hp.trans ht.1, ht.2.le.trans hqa⟩
  let : Nonempty (F.slice p).carrier := by
    simpa only [slice, min_eq_left hpa] using
      (inferInstance : Nonempty (slice F a p).carrier)
  intro L s hs
  obtain ⟨t, ht, x, hx⟩ := F.maximal_intervals p q hpD hstart hpq hOld hfree
    (Or.inl hq) L s hs
  refine ⟨t, ht, ?_⟩
  change ∃ x : (F.slice (min t a)).carrier,
    L < (F.connection (min t a)).curvatureTensorNorm x
  rw [min_eq_left (ht.2.le.trans hqa)]
  exact ⟨x, hx⟩

end PoincareConjecture.M51Empty
