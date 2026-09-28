import PoincareConjecture.Proofs.M47.CanonicalNeckCapIncluded











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.M47





theorem source_search_cap_stop_persistence
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    {C : GeneralizedSliceCarrier.{u}} {origin scale a : ℝ}
    {U : Set C.carrier} (E : SurgeryFlowCylinder F C origin scale (Icc a 0) U)
    (ha : a < 0)
    (hbirthH : origin + a / scale < O.H)
    {A eta theta : ℝ}
    (hT : origin + a / scale ∈ F.surgery_times)
    [Nonempty (F.slice (origin + a / scale)).carrier]
    (i : Fin (F.event (origin + a / scale) hT).cap_count)
    (hA : F.standard_initial.cylindrical_end.radius + 5 < A)
    (hpersist : SurgeryCapPersistenceAlternative F O (origin + a / scale)
      hT i A eta theta)
    (hmargin : (O.H - (origin + a / scale)) /
      (F.parameters.h (origin + a / scale)) ^ 2 < theta)
    {V : Set (F.slice (origin + a / scale)).carrier}
    (f : SurgeryFlowCylinder F (F.slice (origin + a / scale))
      (origin + a / scale) ((F.parameters.h (origin + a / scale))⁻¹ ^ 2)
      (Icc 0 ((O.H - (origin + a / scale)) /
        (F.parameters.h (origin + a / scale)) ^ 2)) V)
    (hfbased : ∀ hs y, y ∈ V → HEq (f.forward 0 hs y) y)
    (x : C.carrier)
    (hyV : E.forward a ⟨le_rfl, ha.le⟩ x ∈ V)
    (hycap : E.forward a ⟨le_rfl, ha.le⟩ x ∈
      ((F.event (origin + a / scale) hT).caps i).carrier) :
    let birth := origin + a / scale
    let h := F.parameters.h birth
    let d := (O.H - birth) / h ^ 2
    0 < d ∧ d < theta ∧
      ∃ closed : SurgeryFlowCylinder F (F.slice birth) birth (h⁻¹ ^ 2)
          (Ico 0 d)
          ((F.metric birth).ball ((F.event birth hT).caps i).tip (A * h)),
        ∃ initial : SurgeryCapInitialComparison F birth hT i A,
          SurgeryCapFamilyComparison F O.standard_flow A eta closed initial.chart ∧
          (∀ hs z, z ∈ (F.metric birth).ball
              ((F.event birth hT).caps i).tip (A * h) →
            HEq (closed.forward 0 hs z) z) := by
  let birth : ℝ := origin + a / scale
  let h : ℝ := F.parameters.h birth
  let d : ℝ := (O.H - birth) / h ^ 2
  have hbirth : birth < O.H := by
    simpa only [birth] using hbirthH
  have hh : 0 < h := by
    dsimp only [h]
    exact F.parameters.h_pos birth
      (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hd : 0 < d := by
    dsimp only [d]
    exact div_pos (sub_pos.mpr hbirth) (sq_pos_of_pos hh)
  have hmargin' : d < theta := by
    simpa only [d, birth, h] using hmargin
  have hmargin'' : (O.H - birth) / h ^ 2 < theta := by
    simpa only [d] using hmargin'
  obtain ⟨closed, initial, hcomparison, hclosedBased⟩ :=
    Proofs.M47.capPersistence_persists_to_horizon O hT i hA V f hfbased
      (E.forward a ⟨le_rfl, ha.le⟩ x) hyV hycap hmargin'' hpersist
  refine ⟨hd, hmargin', ?_⟩
  exact ⟨closed, initial, hcomparison, hclosedBased⟩

end PoincareConjecture.M47
