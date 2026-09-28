import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CapBirth

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M47

theorem exists_blowupCap_scalarRate_tolerance {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : ℝ, 0 < A → ∀ theta : ℝ, theta < 1 →
      ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 / 2 ∧
        ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
          (O : SurgeryObservation F),
          HEq O.standard_flow P.standard_cap.flow →
          ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
            (i : Fin (F.event t hT).cap_count) (J : Set ℝ)
            (U : Set (F.slice t).carrier)
            (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
            (initial : SurgeryCapInitialComparison F t hT i A),
            SurgeryCapFamilyComparison F O.standard_flow A eta e initial.chart →
            0 < F.parameters.h t → ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta →
            ∀ x ∈ F.standard_initial.metric.ball 0 A,
              c / (2 * (1 - s) * (F.parameters.h t) ^ 2) ≤
                (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
                  (e.forward s hs (initial.chart x)) := by
  obtain ⟨c, hc, hrate⟩ := (Classical.choice P.standard_cap_uniqueness).scalar_lower_bound
  refine ⟨c, hc, ?_⟩
  intro A hA theta htheta
  obtain ⟨eta, heta, hetaHalf, hbound⟩ :=
    Proofs.M46.exists_actualCap_scalarRate_tolerance P hc htheta hA hrate
  refine ⟨eta, heta, hetaHalf, ?_⟩
  intro F hinitial O hmodel
  exact hbound F hinitial O.standard_flow hmodel

theorem cap_birth_rescaled_height_lower
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    {t c theta A eta Q D : ℝ} (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    (htheta : 0 < theta) (hA : F.standard_initial.cylindrical_end.radius + 5 < A)
    (htH : t < O.H) (hD : 0 < D)
    (hbound : ∀ (J : Set ℝ) (U : Set (F.slice t).carrier)
      (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
      (initial : SurgeryCapInitialComparison F t hT i A),
      SurgeryCapFamilyComparison F O.standard_flow A eta e initial.chart →
      ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta →
      ∀ x ∈ F.standard_initial.metric.ball 0 A,
        c / (2 * (1 - s) * (F.parameters.h t) ^ 2) ≤
          (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
            (e.forward s hs (initial.chart x)))
    (hpersist : SurgeryCapPersistenceAlternative F O t hT i A eta theta)
    (y : (F.slice t).carrier) (hy : y ∈ ((F.event t hT).caps i).carrier)
    (hscalar : (F.connection t).scalarCurvature y ≤ D * Q) :
    c / (2 * D) ≤ Q * (F.parameters.h t) ^ 2 := by
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hbirth := Proofs.M46.insertedCap_scalarLower_of_persistence O hT i
    htheta hA htH hbound hpersist y hy
  have hlower := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
    (sq_pos_of_pos hh))).mp (hbirth.trans hscalar)
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hD)).mpr
  nlinarith

end PoincareConjecture.M47
