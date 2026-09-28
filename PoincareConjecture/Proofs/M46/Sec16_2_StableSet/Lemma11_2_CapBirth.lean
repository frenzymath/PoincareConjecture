import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Def16_12_CapScalarRate
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_TrackedBall











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46




theorem insertedCap_scalarLower_of_persistence
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    {t c theta A eta : ℝ} (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    (htheta : 0 < theta) (hA : F.standard_initial.cylindrical_end.radius + 5 < A)
    (htH : t < O.H)
    (hbound : ∀ (J : Set ℝ) (U : Set (F.slice t).carrier)
      (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
      (initial : SurgeryCapInitialComparison F t hT i A),
      SurgeryCapFamilyComparison F O.standard_flow A eta e initial.chart →
      ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta →
      ∀ x ∈ F.standard_initial.metric.ball 0 A,
        c / (2 * (1 - s) * (F.parameters.h t) ^ 2) ≤
          (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
            (e.forward s hs (initial.chart x)))
    (hpersist : SurgeryCapPersistenceAlternative F O t hT i A eta theta) :
    ∀ y ∈ ((F.event t hT).caps i).carrier,
      c / (2 * (F.parameters.h t) ^ 2) ≤ (F.connection t).scalarCurvature y := by
  have hApos : 0 < A := by linarith [F.standard_initial.cylindrical_end.radius_pos]
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  let U := (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)
  have hcap : ((F.event t hT).caps i).carrier ⊆ U := by
    intro y hy
    have houter := ((F.event t hT).caps i).outer_ball hy
    change (F.metric t).edist ((F.event t hT).caps i).tip y <
      ENNReal.ofReal (A * F.parameters.h t)
    apply houter.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos hApos hh)).mpr
    nlinarith
  have hbirth {J : Set ℝ}
      (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
      (initial : SurgeryCapInitialComparison F t hT i A)
      (comparison : SurgeryCapFamilyComparison F O.standard_flow A eta e initial.chart)
      (hzero : (0 : ℝ) ∈ J)
      (hidentity : ∀ h y, y ∈ U → HEq (e.forward 0 h y) y) :
      ∀ y ∈ U, c / (2 * (F.parameters.h t) ^ 2) ≤ (F.connection t).scalarCurvature y := by
    intro y hy
    have himage : initial.chart '' F.standard_initial.metric.ball 0 A = U :=
      comparison.choose_spec.2.2.2.1
    obtain ⟨z, hz, rfl⟩ := himage.symm ▸ hy
    have hphysical := hbound J U e initial comparison 0 hzero htheta.le z hz
    have he : (⟨t + 0 / ((F.parameters.h t)⁻¹ ^ 2), e.forward 0 hzero (initial.chart z)⟩ :
        Σ s, (F.slice s).carrier) = ⟨t, initial.chart z⟩ :=
      Sigma.ext (by simp) (hidentity hzero (initial.chart z) hy)
    have hscalar := congrArg
      (fun q : Σ s, (F.slice s).carrier => (F.connection q.1).scalarCurvature q.2) he
    change (F.connection (t + 0 / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
      (e.forward 0 hzero (initial.chart z)) = (F.connection t).scalarCurvature (initial.chart z)
      at hscalar
    rw [hscalar] at hphysical
    simpa only [sub_zero, mul_one] using hphysical
  intro y hy
  rcases hpersist with ⟨e, initial, comparison, hidentity⟩ |
    ⟨tPlus, htPlus, _, _, e, initial, comparison, hidentity, _⟩
  · exact hbirth e initial comparison
      ⟨le_rfl, surgeryCapDuration_pos htH hh htheta⟩ hidentity y (hcap hy)
  · exact hbirth e initial comparison
      ⟨le_rfl, div_pos (sub_pos.mpr htPlus) (sq_pos_of_pos hh)⟩ hidentity y (hcap hy)





theorem exists_insertedCap_scalarLower_tolerance {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {c theta A : ℝ}
    (hc : 0 < c) (htheta : 0 < theta) (hthetaOne : theta < 1)
    (hA : g0.cylindrical_end.radius + 5 < A)
    (hrate : ∀ s ∈ Ico 0 P.standard_cap.flow.base.lifetime, ∀ x : StandardCapSpace,
      c / (1 - s) ≤ (P.standard_cap.flow.connection s).scalarCurvature x) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 / 2 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (O : SurgeryObservation F), HEq O.standard_flow P.standard_cap.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count),
      t < O.H → SurgeryCapPersistenceAlternative F O t hT i A eta theta →
      ∀ y ∈ ((F.event t hT).caps i).carrier,
        c / (2 * (F.parameters.h t) ^ 2) ≤ (F.connection t).scalarCurvature y := by
  have hApos : 0 < A := by linarith [g0.cylindrical_end.radius_pos]
  obtain ⟨eta, heta, hetaHalf, hbound⟩ :=
    exists_actualCap_scalarRate_tolerance P hc hthetaOne hApos hrate
  refine ⟨eta, heta, hetaHalf, ?_⟩
  intro F hinitial O hmodel t hT hn i htH hpersist
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  exact insertedCap_scalarLower_of_persistence O hT i htheta (hinitial.symm ▸ hA) htH
    (fun J U e initial comparison =>
      hbound F hinitial O.standard_flow hmodel t hT hn i J U e initial comparison hh) hpersist

end PoincareConjecture.Proofs.M46
