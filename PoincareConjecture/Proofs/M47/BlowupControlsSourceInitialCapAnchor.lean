import PoincareConjecture.Proofs.M47.BlowupControlsCapClock
import PoincareConjecture.Proofs.M47.BlowupControlsCapSurvival
import PoincareConjecture.Proofs.M47.BlowupControlsCapScalar











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47



theorem source_initial_cap_anchor_comparison
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    {C : GeneralizedSliceCarrier.{u}} {Q b c d L rate A eta theta : ℝ}
    {V : Set C.carrier}
    (E : SurgeryFlowCylinder F C O.H Q (Icc b 0) V)
    (hV : IsOpen V) (hc : c < 0) (hb : b ∈ Icc (c - d) c)
    (hL : 0 < L) (htheta : 0 < theta)
    (hDuration : 16 * L * d ≤ rate * theta)
    (hT : O.H + b / Q ∈ F.surgery_times)
    [Nonempty (F.slice (O.H + b / Q)).carrier]
    (i : Fin (F.event (O.H + b / Q) hT).cap_count)
    (hA : F.standard_initial.cylindrical_end.radius + 5 < A)
    (x : C.carrier) (hx : x ∈ V)
    (hcap : E.forward b ⟨le_rfl, hb.2.trans hc.le⟩ x ∈
      ((F.event (O.H + b / Q) hT).caps i).carrier)
    (hscalar : (F.connection (O.H + b / Q)).scalarCurvature
      (E.forward b ⟨le_rfl, hb.2.trans hc.le⟩ x) ≤ 4 * L * Q)
    (hbound : ∀ (J : Set ℝ) (U : Set (F.slice (O.H + b / Q)).carrier)
      (f : SurgeryFlowCylinder F (F.slice (O.H + b / Q)) (O.H + b / Q)
        ((F.parameters.h (O.H + b / Q))⁻¹ ^ 2) J U)
      (initial : SurgeryCapInitialComparison F (O.H + b / Q) hT i A),
      SurgeryCapFamilyComparison F O.standard_flow A eta f initial.chart →
      ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta →
      ∀ z ∈ F.standard_initial.metric.ball 0 A,
        rate / (2 * (1 - s) * (F.parameters.h (O.H + b / Q)) ^ 2) ≤
          (F.connection ((O.H + b / Q) +
            s / ((F.parameters.h (O.H + b / Q))⁻¹ ^ 2))).scalarCurvature
              (f.forward s hs (initial.chart z)))
    (hpersist : SurgeryCapPersistenceAlternative F O (O.H + b / Q) hT i A eta theta) :
    let birth := O.H + b / Q
    let h := F.parameters.h birth
    let sigma := (c - b) / (Q * h ^ 2)
    rate / (8 * L) ≤ Q * h ^ 2 ∧
      ∃ e : SurgeryFlowCylinder F (F.slice birth) birth (h⁻¹ ^ 2)
          (Ico 0 (surgeryCapDuration birth O.H h theta))
          ((F.metric birth).ball ((F.event birth hT).caps i).tip (A * h)),
        ∃ initial : SurgeryCapInitialComparison F birth hT i A,
          SurgeryCapFamilyComparison F O.standard_flow A eta e initial.chart ∧
          (∀ hs y, y ∈ (F.metric birth).ball ((F.event birth hT).caps i).tip
            (A * h) → HEq (e.forward 0 hs y) y) ∧
          ∃ hAnchor : sigma ∈ Ico 0 (surgeryCapDuration birth O.H h theta),
            sigma ≤ theta / 2 ∧
            (⟨birth + sigma / (h⁻¹ ^ 2),
              e.forward sigma hAnchor (E.forward b ⟨le_rfl, hb.2.trans hc.le⟩ x)⟩ :
                Σ t, (F.slice t).carrier) =
              ⟨O.H + c / Q, E.forward c ⟨hb.2, hc.le⟩ x⟩ := by
  let birth := O.H + b / Q
  let h := F.parameters.h birth
  let sigma := (c - b) / (Q * h ^ 2)
  let bottom : b ∈ Icc b 0 := ⟨le_rfl, hb.2.trans hc.le⟩
  let y := E.forward b bottom x
  have hQ := E.scale_pos
  have hbNeg : b < 0 := hb.2.trans_lt hc
  have hbirth : birth < O.H := add_lt_of_neg_right _ (div_neg_of_neg_of_pos hbNeg hQ)
  have hh : 0 < h :=
    F.parameters.h_pos birth (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hsq : 0 < h ^ 2 := sq_pos_of_pos hh
  have hfloor : rate / (8 * L) ≤ Q * h ^ 2 := by
    have h := cap_birth_rescaled_height_lower O hT i htheta hA hbirth
      (show 0 < 4 * L by positivity) hbound hpersist y hcap hscalar
    convert h using 1
    ring
  have hdBound : d ≤ rate * theta / (16 * L) := by
    apply (le_div_iff₀ (show 0 < 16 * L by positivity)).mpr
    nlinarith only [hDuration]
  have hhalfBound : rate * theta / (16 * L) ≤ (theta / 2) * (Q * h ^ 2) := by
    calc
      _ = (theta / 2) * (rate / (8 * L)) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfloor (by positivity)
  have hSigma0 : 0 ≤ sigma := div_nonneg (sub_nonneg.mpr hb.2) (mul_pos hQ hsq).le
  have hSigmaHalf : sigma ≤ theta / 2 := by
    apply (div_le_iff₀ (mul_pos hQ hsq)).mpr
    exact (show c - b ≤ d by linarith only [hb.1]).trans (hdBound.trans hhalfBound)
  have hSigmaTheta : sigma < theta := hSigmaHalf.trans_lt (by linarith only [htheta])
  have hclock : birth + sigma * h ^ 2 = O.H + c / Q := by
    dsimp only [birth, sigma]
    field_simp [hQ.ne', hsq.ne']
    ring
  have hbeforeH : birth + sigma * h ^ 2 < O.H := by
    rw [hclock]
    exact add_lt_of_neg_right _ (div_neg_of_neg_of_pos hc hQ)
  have hbeforeTheta : birth + sigma * h ^ 2 < birth + theta * h ^ 2 := by
    linarith only [mul_lt_mul_of_pos_right hSigmaTheta hsq]
  have hAnchor : sigma ∈ Ico 0 (surgeryCapDuration birth O.H h theta) := by
    refine ⟨hSigma0, ?_⟩
    change sigma < (min O.H (birth + theta * h ^ 2) - birth) / h ^ 2
    apply (lt_div_iff₀ hsq).mpr
    have hmin := lt_min hbeforeH hbeforeTheta
    linarith only [hmin]
  have hSigmaFuture : sigma ∈ Icc 0 ((O.H - birth) / h ^ 2) := by
    refine ⟨hSigma0, (le_div_iff₀ hsq).mpr ?_⟩
    linarith only [hbeforeH]
  obtain ⟨hmem, f, basedF, pointF⟩ := exists_cap_birth_cylinder E hV hbNeg h hh
  have hyV : y ∈ E.forward b bottom '' V := mem_image_of_mem _ hx
  obtain ⟨e, initial, comparison, basedE⟩ :=
    cap_persistence_of_surviving_birth_cylinder O hT i hA _ f basedF y hyV hcap hpersist
  refine ⟨hfloor, e, initial, comparison, basedE, hAnchor, hSigmaHalf, ?_⟩
  have hyU : y ∈ (F.metric birth).ball ((F.event birth hT).caps i).tip (A * h) :=
    inserted_cap_subset_persistence_ball hT i hA hcap
  have hI : Icc 0 sigma ⊆ Ico 0 (surgeryCapDuration birth O.H h theta) :=
    fun _ hr => ⟨hr.1, hr.2.trans_lt hAnchor.2⟩
  have hJ : Icc 0 sigma ⊆ Icc 0 ((O.H - birth) / h ^ 2) :=
    fun _ hr => ⟨hr.1, hr.2.trans hSigmaFuture.2⟩
  have heq := M44.cylinder_forward_eq_of_initial e f hSigma0 hI hJ y hyU hyV
    (eq_of_heq ((basedE _ _ hyU).trans (basedF _ _ hyV).symm))
  have hparam : b + Q * sigma * h ^ 2 = c := by
    dsimp only [sigma]
    field_simp [hQ.ne', hsq.ne']
    ring
  have hlast (r : ℝ) (hr : r ∈ Icc b 0) (hrc : r = c) :
      (⟨O.H + r / Q, E.forward r hr x⟩ : Σ t, (F.slice t).carrier) =
        ⟨O.H + c / Q, E.forward c ⟨hb.2, hc.le⟩ x⟩ := by
    subst r
    rfl
  have hsame : (⟨birth + sigma / (h⁻¹ ^ 2), e.forward sigma hAnchor y⟩ :
      Σ t, (F.slice t).carrier) =
        ⟨birth + sigma / (h⁻¹ ^ 2), f.forward sigma hSigmaFuture y⟩ :=
    Sigma.ext rfl (heq_of_eq heq)
  exact hsame.trans ((pointF sigma hSigmaFuture x hx).trans (hlast _ _ hparam))

end PoincareConjecture.M47
