import PoincareConjecture.Proofs.M47.CanonicalNeckClosedScalar
import PoincareConjecture.Proofs.M47.BlowupControlsCapStop










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_strongNeck_cap_time_margin (P : M47Predecessors.{u}) {c : ℝ}
    (hc : 0 < c) :
    ∃ theta1 theta2 : ℝ, 1 / 2 < theta1 ∧ theta1 < theta2 ∧ theta2 < 1 ∧
      ∀ {F : SurgeryFlowData.{u}} (O : SurgeryObservation F) {epsilon : ℝ},
      ∀ (N : SurgeryStrongNeck F O.H epsilon), epsilon ≤ 1 / 200 →
      ∀ (U : TopologicalSpace.Opens (F.slice O.H).carrier),
        (U : Set (F.slice O.H).carrier) = N.neck.carrier →
      ∀ E : SurgeryFlowCylinder F (F.slice O.H) O.H 1
          (Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) U,
        (∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x) →
        (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
          (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0),
          ∀ x ∈ U,
            HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x) (N.cylinder.forward s hs x)) →
        let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
        let ha : a ∈ Icc a 0 :=
          ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
        let t := O.H + a / 1
        ∀ (hT : t ∈ F.surgery_times), ∀ [Nonempty (F.slice t).carrier],
        ∀ (i : Fin (F.event t hT).cap_count) (contact : U),
          E.forward a ha contact.val ∈ ((F.event t hT).caps i).carrier →
        ∀ A eta : ℝ, F.standard_initial.cylindrical_end.radius + 5 < A →
          (∀ (J : Set ℝ) (V : Set (F.slice t).carrier)
            (d : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J V)
            (initial : SurgeryCapInitialComparison F t hT i A),
            SurgeryCapFamilyComparison F O.standard_flow A eta d initial.chart →
            ∀ (s : ℝ) (hs : s ∈ J), s ≤ theta2 →
            ∀ z ∈ F.standard_initial.metric.ball 0 A,
              c / (2 * (1 - s) * (F.parameters.h t) ^ 2) ≤
                (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
                  (d.forward s hs (initial.chart z))) →
          SurgeryCapPersistenceAlternative F O t hT i A eta theta2 →
          (N.neck.scale⁻¹ ^ 2)⁻¹ < theta1 * (F.parameters.h t) ^ 2 ∧
            1 < theta1 * ((N.neck.scale⁻¹ ^ 2) * (F.parameters.h t) ^ 2) := by
  obtain ⟨D, hD, hscalar⟩ := exists_strongNeck_closed_scalar_bound P
  obtain ⟨theta1, theta2, ht1, ht12, ht2, _hsigma, _hsigma1, hrate⟩ :=
    PoincareConjecture.M47.exists_cap_comparison_time_margin hc zero_le_one hD.le
  refine ⟨theta1, theta2, ht1, ht12, ht2, ?_⟩
  intro F O epsilon N hsmall U hU E hbased hagree
  dsimp only
  intro hT hn i contact hcontact A eta hA hbound hpersist
  let Q := N.neck.scale⁻¹ ^ 2
  have hQ : 0 < Q := N.cylinder.scale_pos
  have ha : -Q⁻¹ < (0 : ℝ) := neg_neg_of_pos (inv_pos.mpr hQ)
  have hrate' : 2 * Q⁻¹ * (D * Q) < c / (2 * (1 - (2 * theta1 - 1))) := by
    calc
      _ = 2 * 1 * D := by field_simp [hQ.ne']
      _ < _ := hrate
  have hscalar' (s : ℝ) (hs : s ∈ Icc (-Q⁻¹) 0) :
      (F.connection (O.H + s / 1)).scalarCurvature (E.forward s hs contact.val) ≤
        (D * Q) * 1 := by
    simpa only [mul_one] using (le_abs_self _).trans
      (hscalar N hsmall U hU E hbased hagree s hs contact)
  have hmargin := PoincareConjecture.M47.cap_stop_elapsed_lt_comparison_margin
    (T := Q⁻¹) (D := D * Q) O E U.isOpen ha hT i hA (mul_nonneg hD.le hQ.le)
    ht1 ht12 ht2 hrate' (by change -(-Q⁻¹) ≤ Q⁻¹; simpa only [neg_neg] using le_refl Q⁻¹)
    contact.val contact.property hcontact hscalar'
    hbound hpersist
  have hshort : Q⁻¹ < theta1 * (F.parameters.h (O.H + (-Q⁻¹) / 1)) ^ 2 := by
    simpa only [neg_neg, one_mul] using hmargin
  refine ⟨hshort, ?_⟩
  have hnormalized := mul_lt_mul_of_pos_left hshort hQ
  have hcancel : Q * Q⁻¹ = 1 := by field_simp
  rw [hcancel] at hnormalized
  nlinarith only [hnormalized]

end PoincareConjecture.Proofs.M47
