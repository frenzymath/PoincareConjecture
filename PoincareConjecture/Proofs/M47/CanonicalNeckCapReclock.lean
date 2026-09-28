import PoincareConjecture.Proofs.M47.BlowupControlsCapClock
import PoincareConjecture.Proofs.M47.BlowupControlsCapSurvival










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_based_cap_birth_cylinder
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale a : ℝ} {U : Set C.carrier}
    (E : SurgeryFlowCylinder F C origin scale (Icc a 0) U)
    (hU : IsOpen U) (ha : a < 0) (h : ℝ) (hh : 0 < h)
    (hbased : ∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x) :
    let t := origin + a / scale
    let V := E.forward a ⟨le_rfl, ha.le⟩ '' U
    let d := (origin - t) / h ^ 2
    0 < d ∧
      ∃ f : SurgeryFlowCylinder F (F.slice t) t (h⁻¹ ^ 2) (Icc 0 d) V,
        (∀ hs x, x ∈ V → HEq (f.forward 0 hs x) x) ∧
        ∀ hd x, x ∈ U →
          HEq (f.forward d hd (E.forward a ⟨le_rfl, ha.le⟩ x)) x := by
  dsimp only
  have hscale : 0 < scale := E.scale_pos
  have hd : 0 < (origin - (origin + a / scale)) / h ^ 2 := by
    apply div_pos _ (sq_pos_of_pos hh)
    linarith only [div_neg_of_neg_of_pos ha hscale]
  obtain ⟨hmem, f, based, hpoint⟩ :=
    PoincareConjecture.M47.exists_cap_birth_cylinder E hU ha h hh
  refine ⟨hd, f, based, ?_⟩
  intro htop x hx
  let d := (origin - (origin + a / scale)) / h ^ 2
  have hparameter : a + scale * d * h ^ 2 = 0 := by
    dsimp only [d]
    field_simp [hscale.ne', hh.ne']
    ring
  have hterminal (s : ℝ) (hs : s ∈ Icc a 0) (hs0 : s = 0) :
      HEq (E.forward s hs x) x := by
    subst s
    exact hbased hs x hx
  exact (Sigma.mk.inj (hpoint d htop x hx)).2.trans
    (hterminal _ (hmem htop) hparameter)



theorem capPersistence_persists_to_horizon
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    {t A eta theta : ℝ} (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    (hA : F.standard_initial.cylindrical_end.radius + 5 < A)
    (V : Set (F.slice t).carrier)
    (f : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
      (Icc 0 ((O.H - t) / (F.parameters.h t) ^ 2)) V)
    (hbased : ∀ hs x, x ∈ V → HEq (f.forward 0 hs x) x)
    (y : (F.slice t).carrier) (hyV : y ∈ V)
    (hycap : y ∈ ((F.event t hT).caps i).carrier)
    (hmargin : (O.H - t) / (F.parameters.h t) ^ 2 < theta)
    (hpersist : SurgeryCapPersistenceAlternative F O t hT i A eta theta) :
    ∃ e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
        (Ico 0 ((O.H - t) / (F.parameters.h t) ^ 2))
        ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)),
      ∃ initial : SurgeryCapInitialComparison F t hT i A,
        SurgeryCapFamilyComparison F O.standard_flow A eta e initial.chart ∧
        ∀ hs x, x ∈ (F.metric t).ball ((F.event t hT).caps i).tip
          (A * F.parameters.h t) → HEq (e.forward 0 hs x) x := by
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  have hduration : surgeryCapDuration t O.H (F.parameters.h t) theta =
      (O.H - t) / (F.parameters.h t) ^ 2 := by
    have hupper := (div_lt_iff₀ (sq_pos_of_pos hh)).mp hmargin
    unfold surgeryCapDuration surgeryCapEnd
    rw [min_eq_left (by linarith only [hupper])]
  have hp := PoincareConjecture.M47.cap_persistence_of_surviving_birth_cylinder
    O hT i hA V f hbased y hyV hycap hpersist
  rw [hduration] at hp
  exact hp

end PoincareConjecture.Proofs.M47
