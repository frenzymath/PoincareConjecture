import PoincareConjecture.Proofs.M33.GuardedCylinders
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction
import PoincareConjecture.Proofs.M12.GeneralizedCylinderClock
import PoincareConjecture.Definitions.Ch16.CapPersistence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

theorem exists_capPersistence_source_window
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    {t : ℝ} {hT : t ∈ F.surgery_times} [Nonempty (F.slice t).carrier]
    (i : Fin (F.event t hT).cap_count) {A eta theta : ℝ}
    (hh : 0 < F.parameters.h t) (htH : t < O.H) (htheta : 0 < theta)
    (control : SurgeryCapPersistenceAlternative F O t hT i A eta theta) :
    ∃ top : ℝ, t < top ∧ top ≤ t + theta * (F.parameters.h t) ^ 2 ∧
      ∃ e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2)
          (Ico 0 ((top - t) / (F.parameters.h t) ^ 2))
          ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)),
        ∃ initial : SurgeryCapInitialComparison F t hT i A,
          SurgeryCapFamilyComparison F O.standard_flow A eta e initial.chart ∧
          (∀ h x, x ∈ (F.metric t).ball ((F.event t hT).caps i).tip
            (A * F.parameters.h t) → HEq (e.forward 0 h x) x) ∧
          (top = O.H ∨ top = t + theta * (F.parameters.h t) ^ 2 ∨
            SurgeryBallDisappearsAt F e top) := by
  rcases control with ⟨e, initial, comparison, based⟩ |
    ⟨top, httop, _hTtop, htop, e, initial, comparison, based, disappears⟩
  · refine ⟨surgeryCapEnd t O.H (F.parameters.h t) theta, ?_, min_le_right _ _,
      e, initial, comparison, based, ?_⟩
    · exact lt_min htH (by nlinarith [mul_pos htheta (sq_pos_of_pos hh)])
    · by_cases hle : O.H ≤ t + theta * (F.parameters.h t) ^ 2
      · exact Or.inl (min_eq_left hle)
      · exact Or.inr (Or.inl (min_eq_right (le_of_not_ge hle)))
  · exact ⟨top, httop, htop.le.trans (min_le_right _ _), e, initial,
      comparison, based, Or.inr (Or.inr disappears)⟩

noncomputable def capOpenInterval (origin top h : ℝ) (htop : origin < top)
    (hh : 0 < h) : SpacetimeInterval where
  domain := Ioo 0 ((top - origin) / h ^ 2)
  ordConnected := ordConnected_Ioo
  nontrivial := by
    have hb : 0 < (top - origin) / h ^ 2 :=
      div_pos (sub_pos.mpr htop) (sq_pos_of_pos hh)
    refine ⟨((top - origin) / h ^ 2) / 3, ⟨by linarith, by linarith⟩,
      2 * ((top - origin) / h ^ 2) / 3, ⟨by linarith, by linarith⟩, ?_⟩
    linarith

theorem capOpenInterval_physical (origin top h : ℝ) (htop : origin < top)
    (hh : 0 < h) (hq : 0 < h⁻¹ ^ 2) :
    (cylinderPhysicalInterval origin (h⁻¹ ^ 2) hq
      (capOpenInterval origin top h htop hh)).domain = Ioo origin top := by
  have hsq : 0 < h ^ 2 := sq_pos_of_pos hh
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    change origin + s / (h⁻¹ ^ 2) ∈ Ioo origin top
    rw [inv_pow, div_inv_eq_mul]
    refine ⟨by nlinarith [mul_pos hs.1 hsq], ?_⟩
    have := (lt_div_iff₀ hsq).mp hs.2
    linarith
  · intro ht
    refine ⟨(t - origin) / h ^ 2, ⟨div_pos (sub_pos.mpr ht.1) hsq,
      div_lt_div_of_pos_right (sub_lt_sub_right ht.2 origin) hsq⟩, ?_⟩
    change origin + ((t - origin) / h ^ 2) / (h⁻¹ ^ 2) = t
    rw [inv_pow, div_inv_eq_mul, div_mul_cancel₀ _ hsq.ne']
    ring

theorem exists_capCylinder_test_window_lift
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {origin top T h : ℝ}
    {U : Set (F.slice origin).carrier} (hU : IsOpen U)
    (hh : 0 < h) (htop : origin < top) (hT : origin < T)
    (hwindow : Ioo origin (min T top) ⊆ H.generalized.interval)
    (e : SurgeryFlowCylinder F (F.slice origin) origin (h⁻¹ ^ 2)
      (Ico 0 ((top - origin) / h ^ 2)) U) :
    let J := capOpenInterval origin (min T top) h (lt_min hT htop) hh
    ∃ (hJI : J.domain ⊆ Ico 0 ((top - origin) / h ^ 2))
      (htime : ∀ s ∈ J.domain, origin + s / (h⁻¹ ^ 2) ∈ H.generalized.interval),
      ∃ d : GeneralizedFlowCylinder H.generalized (F.slice origin) origin
          (h⁻¹ ^ 2) J.domain U,
        (∀ s hs x, x ∈ U →
          H.history.forward (origin + s / (h⁻¹ ^ 2)) (htime s hs)
            (d.forward s hs x) = e.forward s (hJI hs) x) ∧
        (∀ s hs x, x ∈ U → ∀ v w : TangentSpace (𝓡 3) x,
          d.pullbackInner s hs x v w = e.pullbackInner s (hJI hs) x v w) := by
  dsimp only
  let J := capOpenInterval origin (min T top) h (lt_min hT htop) hh
  have hJI : J.domain ⊆ Ico 0 ((top - origin) / h ^ 2) := by
    intro s hs
    exact ⟨hs.1.le, hs.2.trans_le (div_le_div_of_nonneg_right
      (sub_le_sub_right (min_le_right T top) origin) (sq_nonneg h))⟩
  have htime : ∀ s ∈ J.domain,
      origin + s / (h⁻¹ ^ 2) ∈ H.generalized.interval := by
    intro s hs
    apply hwindow
    rw [← capOpenInterval_physical origin (min T top) h (lt_min hT htop) hh e.scale_pos]
    exact ⟨s, hs, rfl⟩
  let restricted := e.restrict hJI J.ordConnected (Subset.rfl : U ⊆ U)
  obtain ⟨d, forward, metric⟩ := H.cylinder_from_surgery_of_earlier hU htime restricted
    (fun s hs => ⟨s / 2, ⟨by linarith [hs.1], by linarith [hs.1, hs.2]⟩,
      by linarith [hs.1]⟩)
  exact ⟨hJI, htime, d, forward, metric⟩

end PoincareConjecture.Proofs.M46
