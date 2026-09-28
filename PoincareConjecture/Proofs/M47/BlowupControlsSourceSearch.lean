import PoincareConjecture.Proofs.M47.SeedRetainedSearch
import PoincareConjecture.Proofs.M47.SeedCylinderClock










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47



theorem exists_normalized_open_region_search
    (F : SurgeryFlowData.{u}) {origin Q a : ℝ} (hQ : 0 < Q) (ha : a ≤ 0)
    (hJ : Icc (origin + a / Q) origin ⊆ F.time_domain)
    (U : Set (F.slice origin).carrier) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ (b : ℝ) (hb : b ∈ Icc a 0),
      ∃ e : SurgeryFlowCylinder F (F.slice origin) origin Q (Icc b 0) U,
        (∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x) ∧
        (b = a ∨ ∃ hT : origin + b / Q ∈ F.surgery_times,
          ∀ [Nonempty (F.slice (origin + b / Q)).carrier],
            ∃ i : Fin (F.event (origin + b / Q) hT).cap_count,
              (e.forward b ⟨le_rfl, hb.2⟩ '' U ∩
                ((F.event (origin + b / Q) hT).caps i).carrier).Nonempty) := by
  obtain ⟨c, hc, f, hbased, hstop⟩ := Proofs.M47.exists_open_region_seed_search F
    (div_nonpos_of_nonpos_of_nonneg ha hQ.le) hJ U hU hne
  let b := Q * c
  have hb : b ∈ Icc a 0 := by
    constructor
    · have h := (div_le_iff₀ hQ).mp hc.1
      simpa only [b, mul_comm] using h
    · exact mul_nonpos_of_nonneg_of_nonpos hQ.le hc.2
  have hmem : MapsTo (fun s : ℝ => s / Q) (Icc b 0) (Icc c 0) := by
    intro s hs
    constructor
    · apply (le_div_iff₀ hQ).mpr
      simpa only [b, mul_comm] using hs.1
    · exact div_nonpos_of_nonpos_of_nonneg hs.2 hQ.le
  have hmono : StrictMonoOn (fun s : ℝ => s / Q) (Icc b 0) :=
    fun _ _ _ _ hst => (div_lt_div_iff_of_pos_right hQ).mpr hst
  have hclock : ∀ s ∈ Icc b 0, origin + s / Q = origin + (s / Q) / 1 :=
    fun _ _ => by rw [div_one]
  let e := Proofs.M47.seedCylinderReclock f hQ ordConnected_Icc
    (fun s : ℝ => s / Q) hmem hmono hclock
  refine ⟨b, hb, e, ?_, ?_⟩
  · intro hs x hx
    have h := Proofs.M47.seedCylinderReclock_forward_heq f hQ ordConnected_Icc
      (fun s : ℝ => s / Q) hmem hmono hclock 0 hs x
    have hzero : ∀ r (hr : r ∈ Icc c 0), r = 0 → HEq (f.forward r hr x) x := by
      intro r hr hr0
      subst r
      exact hbased hr x hx
    exact h.trans (hzero _ _ (zero_div Q))
  · rcases hstop with hstart | hstop
    · left
      dsimp only [b]
      rw [hstart, mul_div_cancel₀ _ hQ.ne']
    · right
      have hparam : b / Q = c := mul_div_cancel_left₀ c hQ.ne'
      have hbottomtime : origin + b / Q = origin + c / 1 := by
        rw [hparam, div_one]
      have hbottom :
          (⟨origin + b / Q, e.forward b ⟨le_rfl, hb.2⟩⟩ :
            (t : ℝ) × ((F.slice origin).carrier → (F.slice t).carrier)) =
          ⟨origin + c / 1, f.forward c ⟨le_rfl, hc.2⟩⟩ := by
        apply Sigma.ext hbottomtime
        apply Function.hfunext rfl
        intro x y hxy
        cases hxy
        have h := Proofs.M47.seedCylinderReclock_forward_heq f hQ ordConnected_Icc
          (fun s : ℝ => s / Q) hmem hmono hclock b ⟨le_rfl, hb.2⟩ x
        have hpoint : ∀ r (hr : r ∈ Icc c 0), r = c →
            HEq (f.forward r hr x) (f.forward c ⟨le_rfl, hc.2⟩ x) := by
          intro r hr hrc
          subst r
          rfl
        exact h.trans (hpoint _ _ hparam)
      let Contact (p : (t : ℝ) × ((F.slice origin).carrier → (F.slice t).carrier)) : Prop :=
        ∃ hT : p.1 ∈ F.surgery_times, ∀ [Nonempty (F.slice p.1).carrier],
          ∃ i : Fin (F.event p.1 hT).cap_count,
            (p.2 '' U ∩ ((F.event p.1 hT).caps i).carrier).Nonempty
      exact (congrArg Contact hbottom).mpr hstop

end PoincareConjecture.M47
