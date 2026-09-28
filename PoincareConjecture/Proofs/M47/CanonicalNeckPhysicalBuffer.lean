import PoincareConjecture.Proofs.M47.CanonicalNeckPhysicalClock









set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_strongNeck_buffer_or_cap
    {F : SurgeryFlowData.{u}} {T epsilon l H : ℝ}
    (N : SurgeryStrongNeck F T epsilon)
    (hl : l < T - (N.neck.scale⁻¹ ^ 2)⁻¹) (hH : T < H)
    (hJ : Ico l H ⊆ F.time_domain) :
    (∃ d b : ℝ, d < -(N.neck.scale⁻¹ ^ 2)⁻¹ ∧ 0 < b ∧
      l ≤ T + d ∧ T + b < H ∧
      ∃ E : SurgeryFlowCylinder F (F.slice T) T 1 (Icc d b) N.neck.carrier,
        (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
          (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc d b), ∀ x ∈ N.neck.carrier,
            HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x)
              (N.cylinder.forward s hs x)) ∧
        ∀ hs x, x ∈ N.neck.carrier → HEq (E.forward 0 hs x) x) ∨
    (∃ E : SurgeryFlowCylinder F (F.slice T) T 1
        (Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) N.neck.carrier,
      (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
        (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0),
        ∀ x ∈ N.neck.carrier,
          HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x) (N.cylinder.forward s hs x)) ∧
      (∀ hs x, x ∈ N.neck.carrier → HEq (E.forward 0 hs x) x) ∧
      ∃ hT : T + (-(N.neck.scale⁻¹ ^ 2)⁻¹) / 1 ∈ F.surgery_times,
        ∀ [Nonempty (F.slice (T + (-(N.neck.scale⁻¹ ^ 2)⁻¹) / 1)).carrier],
          ∃ i : Fin (F.event (T + (-(N.neck.scale⁻¹ ^ 2)⁻¹) / 1) hT).cap_count,
            (E.forward (-(N.neck.scale⁻¹ ^ 2)⁻¹)
                ⟨le_rfl, (neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le)⟩ ''
                N.neck.carrier ∩
              ((F.event (T + (-(N.neck.scale⁻¹ ^ 2)⁻¹) / 1) hT).caps i).carrier).Nonempty) := by
  let e := strongNeckPhysicalClock N
  have ha : -(N.neck.scale⁻¹ ^ 2)⁻¹ < 0 := neg_neg_of_pos (inv_pos.mpr N.cylinder.scale_pos)
  have hz : (0 : ℝ) ∈ Ioc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0 := ⟨ha, le_rfl⟩
  have hne : N.neck.carrier.Nonempty :=
    ⟨N.neck.center, N.neck.central_sphere_subset N.neck.center_on_central_sphere⟩
  have hagreement (J : Set ℝ)
      (E : SurgeryFlowCylinder F (F.slice T) T 1 J N.neck.carrier)
      (hE : ∀ s (hs : s ∈ Ioc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0)
        (hs' : s ∈ J), ∀ x ∈ N.neck.carrier, E.forward s hs' x = e.forward s hs x) :
      (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0) (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ J),
        ∀ x ∈ N.neck.carrier,
          HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x) (N.cylinder.forward s hs x)) ∧
      ∀ hs x, x ∈ N.neck.carrier → HEq (E.forward 0 hs x) x := by
    constructor
    · intro s hs hs' x hx
      exact (heq_of_eq (hE _ (strongNeckPhysicalClock_parameter N hs) hs' x hx)).trans
        (strongNeckPhysicalClock_forward N s hs _ x)
    · intro hs x hx
      exact (heq_of_eq (hE 0 hz hs x hx)).trans (strongNeckPhysicalClock_terminal N hz x hx)
  rcases exists_strictLeft_cylinder_buffer_or_cap e ha N.neck.carrier_open hne
      (by simpa only [sub_eq_add_neg] using hl) hH hJ with hbuffer | hcap
  · obtain ⟨d, b, hd, hb, hld, hbH, E, hE⟩ := hbuffer
    exact Or.inl ⟨d, b, hd, hb, hld, hbH, E, hagreement _ E hE⟩
  · obtain ⟨E, hE, hcap⟩ := hcap
    obtain ⟨hEold, hEbased⟩ := hagreement _ E hE
    exact Or.inr ⟨E, hEold, hEbased, hcap⟩

end PoincareConjecture.Proofs.M47
