import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeJointFromCollar












set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E V : Type*} [TopologicalSpace E]





theorem joint_cylinder_whole_surface
    {B : Set V} {Q : Set E} {S : Set (E × ℝ)} {r tau epsilon : ℝ}
    (hr : 0 ≤ r) (hepsr : epsilon ≤ r) (hepstau : epsilon ≤ tau)
    (F : V × (ℝ × ℝ) → E × ℝ)
    (hheight : ∀ p ∈ B ×ˢ (Icc (-r) r ×ˢ Icc (-r) r), (F p).2 = p.2.1)
    (hsurface : ∀ p ∈ B ×ˢ (Icc (-r) r ×ˢ Icc (-r) r),
      F p ∈ S ↔ p.2.2 = 0)
    (hband : S ∩ {p | p.2 ∈ Icc (-tau) tau} ⊆
      F '' (B ×ˢ (Icc (-r) r ×ˢ Icc (-r) r)))
    (hcoreQ : ∀ v ∈ B, (F (v, (0, 0))).1 ∈ Q)
    (e : (Q ×ˢ Icc (-epsilon) epsilon : Set (E × ℝ)) ≃ₜ
      (Q ×ˢ Icc (-epsilon) epsilon))
    (heheight : ∀ p, (e p : E × ℝ).2 = (p : E × ℝ).2)
    (hecore : ∀ (p : (Q ×ˢ Icc (-epsilon) epsilon : Set (E × ℝ)))
      (v : V), v ∈ B → (p : E × ℝ).1 = (F (v, (0, 0))).1 →
        (e p : E × ℝ) = F (v, ((p : E × ℝ).2, 0))) :
    (∀ p, (e p : E × ℝ) ∈ S ↔
      (p : E × ℝ).1 ∈ (fun v => (F (v, (0, 0))).1) '' B) ∧
      S ∩ {p | p.2 ∈ Icc (-epsilon) epsilon} ⊆
        Q ×ˢ Icc (-epsilon) epsilon := by
  have hzero : (0 : ℝ) ∈ Icc (-r) r := ⟨neg_nonpos.mpr hr, hr⟩
  have hfull (y : E × ℝ) (hy : y ∈ S) (hyt : y.2 ∈ Icc (-epsilon) epsilon) :
      ∃ v ∈ B, F (v, (y.2, 0)) = y := by
    have hytau : y.2 ∈ Icc (-tau) tau :=
      ⟨(neg_le_neg hepstau).trans hyt.1, hyt.2.trans hepstau⟩
    obtain ⟨p, hp, hpy⟩ := hband ⟨hy, hytau⟩
    have hpz : p.2.2 = 0 := (hsurface p hp).mp (hpy.symm ▸ hy)
    have hpt : p.2.1 = y.2 := (hheight p hp).symm.trans (congrArg Prod.snd hpy)
    refine ⟨p.1, hp.1, ?_⟩
    have hpform : p = (p.1, (y.2, 0)) := Prod.ext rfl (Prod.ext hpt hpz)
    rwa [hpform] at hpy
  constructor
  · intro p
    constructor
    · intro hpS
      have htime : (e p : E × ℝ).2 ∈ Icc (-epsilon) epsilon :=
        (e p).property.2
      obtain ⟨v, hv, hve⟩ := hfull (e p) hpS htime
      let q : (Q ×ˢ Icc (-epsilon) epsilon : Set (E × ℝ)) :=
        ⟨((F (v, (0, 0))).1, (p : E × ℝ).2), hcoreQ v hv, p.property.2⟩
      have heq : e q = e p := by
        apply Subtype.ext
        rw [hecore q v hv rfl]
        change F (v, ((p : E × ℝ).2, 0)) = (e p : E × ℝ)
        simpa only [heheight p] using hve
      have hqp : q = p := e.injective heq
      refine ⟨v, hv, ?_⟩
      exact congrArg (fun x : (Q ×ˢ Icc (-epsilon) epsilon : Set (E × ℝ)) =>
        (x : E × ℝ).1) hqp
    · rintro ⟨v, hv, hvp⟩
      rw [hecore p v hv hvp.symm]
      exact (hsurface (v, ((p : E × ℝ).2, 0))
        ⟨hv, ⟨(neg_le_neg hepsr).trans p.property.2.1,
        p.property.2.2.trans hepsr⟩, hzero⟩).mpr rfl
  · rintro y ⟨hy, hyt⟩
    obtain ⟨v, hv, hvy⟩ := hfull y hy hyt
    let p : (Q ×ˢ Icc (-epsilon) epsilon : Set (E × ℝ)) :=
      ⟨((F (v, (0, 0))).1, y.2), hcoreQ v hv, hyt⟩
    have hep : (e p : E × ℝ) = y := (hecore p v hv rfl).trans hvy
    exact hep ▸ (e p).property

end PoincareConjecture.M76.ZeroChargeJoint
