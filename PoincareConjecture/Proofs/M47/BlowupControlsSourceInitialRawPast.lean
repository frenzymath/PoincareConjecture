import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialAgreement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

theorem exists_source_initial_raw_past
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {T origin Q q b : ℝ} {U V : Set C.carrier}
    (E : SurgeryFlowCylinder F C origin Q (Icc b 0) U)
    (old : SurgeryFlowCylinder F C T q (Ioo (-1 : ℝ) 0) V)
    (hb : b ≤ 0) (hUV : U ⊆ V)
    (hclock : ∀ s : ℝ, origin + s / Q = T + (-1 / 2 + s / (Q / q)) / q)
    (hterminal : ∀ x ∈ U,
      (⟨origin + 0 / Q, E.forward 0 ⟨hb, le_rfl⟩ x⟩ : Σ t, (F.slice t).carrier) =
        ⟨T + (-1 / 2) / q, old.forward (-1 / 2) (by norm_num) x⟩) :
    let H := Q / q
    let left := -1 / 2 + b / H
    let psi := fun v : ℝ => H * (v + 1 / 2)
    ∃ hmem : MapsTo psi (Icc left (-1 / 2)) (Icc b 0),
      ∃ D : SurgeryFlowCylinder F C T q (Icc left (-1 / 2)) U,
        (∀ v (hv : v ∈ Icc left (-1 / 2)) (x : C.carrier),
          (⟨T + v / q, D.forward v hv x⟩ : Σ t, (F.slice t).carrier) =
            ⟨origin + psi v / Q, E.forward (psi v) (hmem hv) x⟩) ∧
        ∀ v (hv : v ∈ Icc left (-1 / 2)) (hraw : v ∈ Ioo (-1 : ℝ) 0),
          ∀ x ∈ U, D.forward v hv x = old.forward v hraw x := by
  let H := Q / q
  let left := -1 / 2 + b / H
  let psi := fun v : ℝ => H * (v + 1 / 2)
  have hH : 0 < H := div_pos E.scale_pos old.scale_pos
  have hleft : left ≤ -1 / 2 := by
    dsimp only [left]
    exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hb hH.le)
  have hpsiLeft : psi left = b := by
    dsimp only [psi, left]
    field_simp [hH.ne']
    ring
  have hpsiTop : psi (-1 / 2) = 0 := by dsimp only [psi]; ring
  have hmono : StrictMono psi := by
    intro s t hst
    exact mul_lt_mul_of_pos_left (by linarith only [hst]) hH
  have hmem : MapsTo psi (Icc left (-1 / 2)) (Icc b 0) := by
    intro v hv
    constructor
    · simpa only [hpsiLeft] using hmono.monotone hv.1
    · simpa only [hpsiTop] using hmono.monotone hv.2
  have hrawClock : ∀ v ∈ Icc left (-1 / 2),
      T + v / q = origin + psi v / Q := by
    intro v _hv
    rw [hclock]
    have hparam : -1 / 2 + psi v / (Q / q) = v := by
      change -1 / 2 + psi v / H = v
      dsimp only [psi]
      rw [mul_div_cancel_left₀ _ hH.ne']
      ring
    rw [hparam]
  let D := Proofs.M47.seedCylinderReclock E old.scale_pos ordConnected_Icc
    psi hmem (hmono.strictMonoOn _) hrawClock
  have hread (v : ℝ) (hv : v ∈ Icc left (-1 / 2)) (x : C.carrier) :
      (⟨T + v / q, D.forward v hv x⟩ : Σ t, (F.slice t).carrier) =
        ⟨origin + psi v / Q, E.forward (psi v) (hmem hv) x⟩ := by
    apply Sigma.ext (hrawClock v hv)
    exact Proofs.M47.seedCylinderReclock_forward_heq E old.scale_pos ordConnected_Icc
      psi hmem (hmono.strictMonoOn _) hrawClock v hv x
  have htop : (-1 / 2 : ℝ) ∈ Icc left (-1 / 2) := ⟨hleft, le_rfl⟩
  have htopRead (x : C.carrier) (hx : x ∈ U) :
      D.forward (-1 / 2) htop x = old.forward (-1 / 2) (by norm_num) x := by
    have h := hread (-1 / 2) htop x
    have hzero : ∀ r (hr : r ∈ Icc b 0), r = 0 →
        (⟨origin + r / Q, E.forward r hr x⟩ : Σ t, (F.slice t).carrier) =
          ⟨origin + 0 / Q, E.forward 0 ⟨hb, le_rfl⟩ x⟩ := by
      intro r hr hr0
      subst r
      rfl
    exact eq_of_heq (Sigma.mk.inj
      (h.trans ((hzero _ _ hpsiTop).trans (hterminal x hx)))).2
  refine ⟨hmem, D, hread, ?_⟩
  intro v hv hraw x hx
  have hD : Icc v (-1 / 2) ⊆ Icc left (-1 / 2) :=
    fun _ ht => ⟨hv.1.trans ht.1, ht.2⟩
  have hOld : Icc v (-1 / 2) ⊆ Ioo (-1 : ℝ) 0 :=
    fun _ ht => ⟨hraw.1.trans_le ht.1, ht.2.trans_lt (by norm_num)⟩
  exact source_initial_cylinder_eq_of_terminal D old hv.2 hD hOld
    x hx x (hUV hx) (htopRead x hx)

end PoincareConjecture.M47
