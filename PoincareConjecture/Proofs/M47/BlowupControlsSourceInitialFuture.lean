import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialSlice
import PoincareConjecture.Proofs.M47.SeedCylinderClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

private theorem old_future_scalar_eq {F : SurgeryFlowData.{u}} {s t : ℝ}
    {x : (F.slice s).carrier} {y : (F.slice t).carrier}
    (hst : s = t) (hxy : HEq x y) :
    (F.connection s).scalarCurvature x = (F.connection t).scalarCurvature y := by
  cases hst
  cases hxy
  rfl

theorem exists_source_initial_old_future
    {F : SurgeryFlowData.{u}} {T : ℝ} (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)
    (old : SurgeryTerminalStrongNeck F T hT i)
    (hsmall : F.parameters.delta T ≤ 1 / 200)
    {base Q u B : ℝ} (hQ : 0 < Q) (hu : u ∈ Ioo (-1 : ℝ) (-1 / 2)) (hB : 0 < B) :
    let N := ((F.event T hT).necks i).neck
    let q := N.scale⁻¹ ^ 2
    let H := Q / q
    let c := H * (u + 1 / 2)
    let shift := -(Q * (base - T)) - H / 2
    let phi := fun s : ℝ => -1 / 2 + s / H
    let V := N.region (-B) B
    c < 0 ∧ IsOpen V ∧ V.Nonempty ∧
      (∀ s ∈ Icc c 0, phi s ∈ Ioo (-1 : ℝ) 0) ∧
      ∃ e0 : SurgeryFlowCylinder F (F.event T hT).terminal
          (base + shift / Q) Q (Icc c 0) V,
        (∀ s (hs : s ∈ Icc c 0) (hraw : phi s ∈ Ioo (-1 : ℝ) 0),
          (⟨(base + shift / Q) + s / Q, e0.forward s hs⟩ :
            (t : ℝ) × ((F.event T hT).terminal.carrier → (F.slice t).carrier)) =
            ⟨T + phi s / q, old.cylinder.forward (phi s) hraw⟩) ∧
        ∀ hs x, x ∈ V → (F.connection ((base + shift / Q) + c / Q)).scalarCurvature
          (e0.forward c hs x) ≤ 2 * q := by
  let N := ((F.event T hT).necks i).neck
  let q := N.scale⁻¹ ^ 2
  let H := Q / q
  let c := H * (u + 1 / 2)
  let shift := -(Q * (base - T)) - H / 2
  let phi := fun s : ℝ => -1 / 2 + s / H
  let V := N.region (-B) B
  have hq : 0 < q := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  have hH : 0 < H := div_pos hQ hq
  have hc : c < 0 := mul_neg_of_pos_of_neg hH (by linarith only [hu.2])
  have hphic : phi c = u := by
    dsimp only [phi, c]
    rw [mul_div_cancel_left₀ _ hH.ne']
    ring
  have hphi0 : phi 0 = -1 / 2 := by simp only [phi, zero_div, add_zero]
  have hmono : StrictMono phi := by
    intro s t hst
    have h := (div_lt_div_iff_of_pos_right hH).mpr hst
    dsimp only [phi]
    linarith only [h]
  have hmem : MapsTo phi (Icc c 0) (Ioo (-1 : ℝ) 0) := by
    intro s hs
    have hlo := hmono.monotone hs.1
    have hhi := hmono.monotone hs.2
    rw [hphic] at hlo
    rw [hphi0] at hhi
    exact ⟨hu.1.trans_le hlo, by linarith only [hhi]⟩
  have hclock : ∀ s ∈ Icc c 0,
      (base + shift / Q) + s / Q = T + phi s / q := by
    intro s _hs
    dsimp only [shift, phi, H]
    field_simp [hQ.ne', hq.ne']
    ring
  have hsub : V ⊆ N.carrier := fun _ hx => hx.1
  let e := old.cylinder.restrict (Subset.refl (Ioo (-1 : ℝ) 0)) ordConnected_Ioo hsub
  let e0 := Proofs.M47.seedCylinderReclock e hQ ordConnected_Icc phi hmem
    (hmono.strictMonoOn _) hclock
  have hcenter : N.center ∈ N.carrier := N.central_sphere_subset N.center_on_central_sphere
  have hheight : (N.coordinate_inverse N.center).2 = 0 :=
    (N.mem_central_sphere_iff_of_mem hcenter).mp N.center_on_central_sphere
  have hcenterV : N.center ∈ V :=
    ⟨hcenter, by rw [hheight]; exact ⟨neg_neg_of_pos hB, hB⟩⟩
  have hread (s : ℝ) (hs : s ∈ Icc c 0) (x : (F.event T hT).terminal.carrier) :
      HEq (e0.forward s hs x) (old.cylinder.forward (phi s) (hmem hs) x) :=
    Proofs.M47.seedCylinderReclock_forward_heq e hQ ordConnected_Icc phi hmem
      (hmono.strictMonoOn _) hclock s hs x
  refine ⟨hc, N.region_isOpen _ _, ⟨N.center, hcenterV⟩, hmem, e0, ?_, ?_⟩
  · intro s hs hraw
    apply Sigma.ext (hclock s hs)
    apply Function.hfunext rfl
    intro x y hxy
    cases hxy
    exact hread s hs x
  · intro hs x hx
    have htime : (base + shift / Q) + c / Q = T + u / q := by
      rw [hclock c ⟨le_rfl, hc.le⟩, hphic]
    have huI : u ∈ Ioo (-1 : ℝ) 0 := ⟨hu.1, by linarith only [hu.2]⟩
    have hraw : ∀ s (hs : s ∈ Ioo (-1 : ℝ) 0), s = u →
        HEq (old.cylinder.forward s hs x) (old.cylinder.forward u huI x) := by
      intro s hs hsu
      subst s
      rfl
    have heq := (hread c ⟨le_rfl, hc.le⟩ x).trans (hraw _ _ hphic)
    rw [old_future_scalar_eq htime heq]
    exact (source_initial_old_scalar_bounds hT i old hsmall u huI hx.1).2

end PoincareConjecture.M47
