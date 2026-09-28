import PoincareConjecture.Proofs.M47.SeedM15Cylinder
import PoincareConjecture.Proofs.M47.SeedCylinderClock










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47



theorem source_initial_cylinder_eq_of_terminal
    {F : SurgeryFlowData.{u}} {C D : GeneralizedSliceCarrier.{u}}
    {origin scale a b : ℝ} {I J : Set ℝ} {U : Set C.carrier} {V : Set D.carrier}
    (e : SurgeryFlowCylinder F C origin scale I U)
    (f : SurgeryFlowCylinder F D origin scale J V)
    (hab : a ≤ b) (hI : Icc a b ⊆ I) (hJ : Icc a b ⊆ J)
    (x : C.carrier) (hx : x ∈ U) (y : D.carrier) (hy : y ∈ V)
    (hterminal : e.forward b (hI ⟨hab, le_rfl⟩) x =
      f.forward b (hJ ⟨hab, le_rfl⟩) y) :
    e.forward a (hI ⟨le_rfl, hab⟩) x = f.forward a (hJ ⟨le_rfl, hab⟩) y := by
  let c := (a - b) / scale
  let phi := fun s : ℝ => b + scale * s
  have hc : c ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hab) e.scale_pos.le
  have hphic : phi c = a := by
    dsimp only [phi, c]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ e.scale_pos.ne']
    ring
  have hphi0 : phi 0 = b := by simp only [phi, mul_zero, add_zero]
  have hmono : StrictMono phi := by
    intro s t hst
    simpa only [phi, add_comm] using
      add_lt_add_left (mul_lt_mul_of_pos_left hst e.scale_pos) b
  have hmem : MapsTo phi (Icc c 0) (Icc a b) := by
    intro s hs
    constructor
    · simpa only [hphic] using hmono.monotone hs.1
    · simpa only [hphi0] using hmono.monotone hs.2
  have hclock : ∀ s ∈ Icc c 0,
      (origin + b / scale) + s / 1 = origin + phi s / scale := by
    intro s _hs
    dsimp only [phi]
    rw [div_one, add_div, mul_div_cancel_left₀ _ e.scale_pos.ne']
    ring
  let E := Proofs.M47.seedCylinderReclock e (by norm_num : (0 : ℝ) < 1)
    ordConnected_Icc phi (fun _ hs => hI (hmem hs)) (hmono.strictMonoOn _) hclock
  let G := Proofs.M47.seedCylinderReclock f (by norm_num : (0 : ℝ) < 1)
    ordConnected_Icc phi (fun _ hs => hJ (hmem hs)) (hmono.strictMonoOn _) hclock
  have he (s : ℝ) (hs : s ∈ Icc c 0) (t : ℝ) (ht : t ∈ I) (hst : phi s = t) :
      HEq (E.forward s hs x) (e.forward t ht x) := by
    have h := Proofs.M47.seedCylinderReclock_forward_heq e
      (by norm_num : (0 : ℝ) < 1) ordConnected_Icc phi
      (fun _ hs => hI (hmem hs)) (hmono.strictMonoOn _) hclock s hs x
    subst t
    exact h
  have hf (s : ℝ) (hs : s ∈ Icc c 0) (t : ℝ) (ht : t ∈ J) (hst : phi s = t) :
      HEq (G.forward s hs y) (f.forward t ht y) := by
    have h := Proofs.M47.seedCylinderReclock_forward_heq f
      (by norm_num : (0 : ℝ) < 1) ordConnected_Icc phi
      (fun _ hs => hJ (hmem hs)) (hmono.strictMonoOn _) hclock s hs y
    subst t
    exact h
  have hzero : (0 : ℝ) ∈ Icc c 0 := ⟨hc, le_rfl⟩
  have hterminal' : E.forward 0 hzero x = G.forward 0 hzero y :=
    eq_of_heq ((he 0 hzero b (hI ⟨hab, le_rfl⟩) hphi0).trans
      ((heq_of_eq hterminal).trans (hf 0 hzero b (hJ ⟨hab, le_rfl⟩) hphi0).symm))
  have heq := seedM15_cylinder_eq_of_terminal E G hc (Subset.refl _) (Subset.refl _)
    x hx y hy hterminal'
  have hbottom : c ∈ Icc c 0 := ⟨le_rfl, hc⟩
  exact eq_of_heq ((he c hbottom a (hI ⟨le_rfl, hab⟩) hphic).symm.trans
    ((heq_of_eq heq).trans (hf c hbottom a (hJ ⟨le_rfl, hab⟩) hphic)))

end PoincareConjecture.M47
