import PoincareConjecture.Proofs.M47.SeedCylinderSource
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_TrackedBall










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale a : ℝ} {U : Set C.carrier}



theorem exists_cap_birth_cylinder
    (e : SurgeryFlowCylinder F C origin scale (Icc a 0) U)
    (hU : IsOpen U) (ha : a < 0) (h : ℝ) (hh : 0 < h) :
    let t := origin + a / scale
    let V := e.forward a ⟨le_rfl, ha.le⟩ '' U
    ∃ hmem : MapsTo (fun s : ℝ => a + scale * s * h ^ 2)
        (Icc 0 ((origin - t) / h ^ 2)) (Icc a 0),
      ∃ f : SurgeryFlowCylinder F (F.slice t) t (h⁻¹ ^ 2)
          (Icc 0 ((origin - t) / h ^ 2)) V,
        (∀ hs x, x ∈ V → HEq (f.forward 0 hs x) x) ∧
        ∀ s hs x, x ∈ U →
          (⟨t + s / (h⁻¹ ^ 2), f.forward s hs (e.forward a ⟨le_rfl, ha.le⟩ x)⟩ :
            Σ t, (F.slice t).carrier) =
          ⟨origin + (a + scale * s * h ^ 2) / scale,
            e.forward (a + scale * s * h ^ 2) (hmem hs) x⟩ := by
  let t := origin + a / scale
  let V := e.forward a ⟨le_rfl, ha.le⟩ '' U
  let J := Icc 0 ((origin - t) / h ^ 2)
  let phi : ℝ → ℝ := fun s => a + scale * s * h ^ 2
  have hsq : 0 < h ^ 2 := sq_pos_of_pos hh
  have hmem : MapsTo phi J (Icc a 0) := by
    intro s hs
    have hmax : s * h ^ 2 ≤ origin - t := (le_div_iff₀ hsq).mp hs.2
    have hupper := mul_le_mul_of_nonneg_left hmax e.scale_pos.le
    have hclockEnd : scale * (origin - t) = -a := by
      dsimp only [t]
      field_simp [e.scale_pos.ne']
      ring
    rw [hclockEnd] at hupper
    constructor
    · dsimp only [phi]
      nlinarith only [mul_nonneg e.scale_pos.le (mul_nonneg hs.1 hsq.le)]
    · dsimp only [phi]
      nlinarith only [hupper]
  have hmono : StrictMonoOn phi J := by
    intro s _ r _ hsr
    dsimp only [phi]
    nlinarith only [mul_lt_mul_of_pos_right hsr (mul_pos e.scale_pos hsq)]
  have hclock (s : ℝ) (_hs : s ∈ J) :
      t + s / (h⁻¹ ^ 2) = origin + phi s / scale := by
    dsimp only [t, phi]
    rw [surgeryCap_physical_time]
    field_simp [e.scale_pos.ne']
    ring
  let chart := M44.cylinderSliceChart e hU a ⟨le_rfl, ha.le⟩
  have hcapScale : 0 < h⁻¹ ^ 2 := pow_pos (inv_pos.mpr hh) 2
  let shifted := Proofs.M47.seedCylinderReclock e hcapScale ordConnected_Icc
    phi hmem hmono hclock
  have hsource : V ⊆ chart.symm.source := Subset.rfl
  have hmaps : MapsTo chart.symm V U := fun _ hx => chart.symm.map_source (hsource hx)
  let f := Proofs.M47.seedCylinderSource shifted chart.symm V hsource hmaps
  refine ⟨hmem, f, ?_, ?_⟩
  · intro hs x hx
    have he := Proofs.M47.seedCylinderReclock_forward_heq e hcapScale
      ordConnected_Icc phi hmem hmono hclock 0 hs (chart.symm x)
    change HEq (f.forward 0 hs x) (e.forward (phi 0) (hmem hs) (chart.symm x)) at he
    have hphi : phi 0 = a := by simp only [phi, mul_zero, zero_mul, add_zero]
    have hpoint (s : ℝ) (hs : s ∈ Icc a 0) (hsa : s = a) :
        HEq (e.forward s hs (chart.symm x)) x := by
      subst s
      exact heq_of_eq (chart.right_inv hx)
    exact he.trans (hpoint _ _ hphi)
  · intro s hs x hx
    have he := Proofs.M47.seedCylinderReclock_forward_heq e hcapScale
      ordConnected_Icc phi hmem hmono hclock s hs (chart.symm (e.forward a ⟨le_rfl, ha.le⟩ x))
    change HEq (f.forward s hs (e.forward a ⟨le_rfl, ha.le⟩ x))
      (e.forward (phi s) (hmem hs) (chart.symm (chart x))) at he
    exact Sigma.ext (hclock s hs)
      (he.trans (heq_of_eq (congrArg (e.forward (phi s) (hmem hs)) (chart.left_inv hx))))



theorem exists_cap_birth_cylinder_scalar_bound
    (e : SurgeryFlowCylinder F C origin scale (Icc a 0) U)
    (hU : IsOpen U) (ha : a < 0) (h : ℝ) (hh : 0 < h)
    (x : C.carrier) (hx : x ∈ U) {K : ℝ}
    (hscalar : ∀ s (hs : s ∈ Icc a 0),
      (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs x) ≤ K) :
    let t := origin + a / scale
    let V := e.forward a ⟨le_rfl, ha.le⟩ '' U
    ∃ f : SurgeryFlowCylinder F (F.slice t) t (h⁻¹ ^ 2)
        (Icc 0 ((origin - t) / h ^ 2)) V,
      (∀ hs y, y ∈ V → HEq (f.forward 0 hs y) y) ∧
      ∀ s hs, (F.connection (t + s / (h⁻¹ ^ 2))).scalarCurvature
        (f.forward s hs (e.forward a ⟨le_rfl, ha.le⟩ x)) ≤ K := by
  obtain ⟨hmem, f, based, point⟩ := exists_cap_birth_cylinder e hU ha h hh
  refine ⟨f, based, ?_⟩
  intro s hs
  have hread := congrArg
    (fun z : Σ t, (F.slice t).carrier => (F.connection z.1).scalarCurvature z.2)
    (point s hs x hx)
  exact hread.trans_le (hscalar (a + scale * s * h ^ 2) (hmem hs))

end PoincareConjecture.M47
