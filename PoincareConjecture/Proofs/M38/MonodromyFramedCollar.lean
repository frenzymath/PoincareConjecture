import PoincareConjecture.Proofs.M38.MonodromyLiftedCollar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (beta theta : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
  {k : ℝ} (hk : 0 < k)

noncomputable def monodromyCylinderFrame :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞ where
  toFun z := (theta z.1, k * z.2)
  invFun z := (theta.symm z.1, z.2 / k)
  left_inv z := Prod.ext (theta.symm_apply_apply z.1) (mul_div_cancel_left₀ z.2 hk.ne')
  right_inv z := Prod.ext (theta.apply_symm_apply z.1) (mul_div_cancel₀ z.2 hk.ne')
  contMDiff_toFun := (theta.contMDiff.comp contMDiff_fst).prodMk
    ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_snd)
  contMDiff_invFun := (theta.symm.contMDiff.comp contMDiff_fst).prodMk
    ((contDiff_id.div_const k).contMDiff.comp contMDiff_snd)

noncomputable def monodromyFramedCollar (a : ℝ) (hwidth : 2 * (k * a) ≤ 1) :
    PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace
      (monodromyCarrier.{u} beta).carrier ∞ :=
  (monodromyCylinderFrame theta hk).toPartialDiffeomorph.trans
    (monodromyLiftedCollar beta (k * a) hwidth)

theorem monodromyFramedCollar_source (a : ℝ) (hwidth : 2 * (k * a) ≤ 1) :
    (monodromyFramedCollar.{u} beta theta hk a hwidth).source =
      Set.univ ×ˢ Set.Ioo (-a) a := by
  change Set.univ ∩ (fun z : RoundCylinderSpace => (theta z.1, k * z.2)) ⁻¹'
    (Set.univ ×ˢ Set.Ioo (-(k * a)) (k * a)) = _
  ext z
  simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_preimage,
    Set.mem_prod, Set.mem_Ioo]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor <;> nlinarith
  · rintro ⟨hlo, hhi⟩
    constructor
    · nlinarith [mul_lt_mul_of_pos_left hlo hk]
    · exact mul_lt_mul_of_pos_left hhi hk

theorem monodromyFramedCollar_apply (a : ℝ) (hwidth : 2 * (k * a) ≤ 1)
    (z : RoundCylinderSpace) :
    monodromyFramedCollar.{u} beta theta hk a hwidth z =
      monodromyLiftedCylinder beta (theta z.1, k * z.2) := rfl

theorem monodromyFramedCollar_inverse (a : ℝ) (hwidth : 2 * (k * a) ≤ 1)
    (q : (monodromyCarrier.{u} beta).carrier) :
    (monodromyFramedCollar beta theta hk a hwidth).symm q =
      (theta.symm (monodromyStripInverse beta (-(k * a)) (k * a) q.down).1,
        (monodromyStripInverse beta (-(k * a)) (k * a) q.down).2 / k) := rfl

theorem monodromyFramedCollar_central (a : ℝ) (hwidth : 2 * (k * a) ≤ 1) :
    comparisonCentralSphere (monodromyFramedCollar.{u} beta theta hk a hwidth) =
      monodromyLiftedZeroFiber beta := by
  rw [← monodromyLiftedCollar_central beta (k * a) hwidth]
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨(theta z.1, 0), ⟨Set.mem_univ _, rfl⟩, ?_⟩
    have hz0 : z.2 = 0 := hz.2
    change monodromyLiftedCylinder beta (theta z.1, 0) =
      monodromyLiftedCylinder beta (theta z.1, k * z.2)
    rw [hz0, mul_zero]
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨(theta.symm z.1, 0), ⟨Set.mem_univ _, rfl⟩, ?_⟩
    have hz0 : z.2 = 0 := hz.2
    change monodromyLiftedCylinder beta (theta (theta.symm z.1), k * 0) =
      monodromyLiftedCylinder beta z
    rw [mul_zero, theta.apply_symm_apply]
    exact congrArg (monodromyLiftedCylinder beta) (Prod.ext rfl hz0.symm)

omit theta hk in

theorem monodromyLiftedCylinder_shift (z : UnitTwoSphere) (t : ℝ) :
    monodromyLiftedCylinder.{u} beta (z, 1 + t) =
      monodromyLiftedCylinder beta (beta z, t) := by
  apply ULift.ext
  have h := (monodromy_quotient_deck beta (-1)
    (monodromyPolarPoint (z, 1 + t))).symm
  simpa only [monodromyLiftedCylinder, monodromyCylinder, monodromyDeck_polar,
    neg_neg, zpow_one, Int.cast_neg, Int.cast_one, Diffeomorph.coe_toEquiv,
    show (1 + t) + -1 = t by ring] using h

noncomputable def attachingMonodromy
    (theta0 theta1 g : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞) :
    Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞ :=
  theta0.symm.trans (g.trans theta1)

theorem attachingMonodromy_angle
    (theta0 theta1 g : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
    (z : UnitTwoSphere) :
    attachingMonodromy theta0 theta1 g (theta0 z) = theta1 (g z) := by
  change theta1 (g (theta0.symm (theta0 z))) = _
  rw [theta0.symm_apply_apply]

theorem attachingMonodromy_negative
    (theta0 theta1 g : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
    (z : UnitTwoSphere) (t : ℝ) :
    monodromyLiftedCylinder.{u} (attachingMonodromy theta0 theta1 g) (theta0 z, 1 + t) =
      monodromyLiftedCylinder (attachingMonodromy theta0 theta1 g) (theta1 (g z), t) := by
  rw [monodromyLiftedCylinder_shift, attachingMonodromy_angle]

end PoincareConjecture.M38
