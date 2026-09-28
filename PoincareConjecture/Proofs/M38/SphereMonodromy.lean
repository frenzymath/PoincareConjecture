import PoincareConjecture.Proofs.M38.PolarCoordinates
import Mathlib.Algebra.Group.End
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Geometry.Manifold.Algebra.Structures

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

def monodromyPunctureOpen : TopologicalSpace.Opens StandardCapSpace :=
  ⟨{0}ᶜ, isOpen_compl_singleton⟩

variable (phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

theorem monodromy_power_smooth (n : ℤ) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (fun x => (phi.toEquiv ^ n) x) := by
  cases n with
  | ofNat n =>
      change ContMDiff (𝓡 2) (𝓡 2) ∞ (⇑(phi.toEquiv ^ (n : ℤ)))
      rw [zpow_natCast, Equiv.Perm.coe_pow, Diffeomorph.coe_toEquiv]
      exact (phi.contMDiff).iterate n
  | negSucc n =>
      change ContMDiff (𝓡 2) (𝓡 2) ∞ (⇑(phi.toEquiv ^ Int.negSucc n))
      rw [zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow, Equiv.Perm.coe_inv,
        Diffeomorph.toEquiv_coe_symm]
      exact (phi.symm.contMDiff).iterate (n + 1)

noncomputable def monodromyDeck (n : ℤ) (x : monodromyPunctureOpen) :
    monodromyPunctureOpen :=
  ⟨(Real.exp (n : ℝ) * ‖x.val‖) •
      ((phi.toEquiv ^ (-n)) (capUnitDirection x.val)).val, by
    have hr : 0 < Real.exp (n : ℝ) * ‖x.val‖ :=
      mul_pos (Real.exp_pos _) (norm_pos_iff.mpr x.property)
    change (Real.exp (n : ℝ) * ‖x.val‖) •
      ((phi.toEquiv ^ (-n)) (capUnitDirection x.val)).val ≠ 0
    apply norm_pos_iff.mp
    simpa [norm_smul, abs_of_pos hr] using hr⟩

theorem monodromyDeck_norm (n : ℤ) (x : monodromyPunctureOpen) :
    ‖(monodromyDeck phi n x).val‖ = Real.exp (n : ℝ) * ‖x.val‖ := by
  simp [monodromyDeck, norm_smul]

theorem monodromyDeck_direction (n : ℤ) (x : monodromyPunctureOpen) :
    capUnitDirection (monodromyDeck phi n x).val =
      (phi.toEquiv ^ (-n)) (capUnitDirection x.val) :=
  capUnitDirection_smul _ (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr x.property))

theorem monodromyDeck_zero (x : monodromyPunctureOpen) :
    monodromyDeck phi 0 x = x := by
  apply Subtype.ext
  simpa only [monodromyDeck, Int.cast_zero, Real.exp_zero, one_mul, neg_zero,
    zpow_zero, Equiv.Perm.one_apply] using capUnitDirection_radial x.val

theorem monodromyDeck_add (m n : ℤ) (x : monodromyPunctureOpen) :
    monodromyDeck phi m (monodromyDeck phi n x) = monodromyDeck phi (m + n) x := by
  apply Subtype.ext
  change (Real.exp (m : ℝ) * ‖(monodromyDeck phi n x).val‖) •
      ((phi.toEquiv ^ (-m)) (capUnitDirection (monodromyDeck phi n x).val)).val =
    (Real.exp ((m + n : ℤ) : ℝ) * ‖x.val‖) •
      ((phi.toEquiv ^ (-(m + n))) (capUnitDirection x.val)).val
  rw [monodromyDeck_norm, monodromyDeck_direction, Int.cast_add, Real.exp_add,
    neg_add, zpow_add, Equiv.Perm.mul_apply, mul_assoc]

theorem monodromy_radius_smooth :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x : monodromyPunctureOpen => ‖x.val‖) := by
  intro x
  apply (contMDiffAt_subtype_iff (U := monodromyPunctureOpen)).mpr
  exact (contDiffAt_norm ℝ x.property).contMDiffAt

theorem monodromyDeck_smooth (n : ℤ) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (monodromyDeck phi n) := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩
  apply (ContMDiff.subtypeVal_comp_iff monodromyPunctureOpen _).mp
  have hd : ContMDiff (𝓡 3) (𝓡 2) ∞
      (fun x : monodromyPunctureOpen => capUnitDirection x.val) :=
    capUnitDirection_smooth.comp_contMDiff contMDiff_subtype_val (fun x => x.property)
  have hs : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun x : monodromyPunctureOpen =>
        ((phi.toEquiv ^ (-n)) (capUnitDirection x.val)).val) :=
    contMDiff_coe_sphere.comp ((monodromy_power_smooth phi (-n)).comp hd)
  exact (contMDiff_const.mul monodromy_radius_smooth).smul hs

noncomputable def monodromyDeckDiffeomorph (n : ℤ) :
    Diffeomorph (𝓡 3) (𝓡 3) monodromyPunctureOpen monodromyPunctureOpen ∞ where
  toFun := monodromyDeck phi n
  invFun := monodromyDeck phi (-n)
  left_inv := fun x => by rw [monodromyDeck_add, neg_add_cancel, monodromyDeck_zero]
  right_inv := fun x => by rw [monodromyDeck_add, add_neg_cancel, monodromyDeck_zero]
  contMDiff_toFun := monodromyDeck_smooth phi n
  contMDiff_invFun := monodromyDeck_smooth phi (-n)

noncomputable def monodromyLogRadius (x : monodromyPunctureOpen) : ℝ := Real.log ‖x.val‖

theorem monodromyLogRadius_smooth :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ monodromyLogRadius := by
  intro x
  exact (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr x.property)).contMDiffAt.comp x
    (monodromy_radius_smooth x)

theorem monodromyDeck_logRadius (n : ℤ) (x : monodromyPunctureOpen) :
    monodromyLogRadius (monodromyDeck phi n x) = (n : ℝ) + monodromyLogRadius x := by
  rw [monodromyLogRadius, monodromyDeck_norm,
    Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr x.property), Real.log_exp]
  rfl

theorem monodromyDeck_eq_self_iff (n : ℤ) (x : monodromyPunctureOpen) :
    monodromyDeck phi n x = x ↔ n = 0 := by
  constructor
  · intro h
    have hlog := congrArg monodromyLogRadius h
    rw [monodromyDeck_logRadius] at hlog
    have hn : (n : ℝ) = 0 := by linarith
    exact Int.cast_eq_zero.mp hn
  · rintro rfl
    exact monodromyDeck_zero phi x

@[instance_reducible]
noncomputable def monodromyAddAction : AddAction ℤ monodromyPunctureOpen where
  vadd := monodromyDeck phi
  zero_vadd := monodromyDeck_zero phi
  add_vadd := fun m n x => (monodromyDeck_add phi m n x).symm

end PoincareConjecture.M38
