import Mathlib.Order.Hom.Set
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic

/-!
# Continuous reparametrization of radial flow lines

A continuous family of strictly increasing surjections has a jointly
continuous inverse. Applied to positive radii, this changes the parameter
along each flow line to its actual distance without requiring smoothness of
the distance function at cut points.

This is the topological reparametrization used in the discussion following
Morgan--Tian, Corollary 2.10, p. 27.
-/

noncomputable section
set_option autoImplicit false

open Set

namespace Poincare.Topology

variable {Theta A B : Type*} [TopologicalSpace Theta]
  [LinearOrder A] [TopologicalSpace A] [OrderTopology A]
  [LinearOrder B] [TopologicalSpace B] [OrderTopology B]

/-- The inverses of a continuous family of increasing bijections depend
continuously on both the parameter and the target value. -/
theorem continuous_monotoneFamily_inverse (f : Theta × A → B)
    (hf : Continuous f)
    (hmono : ∀ theta, StrictMono (fun a => f (theta, a)))
    (hsurj : ∀ theta, Function.Surjective (fun a => f (theta, a))) :
    Continuous (fun z : Theta × B =>
      ((hmono z.1).orderIsoOfSurjective (fun a => f (z.1, a)) (hsurj z.1)).symm z.2) := by
  apply OrderTopology.continuous_iff.mpr
  intro a
  have hslice : Continuous (fun z : Theta × B => f (z.1, a)) :=
    hf.comp (continuous_fst.prodMk continuous_const)
  constructor
  · have heq :
        (fun z : Theta × B =>
          ((hmono z.1).orderIsoOfSurjective (fun a => f (z.1, a)) (hsurj z.1)).symm z.2)
            ⁻¹' Ioi a = {z : Theta × B | f (z.1, a) < z.2} := by
      ext z
      exact ((hmono z.1).orderIsoOfSurjective (fun a => f (z.1, a))
        (hsurj z.1)).lt_symm_apply
    rw [heq]
    exact isOpen_lt hslice continuous_snd
  · have heq :
        (fun z : Theta × B =>
          ((hmono z.1).orderIsoOfSurjective (fun a => f (z.1, a)) (hsurj z.1)).symm z.2)
            ⁻¹' Iio a = {z : Theta × B | z.2 < f (z.1, a)} := by
      ext z
      exact ((hmono z.1).orderIsoOfSurjective (fun a => f (z.1, a))
        (hsurj z.1)).symm_apply_lt
    rw [heq]
    exact isOpen_lt continuous_snd hslice

/-- Reparametrize an ordered coordinate by a continuous family of strictly
increasing surjections, retaining the other coordinate. -/
def monotoneFamilyHomeomorph (f : Theta × A → B) (hf : Continuous f)
    (hmono : ∀ theta, StrictMono (fun a => f (theta, a)))
    (hsurj : ∀ theta, Function.Surjective (fun a => f (theta, a))) :
    (Theta × A) ≃ₜ (Theta × B) where
  toFun z := (z.1, f z)
  invFun z := (z.1,
    ((hmono z.1).orderIsoOfSurjective (fun a => f (z.1, a)) (hsurj z.1)).symm z.2)
  left_inv z := Prod.ext rfl
    (((hmono z.1).orderIsoOfSurjective (fun a => f (z.1, a))
      (hsurj z.1)).symm_apply_apply z.2)
  right_inv z := Prod.ext rfl
    (((hmono z.1).orderIsoOfSurjective (fun a => f (z.1, a))
      (hsurj z.1)).apply_symm_apply z.2)
  continuous_toFun := continuous_fst.prodMk hf
  continuous_invFun := continuous_fst.prodMk
    (continuous_monotoneFamily_inverse f hf hmono hsurj)

@[simp] theorem monotoneFamilyHomeomorph_apply (f : Theta × A → B) (hf : Continuous f)
    (hmono : ∀ theta, StrictMono (fun a => f (theta, a)))
    (hsurj : ∀ theta, Function.Surjective (fun a => f (theta, a))) (z : Theta × A) :
    monotoneFamilyHomeomorph f hf hmono hsurj z = (z.1, f z) := rfl

@[simp] theorem monotoneFamilyHomeomorph_symm_fst (f : Theta × A → B) (hf : Continuous f)
    (hmono : ∀ theta, StrictMono (fun a => f (theta, a)))
    (hsurj : ∀ theta, Function.Surjective (fun a => f (theta, a))) (z : Theta × B) :
    ((monotoneFamilyHomeomorph f hf hmono hsurj).symm z).1 = z.1 := rfl

/-- Replace a positive radius by its continuous, strictly increasing,
surjective distance readout along each flow line. -/
abbrev positiveRadiusReparametrization
    (f : Theta × Ioi (0 : ℝ) → Ioi (0 : ℝ)) (hf : Continuous f)
    (hmono : ∀ theta, StrictMono (fun r => f (theta, r)))
    (hsurj : ∀ theta, Function.Surjective (fun r => f (theta, r))) :
    (Theta × Ioi (0 : ℝ)) ≃ₜ (Theta × Ioi (0 : ℝ)) :=
  monotoneFamilyHomeomorph f hf hmono hsurj

end Poincare.Topology
