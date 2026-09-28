import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Homotopy.Basic

set_option autoImplicit false
open Set Topology unitInterval

namespace PoincareConjecture.M76.CollarIsotopy

def cutoff (t r : I) : I :=
  ⟨min (t : ℝ) (1 - (r : ℝ)),
    le_min t.property.1 (sub_nonneg.mpr r.property.2),
    (min_le_left _ _).trans t.property.2⟩

theorem continuous_cutoff : Continuous (fun z : I × I => cutoff z.1 z.2) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).min
    (continuous_const.sub (continuous_subtype_val.comp continuous_snd))

@[simp] theorem cutoff_outer (t : I) : cutoff t 0 = t := by
  apply Subtype.ext
  exact (show min (t : ℝ) (1 - 0) = (t : ℝ) by
    rw [sub_zero, min_eq_left t.property.2])

@[simp] theorem cutoff_inner (t : I) : cutoff t 1 = 0 := by
  apply Subtype.ext
  change min (t : ℝ) (1 - 1) = 0
  rw [sub_self, min_eq_right t.property.1]

@[simp] theorem cutoff_zero (r : I) : cutoff 0 r = 0 := by
  apply Subtype.ext
  exact min_eq_left (sub_nonneg.mpr r.property.2)

variable {S : Type*} [TopologicalSpace S]

def collarExtension (H : I → S ≃ₜ S)
    (hc : Continuous (fun z : I × S => H z.1 z.2))
    (hci : Continuous (fun z : I × S => (H z.1).symm z.2))
    (t : I) : (I × S) ≃ₜ (I × S) where
  toFun z := (z.1, H (cutoff t z.1) z.2)
  invFun z := (z.1, (H (cutoff t z.1)).symm z.2)
  left_inv z := Prod.ext rfl ((H (cutoff t z.1)).symm_apply_apply z.2)
  right_inv z := Prod.ext rfl ((H (cutoff t z.1)).apply_symm_apply z.2)
  continuous_toFun := continuous_fst.prodMk (hc.comp
    ((continuous_cutoff.comp (continuous_const.prodMk continuous_fst)).prodMk continuous_snd))
  continuous_invFun := continuous_fst.prodMk (hci.comp
    ((continuous_cutoff.comp (continuous_const.prodMk continuous_fst)).prodMk continuous_snd))

variable (H : I → S ≃ₜ S)
  (hc : Continuous (fun z : I × S => H z.1 z.2))
  (hci : Continuous (fun z : I × S => (H z.1).symm z.2))

@[simp] theorem collarExtension_apply (t r : I) (x : S) :
    collarExtension H hc hci t (r, x) = (r, H (cutoff t r) x) := rfl

@[simp] theorem collarExtension_symm_apply (t r : I) (x : S) :
    (collarExtension H hc hci t).symm (r, x) = (r, (H (cutoff t r)).symm x) := rfl

theorem continuous_collarExtension :
    Continuous (fun z : I × (I × S) => collarExtension H hc hci z.1 z.2) := by
  exact (continuous_fst.comp continuous_snd).prodMk (hc.comp
    ((continuous_cutoff.comp (continuous_fst.prodMk
      (continuous_fst.comp continuous_snd))).prodMk (continuous_snd.comp continuous_snd)))

theorem continuous_collarExtension_symm :
    Continuous (fun z : I × (I × S) => (collarExtension H hc hci z.1).symm z.2) := by
  exact (continuous_fst.comp continuous_snd).prodMk (hci.comp
    ((continuous_cutoff.comp (continuous_fst.prodMk
      (continuous_fst.comp continuous_snd))).prodMk (continuous_snd.comp continuous_snd)))

@[simp] theorem collarExtension_outer (t : I) (x : S) :
    collarExtension H hc hci t (0, x) = (0, H t x) := by
  rw [collarExtension_apply, cutoff_outer]

theorem collarExtension_inner (hzero : ∀ x, H 0 x = x) (t : I) (x : S) :
    collarExtension H hc hci t (1, x) = (1, x) := by
  rw [collarExtension_apply, cutoff_inner, hzero]

theorem collarExtension_zero (hzero : ∀ x, H 0 x = x) :
    collarExtension H hc hci 0 = Homeomorph.refl (I × S) := by
  apply Homeomorph.ext
  rintro ⟨r, x⟩
  rw [collarExtension_apply, cutoff_zero, hzero]
  rfl

theorem collarExtension_fixed (x : S) (hx : ∀ t, H t x = x) (t r : I) :
    collarExtension H hc hci t (r, x) = (r, x) := by
  rw [collarExtension_apply, hx]

def collarHomotopyRelInner (hzero : ∀ x, H 0 x = x) :
    (ContinuousMap.id (I × S)).HomotopyRel
      ⟨collarExtension H hc hci 1, (collarExtension H hc hci 1).continuous⟩
      {z : I × S | z.1 = 1} where
  toFun z := collarExtension H hc hci z.1 z.2
  continuous_toFun := continuous_collarExtension H hc hci
  map_zero_left x := by
    rw [collarExtension_zero H hc hci hzero]
    rfl
  map_one_left _ := rfl
  prop' t x hx := by
    change collarExtension H hc hci t x = x
    rcases x with ⟨r, x⟩
    change r = 1 at hx
    subst r
    exact collarExtension_inner H hc hci hzero t x

end PoincareConjecture.M76.CollarIsotopy
