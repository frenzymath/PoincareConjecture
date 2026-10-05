import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineHyperplaneCoordinates
import Mathlib.Topology.Homeomorph.Defs

/-!
# Literal product coordinates for an original affine halfspace

Subtract the given affine height in the slope-one direction, use
the existing zero-hyperplane coordinates, and retain the height
as the second coordinate. See Wall derivation006, section2.
-/

set_option autoImplicit false

open Set

namespace ContinuousAffineMap

/-- A slope-one affine scalar is the literal second coordinate of
an actual ambient product homeomorphism. Both inverse identities are
constructed from the zero-level coordinates. See Wall006, section2. -/
theorem exists_halfspace_product_homeomorph
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (ell : E →ᴬ[ℝ] ℝ) (v : E) (hv : ell.contLinear v = 1)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1) :
    ∃ H : E ≃ₜ (F × ℝ), ∀ z, (H z).2 = ell z := by
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro h
    have hval : ell.toAffineMap.linear v = 1 := hv
    rw [h] at hval
    norm_num at hval
  obtain ⟨a, r, hra, har, ha⟩ := ell.toAffineMap.exists_zeroLevel_coordinates hell hdim
  have hadd (z : E) (t : ℝ) : ell (z + t • v) = ell z + t := by
    simpa only [vadd_eq_add, map_smul, hv, smul_eq_mul, mul_one, add_comm]
      using ell.map_vadd z (t • v)
  have hzero (z : E) : ell (z - ell z • v) = 0 := by
    simpa only [neg_smul, ← sub_eq_add_neg, sub_self] using hadd z (-ell z)
  have hheight (w : F) (t : ℝ) : ell (a w + t • v) = t := by
    have haw : ell (a w) = 0 := ha w
    rw [hadd, haw, zero_add]
  let H : E ≃ₜ (F × ℝ) :=
    { toFun := fun z => (r (z - ell z • v), ell z)
      invFun := fun z => a z.1 + z.2 • v
      left_inv := by
        intro z
        change a (r (z - ell z • v)) + ell z • v = z
        rw [har (hzero z), sub_add_cancel]
      right_inv := by
        intro z
        change (r (a z.1 + z.2 • v - ell (a z.1 + z.2 • v) • v),
          ell (a z.1 + z.2 • v)) = z
        rw [hheight]
        simp only [add_sub_cancel_right]
        exact Prod.ext (hra z.1) rfl
      continuous_toFun :=
        (r.continuous.comp (continuous_id.sub
          (ell.continuous.smul continuous_const))).prodMk ell.continuous
      continuous_invFun :=
        (a.continuous.comp continuous_fst).add (continuous_snd.smul continuous_const) }
  exact ⟨H, fun _ => rfl⟩

end ContinuousAffineMap
