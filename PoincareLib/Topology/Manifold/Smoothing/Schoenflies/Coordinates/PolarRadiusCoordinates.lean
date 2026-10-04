import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Maps.CompactifiedPolarMap
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

/-!
# The actual inverse of the regular polar cylinder map

The normalized height-radius correspondence is an explicit
homeomorphism. Compose it with Mathlib's actual unit-sphere polar
homeomorphism, retaining the literal vector formula.
See Brown1960 Theorem5 and Brown derivation018, section3.
-/

set_option autoImplicit false

open Set Metric
open scoped OnePoint

namespace BrownSchoenflies

/-- The radius is strictly positive at every non-endpoint cylinder height. -/
theorem polarRadius_pos {t : ℝ} (ht : -1 < t) (ht' : t < 1) :
    0 < polarRadius t :=
  div_pos (by linarith) (sub_pos.mpr ht')

/-- The actual normalized height-radius homeomorphism, with inverse
r |-> (r-1)/(r+1). See Brown derivation018, section3. -/
noncomputable def polarRadiusHomeomorph : Ioo (-1 : ℝ) 1 ≃ₜ Ioi (0 : ℝ) where
  toFun t := ⟨polarRadius t, polarRadius_pos t.property.1 t.property.2⟩
  invFun r := ⟨((r : ℝ) - 1) / ((r : ℝ) + 1), by
    have hr : 0 < (r : ℝ) := r.property
    have hp : 0 < (r : ℝ) + 1 := by linarith
    exact ⟨(lt_div_iff₀ hp).mpr (by linarith),
      (div_lt_iff₀ hp).mpr (by linarith)⟩⟩
  left_inv t := by
    apply Subtype.ext
    change (polarRadius t - 1) / (polarRadius t + 1) = (t : ℝ)
    have hp : 0 < polarRadius t + 1 := by
      have h := polarRadius_pos t.property.1 t.property.2
      linarith
    apply (div_eq_iff hp.ne').mpr
    have hd : (1 : ℝ) - (t : ℝ) ≠ 0 := (sub_pos.mpr t.property.2).ne'
    dsimp only [polarRadius]
    field_simp [hd]
    ring
  right_inv r := by
    apply Subtype.ext
    change polarRadius (((r : ℝ) - 1) / ((r : ℝ) + 1)) = (r : ℝ)
    have hr : 0 < (r : ℝ) := r.property
    have hp : 0 < (r : ℝ) + 1 := by linarith
    have ht : ((r : ℝ) - 1) / ((r : ℝ) + 1) < 1 :=
      (div_lt_iff₀ hp).mpr (by linarith)
    apply (div_eq_iff (sub_pos.mpr ht).ne').mpr
    field_simp [hp.ne']
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.add continuous_subtype_val).div
      (continuous_const.sub continuous_subtype_val)
      (fun t => (sub_pos.mpr t.property.2).ne')
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.sub continuous_const).div
      (continuous_subtype_val.add continuous_const)
      (fun r => ne_of_gt (by
        have hr : 0 < (r : ℝ) := r.property
        linarith))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual regular polar homeomorphism onto all nonzero vectors.
The core polar-coordinate logic is Mathlib's existing construction.
See Brown derivation018, section3. -/
noncomputable def regularPolarHomeomorph :
    (sphere (0 : E) 1 × Ioo (-1 : ℝ) 1) ≃ₜ ↥(({0} : Set E)ᶜ) :=
  ((Homeomorph.refl (sphere (0 : E) 1)).prodCongr polarRadiusHomeomorph).trans
    (homeomorphUnitSphereProd E).symm

/-- The regular polar homeomorphism has the literal radial vector formula. -/
theorem regularPolarHomeomorph_apply (z : sphere (0 : E) 1 × Ioo (-1 : ℝ) 1) :
    (regularPolarHomeomorph z : E) = (polarRadius z.2) • (z.1 : E) := rfl

/-- The regular homeomorphism is exactly the finite restriction of
the constructed closed-cylinder map, not just an abstract model.
See Brown derivation018, section3. -/
theorem compactifiedPolar_regular (z : sphere (0 : E) 1 × Ioo (-1 : ℝ) 1) :
    compactifiedPolar (z.1, ⟨(z.2 : ℝ), z.2.property.1.le, z.2.property.2.le⟩) =
      ((regularPolarHomeomorph z : E) : OnePoint E) := by
  rw [compactifiedPolar, if_neg (ne_of_lt z.2.property.2)]
  rfl

end BrownSchoenflies
