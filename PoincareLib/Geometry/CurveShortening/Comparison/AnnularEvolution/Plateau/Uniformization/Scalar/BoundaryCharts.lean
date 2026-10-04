import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.Regularity
import PoincareLib.Geometry.Manifold.SmoothDomain.HalfSpaceChart

/-!
# Actual regular boundary charts for the scalar annulus

The polynomial `(norm squared - 1) * (4 - norm squared)` defines the fixed
annulus as a positive superlevel and has nonzero differential on both
boundary circles. The lower implicit-function construction therefore gives
genuine smooth half-space charts, without a supplied smooth-domain record.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Function
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- A global smooth defining function for the two boundary circles. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-nonconstancy.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
def scalarAnnulusDefining (x : Plane) : ℝ := (‖x‖ ^ 2 - 1) * (4 - ‖x‖ ^ 2)

/-- The literal polynomial defining the two annular boundaries is globally smooth. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-nonconstancy.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalarAnnulusDefining_smooth :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ scalarAnnulusDefining := by
  apply contMDiff_iff_contDiff.mpr
  exact ((contDiff_norm_sq ℝ).sub contDiff_const).mul
    (contDiff_const.sub (contDiff_norm_sq ℝ))

/-- The positive superlevel of the defining polynomial is exactly the open annulus of radii
one and two. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project
construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-nonconstancy.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalarAnnulusDefining_pos (x : Plane) :
    0 < scalarAnnulusDefining x ↔ x ∈ scalarAnnulus := by
  have hn := norm_nonneg x
  change 0 < (‖x‖ ^ 2 - 1) * (4 - ‖x‖ ^ 2) ↔ 1 < ‖x‖ ∧ ‖x‖ < 2
  constructor
  · intro h
    rcases mul_pos_iff.mp h with h | h <;> constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    apply mul_pos <;> nlinarith

/-- The defining differential is surjective at every point of either actual boundary circle.
Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-nonconstancy.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem scalarAnnulusDefining_regular {a : Plane} (ha : ‖a‖ = 1 ∨ ‖a‖ = 2) :
    Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) scalarAnnulusDefining a) := by
  suffices hs : Surjective (fderiv ℝ scalarAnnulusDefining a) by
    simpa only [mfderiv_eq_fderiv, TangentSpace] using hs
  have hd := ((hasStrictFDerivAt_norm_sq a).hasFDerivAt.sub_const 1).mul
    ((hasFDerivAt_const (4 : ℝ) a).sub (hasStrictFDerivAt_norm_sq a).hasFDerivAt)
  have heq : fderiv ℝ scalarAnnulusDefining a a =
      (5 - 2 * ‖a‖ ^ 2) * (2 * ‖a‖ ^ 2) := by
    have h := congrArg (fun L : Plane →L[ℝ] ℝ => L a) hd.fderiv
    change fderiv ℝ scalarAnnulusDefining a a = _ at h
    rw [h]
    simp only [add_apply, smul_apply, sub_apply, zero_apply, smul_eq_mul,
      innerSL_apply_apply, real_inner_self_eq_norm_sq, Pi.sub_apply]
    ring
  have hn : fderiv ℝ scalarAnnulusDefining a a ≠ 0 := by
    rw [heq]
    rcases ha with ha | ha <;> norm_num [ha]
  intro y
  refine ⟨(y / fderiv ℝ scalarAnnulusDefining a a) • a, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hn]

/-- Every point on either actual annular boundary circle has a smooth parametrization whose
positive first coordinate is exactly the annulus. Source: Morgan--Tian (2007), Lemma 19.15,
pp. 447-449, with the project construction in
`proof-work/tasks/M64/derivations/2026-09-24-annular-scalar-nonconstancy.md`; scalar
boundary and energy details are recorded in
`proof-work/tasks/M64/reviews/2026-09-27-round1-uniformization-scalar.md`. -/
theorem exists_scalarAnnulus_boundary_chart {a : Plane}
    (ha : ‖a‖ = 1 ∨ ‖a‖ = 2) :
    ∃ e : OpenPartialHomeomorph Plane Plane,
      a ∈ e.target ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      (e.symm a) 0 = 0 ∧
      ∀ z ∈ e.source, e z ∈ scalarAnnulus ↔ 0 < z 0 := by
  obtain ⟨φ, haφ, hφ, hφi, hfirst, -⟩ :=
    Poincare.Manifold.exists_normalized_regular_point_chart
      (n := 1) (by simp : Module.finrank ℝ Plane = 1 + 1)
      scalarAnnulusDefining_smooth a 0 (scalarAnnulusDefining_regular ha)
  refine ⟨φ.symm, haφ, hφi, hφ, ?_, ?_⟩
  · change φ a 0 = 0
    rw [hfirst a haφ, sub_zero]
    rcases ha with ha | ha <;> norm_num [scalarAnnulusDefining, ha]
  · intro z hz
    have h := hfirst (φ.symm z) (φ.map_target hz)
    rw [φ.right_inv hz, sub_zero] at h
    rw [← scalarAnnulusDefining_pos, ← h]

end PoincareMT.M64Uniformization
