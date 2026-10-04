import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Topology3D.Geometry.Services
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Period coordinates on the prescribed Euclidean unit circle

Identify the additive period circle with the actual `UnitCircle` and
construct a smooth local time function using a rotated logarithm. The
logarithm is differentiated only at a point where its argument is one.
These are the angular coordinates in the reviewed period-circle-planar
adapter derivation of 2026-09-22, for Hatcher, Notes on Basic 3-Manifold
Topology, Theorem 1.1, pp. 1-2.
-/

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareMT.M25.Topology3D

/-- The native complex circle and the prescribed Euclidean unit circle
are identified by the orthonormal real and imaginary coordinates. -/
noncomputable def complexUnitCircleHomeomorph : Circle ≃ₜ UnitCircle :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype (fun z => by
    change z ∈ sphere (0 : ℂ) 1 ↔ Complex.orthonormalBasisOneI.repr z ∈ sphere (0 : E2) 1
    simp only [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map])

/-- The circle identification is smooth for the existing sphere models. -/
theorem complexUnitCircleHomeomorph_contMDiff :
    ContMDiff (𝓡 1) (𝓡 1) ∞ complexUnitCircleHomeomorph := by
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  have hi : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) :=
    contMDiff_coe_sphere (E := ℂ) (n := 1)
  exact (Complex.orthonormalBasisOneI.repr.contDiff.contMDiff.comp
    hi).codRestrict_sphere _

/-- The inverse identification is smooth in the same sphere models. -/
theorem complexUnitCircleHomeomorph_symm_contMDiff :
    ContMDiff (𝓡 1) (𝓡 1) ∞ complexUnitCircleHomeomorph.symm := by
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  have hi : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ ((↑) : UnitCircle → E2) := contMDiff_coe_sphere
  exact (Complex.orthonormalBasisOneI.repr.symm.contDiff.contMDiff.comp
    hi).codRestrict_sphere _

/-- A nonzero additive period gives the full Euclidean circle. -/
noncomputable def periodUnitCircleHomeomorph (T : ℝ) (hT : T ≠ 0) :
    AddCircle T ≃ₜ UnitCircle :=
  (AddCircle.homeomorphCircle hT).trans complexUnitCircleHomeomorph

/-- The angular parametrization with the prescribed real period. -/
noncomputable def periodCircleParam (T : ℝ) (s : ℝ) : UnitCircle :=
  complexUnitCircleHomeomorph (Circle.exp (2 * Real.pi / T * s))

/-- The angular parametrization is the exact real lift of the period
homeomorphism, with no choice of discontinuous representatives. -/
theorem periodUnitCircleHomeomorph_coe (T : ℝ) (hT : T ≠ 0) (s : ℝ) :
    periodUnitCircleHomeomorph T hT (s : AddCircle T) = periodCircleParam T s := by
  change complexUnitCircleHomeomorph (AddCircle.homeomorphCircle hT (s : AddCircle T)) = _
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  rfl

/-- The angular parametrization is smooth even as a sphere-valued map. -/
theorem periodCircleParam_contMDiff (T : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ (periodCircleParam T) :=
  complexUnitCircleHomeomorph_contMDiff.comp
    (contMDiff_circleExp.comp ((contDiff_const.mul contDiff_id).contMDiff))

/-- At every point of the Euclidean circle there is a smooth local time
function. Its right-inverse identity holds everywhere, while smoothness
is asserted only at the chosen point away from the logarithm cut. -/
theorem exists_periodCircle_local_time (T : ℝ) (hT : T ≠ 0) (q : UnitCircle) :
    ∃ s : UnitCircle → ℝ, ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ s q ∧
      periodCircleParam T ∘ s = id := by
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  let J := complexUnitCircleHomeomorph
  let z₀ : Circle := J.symm q
  let r : UnitCircle → Circle := fun p => z₀⁻¹ * J.symm p
  let k : ℝ := T / (2 * Real.pi)
  let s : UnitCircle → ℝ := fun p =>
    k * Complex.arg (z₀ : ℂ) + k * (Complex.log (r p : ℂ)).im
  have hr : ContMDiff (𝓡 1) (𝓡 1) ∞ r :=
    contMDiff_const.mul complexUnitCircleHomeomorph_symm_contMDiff
  have hr₀ : (r q : ℂ) = 1 := by simp [r, z₀]
  have hlog : ContDiffAt ℝ ∞ Complex.log (r q : ℂ) := by
    rw [hr₀]
    exact (Complex.contDiffAt_log Complex.one_mem_slitPlane).restrict_scalars ℝ
  have hlogr : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun p => Complex.log (r p : ℂ)) q :=
    hlog.comp_contMDiffAt (f := fun p : UnitCircle => (r p : ℂ))
      (((contMDiff_coe_sphere (E := ℂ) (n := 1) :
      ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ))).comp hr) q)
  have haff : ContDiff ℝ ∞ (fun x : ℝ => k * Complex.arg (z₀ : ℂ) + k * x) :=
    contDiff_const.add (contDiff_const.mul contDiff_id)
  have hs : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ s q :=
    haff.comp_contMDiffAt (Complex.imCLM.contDiff.comp_contMDiffAt hlogr)
  have hk : 2 * Real.pi / T * k = 1 := by
    dsimp [k]
    field_simp [hT, Real.pi_ne_zero]
  refine ⟨s, hs, funext fun p => ?_⟩
  have hangle : 2 * Real.pi / T * s p =
      Complex.arg (z₀ : ℂ) + Complex.arg (r p : ℂ) := by
    dsimp [s]
    rw [mul_add, ← mul_assoc, hk, one_mul, ← mul_assoc, hk, one_mul, Complex.log_im]
  change J (Circle.exp (2 * Real.pi / T * s p)) = p
  rw [hangle, Circle.exp_add, Circle.exp_arg, Circle.exp_arg]
  simp only [r, mul_inv_cancel_left, J.apply_symm_apply]

end PoincareMT.M25.Topology3D
