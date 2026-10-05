import PoincareLib.Geometry.CurveShortening.Comparison.Annulus
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.PlaneReflection
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Derivative.Manifold.Equiv

/-!
# Radial reflection of the annulus rectangle

The affine involution fixes the angular coordinate and sends the radial
coordinate to its complement. It preserves both volume and the rectangle.

Morgan--Tian context: Section 19.6, Lemmas 19.30-19.31, printed pp. 461-466.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold

namespace PoincareMT

/-- The affine reflection fixing the angular coordinate and sending the radial coordinate to
one minus itself. Source: Auxiliary step for MT Lemma 19.30, p. 462; the actual half-disk
collar in `proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
noncomputable def m64AnnulusFlip : LoopPlane ≃ₜ LoopPlane :=
  m60PlaneReflection.toHomeomorph.trans (Homeomorph.addRight (annulusPoint 0 1))

/-- The affine annulus reflection equals the explicit coordinate formula. Source: Auxiliary
step for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64AnnulusFlip_apply (p : LoopPlane) :
    m64AnnulusFlip p = m60PlaneReflection p + annulusPoint 0 1 := rfl

/-- Annulus reflection fixes the angular coordinate. Source: Auxiliary step for MT Lemma
19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64AnnulusFlip_coord_zero (p : LoopPlane) : m64AnnulusFlip p 0 = p 0 := by
  simp [m64AnnulusFlip_apply, m60PlaneReflection_apply, annulusPoint]

/-- Annulus reflection reverses the unit radial coordinate. Source: Auxiliary step for MT
Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64AnnulusFlip_coord_one (p : LoopPlane) : m64AnnulusFlip p 1 = 1 - p 1 := by
  simp [m64AnnulusFlip_apply, m60PlaneReflection_apply, annulusPoint]
  ring

/-- Reflection sends a displayed annulus point to the same angle at the reversed radius.
Source: Auxiliary step for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64AnnulusFlip_annulusPoint (x s : ℝ) :
    m64AnnulusFlip (annulusPoint x s) = annulusPoint x (1 - s) := by
  ext i
  fin_cases i <;>
    simp [m64AnnulusFlip_coord_zero, m64AnnulusFlip_coord_one, annulusPoint]

/-- Applying annulus reflection twice returns the original point. Source: Auxiliary step for
MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64AnnulusFlip_involutive : Function.Involutive m64AnnulusFlip := by
  intro p
  ext i
  fin_cases i <;> simp [m64AnnulusFlip_coord_zero, m64AnnulusFlip_coord_one]

/-- The annulus reflection is a Euclidean isometry. Source: Auxiliary step for MT Lemma
19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64AnnulusFlip_isometry : Isometry m64AnnulusFlip :=
  (isometry_add_right (annulusPoint 0 1)).comp m60PlaneReflection.isometry

/-- The affine radial reflection preserves planar volume. Source: Auxiliary step for MT
Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64AnnulusFlip_measurePreserving :
    MeasurePreserving m64AnnulusFlip (volume : Measure LoopPlane) volume :=
  (measurePreserving_add_right volume (annulusPoint 0 1)).comp
    m60PlaneReflection.measurePreserving

/-- A point lies in the annulus rectangle exactly when its reflection does. Source:
Auxiliary step for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64AnnulusFlip_mem_domain (p : LoopPlane) :
    m64AnnulusFlip p ∈ m64AnnulusDomain ↔ p ∈ m64AnnulusDomain := by
  change (0 ≤ m64AnnulusFlip p 0 ∧ m64AnnulusFlip p 0 ≤ curvePeriod ∧
    0 ≤ m64AnnulusFlip p 1 ∧ m64AnnulusFlip p 1 ≤ 1) ↔ _
  rw [m64AnnulusFlip_coord_zero, m64AnnulusFlip_coord_one]
  change (0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ 1 - p 1 ∧ 1 - p 1 ≤ 1) ↔
    (0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1)
  constructor <;> intro h <;> refine ⟨h.1, h.2.1, ?_, ?_⟩ <;> linarith [h.2.2.1, h.2.2.2]

/-- The annulus domain is its own preimage under radial reflection. Source: Auxiliary step
for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64AnnulusFlip_preimage_domain :
    m64AnnulusFlip ⁻¹' m64AnnulusDomain = m64AnnulusDomain :=
  Set.ext m64AnnulusFlip_mem_domain

/-- The reflection has the constant derivative fixing the angular column and negating the
radial column. Source: Auxiliary step for MT Lemma 19.30, p. 462; the actual half-disk
collar in `proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64AnnulusFlip_hasFDerivAt (p : LoopPlane) :
    HasFDerivAt m64AnnulusFlip
      m60PlaneReflection.toContinuousLinearEquiv.toContinuousLinearMap p := by
  exact m60PlaneReflection.toContinuousLinearEquiv.hasFDerivAt.add_const
    (annulusPoint 0 1)

/-- The actual manifold derivative obeys the reflection chain rule in both differentiable
and totalized cases. Source: Auxiliary step for MT Lemma 19.30, p. 462; the actual half-disk
collar in `proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem mfderiv_comp_m64AnnulusFlip
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : LoopPlane → M) (p : LoopPlane) :
    mfderiv (𝓡 2) (𝓡 n) (fun z => f (m64AnnulusFlip z)) p =
      (mfderiv (𝓡 2) (𝓡 n) f (m64AnnulusFlip p)).comp
        m60PlaneReflection.toContinuousLinearEquiv.toContinuousLinearMap := by
  have he := (m64AnnulusFlip_hasFDerivAt p).hasMFDerivAt
  by_cases hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (m64AnnulusFlip p)
  · change mfderiv (𝓡 2) (𝓡 n) (f ∘ m64AnnulusFlip) p = _
    erw [mfderiv_comp p hf he.mdifferentiableAt, he.mfderiv]
  · have hcomp : ¬MDifferentiableAt (𝓡 2) (𝓡 n)
        (fun z => f (m64AnnulusFlip z)) p := by
      intro h
      have hback := h.comp_of_eq (m64AnnulusFlip p)
        (m64AnnulusFlip_hasFDerivAt (m64AnnulusFlip p)).hasMFDerivAt.mdifferentiableAt
        (m64AnnulusFlip_involutive p)
      apply hf
      have hfun : (fun x => f (m64AnnulusFlip (m64AnnulusFlip x))) = f :=
        funext (fun x => congrArg f (m64AnnulusFlip_involutive x))
      simpa only [Function.comp_def, hfun] using hback
    rw [mfderiv_zero_of_not_mdifferentiableAt hcomp,
      mfderiv_zero_of_not_mdifferentiableAt hf, ContinuousLinearMap.zero_comp]

end PoincareMT
