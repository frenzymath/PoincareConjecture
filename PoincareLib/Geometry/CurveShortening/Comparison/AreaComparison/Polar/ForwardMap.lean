import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AreaComparison.Polar.AnnulusMap
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Polar.Derivatives
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Smooth coordinates from the rectangle to the polar collar

The forward map has explicit angular and radial differential columns. Its
composition with the polar collar recovers the original periodic rectangle
map wherever the radius is positive, independent of the angular branch cut.

Morgan--Tian context: Section 19.6, Lemmas 19.30-19.31, printed pp. 461-466.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareMT

open Proofs.M58

/-- Map the rectangle to the half-disk collar by its literal angle and affine positive
radius. Source: Auxiliary step for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
noncomputable def m64PolarForwardMap (p : LoopPlane) : LoopPlane :=
  ((1 / 2 : ℝ) * (p 1 + 1)) • angularPoint (p 0)

/-- Compute the forward polar map's actual angular and radial differential columns. Source:
Auxiliary step for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64PolarForwardMap_hasFDerivAt (p : LoopPlane) :
    HasFDerivAt (𝕜 := ℝ) m64PolarForwardMap
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).smulRight
          (((1 / 2 : ℝ) * (p 1 + 1)) • angularVector (p 0)) +
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).smulRight
          ((1 / 2 : ℝ) • angularPoint (p 0))) p := by
  have h0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p (0 : Fin 2)
  have h1 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p (1 : Fin 2)
  have hs := (h1.add_const 1).const_mul (1 / 2 : ℝ)
  have ha := (hasDerivAt_angularPoint (p 0)).hasFDerivAt.comp p h0
  convert! hs.smul ha using 1
  ext w i
  change w 0 * (((1 / 2 : ℝ) * (p 1 + 1)) * angularVector (p 0) i) +
      w 1 * ((1 / 2 : ℝ) * angularPoint (p 0) i) =
    ((1 / 2 : ℝ) * (p 1 + 1)) * (w 0 * angularVector (p 0) i) +
      ((1 / 2 : ℝ) * w 1) * angularPoint (p 0) i
  ring

/-- The descended collar composed with positive-radius forward coordinates equals the
original periodic map. Source: Auxiliary step for MT Lemma 19.30, p. 462; the actual
half-disk collar in `proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64PolarAnnulusMap_comp_forward
    {Y : Type*} {f : LoopPlane → Y}
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    {p : LoopPlane} (hp : -1 < p 1) :
    m64PolarAnnulusMap f (m64PolarForwardMap p) = f p := by
  have hr : 0 < (1 / 2 : ℝ) * (p 1 + 1) := by linarith
  have h := m64PolarAnnulusMap_polar hperiodic hr (p 0)
  have harg : 2 * ((1 / 2 : ℝ) * (p 1 + 1)) - 1 = p 1 := by ring
  rw [harg] at h
  have hpoint : annulusPoint (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
  simpa only [m64PolarForwardMap, hpoint] using h

/-- The collar-to-rectangle identity holds on a full neighborhood wherever the radius is
positive. Source: Auxiliary step for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
theorem m64PolarAnnulusMap_comp_forward_eventually
    {Y : Type*} {f : LoopPlane → Y}
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    {p : LoopPlane} (hp : -1 < p 1) :
    (m64PolarAnnulusMap f ∘ m64PolarForwardMap) =ᶠ[𝓝 p] f := by
  have hopen : IsOpen {q : LoopPlane | -1 < q 1} :=
    isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)
  filter_upwards [hopen.mem_nhds hp] with q hq
  exact m64PolarAnnulusMap_comp_forward hperiodic hq

end PoincareMT
