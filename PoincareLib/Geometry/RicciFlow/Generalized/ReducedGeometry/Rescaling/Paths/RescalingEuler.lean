import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ParabolicRescaling
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Rescaling.Geometry.RescalingPullback
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Rescaling.Paths.RescalingPaths
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquarePullback

/-!
# Actual Euler equations under parabolic rescaling

Morgan-Tian Lemma 6.72 and Remark 6.73, p. 141. The actual original-time
pullback extension is reparameterized and scaled with the path velocity.
Every paired Euler term then has the same inverse metric scale.
-/

set_option autoImplicit false
-- The actual target retains the ambient manifold and transported horizontal fibers.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

include hQ in
/-- The genuine strict backward interval maps to the old one under
division by the scale. Lemma 6.72, p. 141. -/
theorem rescalingParameter_mapsTo (τ₁ τ₂ : ℝ) :
    MapsTo (fun s : ℝ => s / Q) (Ioo (Q * τ₁) (Q * τ₂)) (Ioo τ₁ τ₂) := by
  intro s hs
  exact ⟨(lt_div_iff₀ hQ).mpr (by simpa only [mul_comm] using hs.1),
    (div_lt_iff₀ hQ).mpr (by simpa only [mul_comm] using hs.2)⟩

/-- The actual original-time velocity extension is transported and
reparameterized with its inverse scale. Lemma 6.72, p. 141. -/
noncomputable def rescalingPathExtension
    {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity) :
    M14PullbackExtension (rescalingTransport hM12 hM13 G Q hQ a)
      (rescalingPath hM12 hM13 G Q hQ a p).curve (Ioo (Q * τ₁) (Q * τ₂))
      (rescalingPath hM12 hM13 G Q hQ a p).horizontal_velocity :=
  pullbackExtensionSmulComp (rescalingPullbackExtension hM12 hM13 G Q hQ a E)
    (fun s => s / Q) (fun _ => Q⁻¹) (contDiff_id.div_const Q) contDiff_const
    (rescalingParameter_mapsTo Q hQ τ₁ τ₂)

/-- Covariant acceleration has inverse-square scale along the actual
rescaled original-time path. Lemma 6.72, p. 141. -/
theorem rescalingPath_covariantDerivative
    {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    {s : ℝ} (hs : s ∈ Ioo (Q * τ₁) (Q * τ₂)) :
    M14HorizontalCovariantDerivative (rescalingTransport hM12 hM13 G Q hQ a)
      (rescalingPath hM12 hM13 G Q hQ a p).curve (Ioo (Q * τ₁) (Q * τ₂))
      (rescalingPath hM12 hM13 G Q hQ a p).horizontal_velocity
      (rescalingPathExtension hM12 hM13 G Q hQ a p E) s =
      (Q⁻¹ * Q⁻¹) • M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (p.curve (s / Q))
        (M14HorizontalCovariantDerivative G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity
          E (s / Q)) := by
  have hm := rescalingParameter_mapsTo Q hQ τ₁ τ₂
  have hderiv : deriv (fun r : ℝ => r / Q) s = Q⁻¹ := by
    simpa only [id_eq, one_div] using ((hasDerivAt_id s).div_const Q).deriv
  have hγ := (p.curve_regular.contMDiffAt (isOpen_Ioo.mem_nhds (hm hs))).mdifferentiableAt
    (by simp)
  have h := horizontalCovariantDerivative_smul_comp
    (rescalingPullbackExtension hM12 hM13 G Q hQ a E)
    (fun r => r / Q) (fun _ => Q⁻¹) (contDiff_id.div_const Q) contDiff_const hm
    hs (isOpen_Ioo.mem_nhds hs) (isOpen_Ioo.mem_nhds (hm hs)) hγ
  simp only [deriv_const, zero_smul, zero_add, hderiv,
    rescalingPullbackDerivative hM12 hM13 G Q hQ a E (hm hs)] at h
  exact h

/-- Each paired original-time Euler term has the same inverse scale.
Lemma 6.72 and Remark 6.73, p. 141. -/
theorem rescalingEulerResidual
    {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    {s : ℝ} (hs : s ∈ Ioo (Q * τ₁) (Q * τ₂))
    (W : G.Horizontal (p.curve (s / Q))) :
    M14EulerResidual (rescalingTransport hM12 hM13 G Q hQ a)
      (rescalingPath hM12 hM13 G Q hQ a p)
      (rescalingPathExtension hM12 hM13 G Q hQ a p E) s
      (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (p.curve (s / Q)) W) =
      Q⁻¹ * M14EulerResidual G p E (s / Q) W := by
  unfold M14EulerResidual
  rw [rescalingPath_covariantDerivative hM12 hM13 G Q hQ a p E hs]
  change (M13.parabolicSpacetime G.spacetime Q hQ a).horizontalMetric.inner
      (p.curve (s / Q))
      ((Q⁻¹ * Q⁻¹) • M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a
        (p.curve (s / Q))
        (M14HorizontalCovariantDerivative G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity E (s / Q)))
      (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (p.curve (s / Q)) W) -
    (1 / 2 : ℝ) * M14HorizontalScalarDifferential (rescalingTransport hM12 hM13 G Q hQ a)
      (p.curve (s / Q)) W.val +
    (1 / (2 * s) : ℝ) * (M13.parabolicSpacetime G.spacetime Q hQ a).horizontalMetric.inner
      (p.curve (s / Q))
      (Q⁻¹ • M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a
        (p.curve (s / Q)) (p.horizontal_velocity (s / Q)))
      (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (p.curve (s / Q)) W) +
    2 * horizontalRicci (rescalingLeafwise G Q hQ a) (p.curve (s / Q))
      (Q⁻¹ • M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a
        (p.curve (s / Q)) (p.horizontal_velocity (s / Q)))
      (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (p.curve (s / Q)) W) = _
  erw [horizontalRicci_smul_left (G := rescalingTransport hM12 hM13 G Q hQ a) hM12]
  erw [rescalingHorizontalRicci G.spacetime G.slices Q hQ a G.leafwise
    (rescalingLeafwise G Q hQ a) hM13]
  simp only [map_smul, smul_apply, smul_eq_mul, M13.parabolicSpacetime_metric,
    rescalingScalarDifferential hM12 hM13 G Q hQ a]
  field_simp [hQ.ne']

/-- Every actual original-time Euler path transports to an Euler path.
Lemma 6.72 and Remark 6.73, p. 141. -/
theorem rescalingEulerEquation
    {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    (he : M14EulerEquation G p E) :
    M14EulerEquation (rescalingTransport hM12 hM13 G Q hQ a)
      (rescalingPath hM12 hM13 G Q hQ a p)
      (rescalingPathExtension hM12 hM13 G Q hQ a p E) := by
  intro s hs W
  obtain ⟨W, rfl⟩ := (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a
    (p.curve (s / Q))).surjective W
  rw [rescalingEulerResidual hM12 hM13 G Q hQ a p E hs W,
    he _ (rescalingParameter_mapsTo Q hQ τ₁ τ₂ hs) W, mul_zero]

/-- Actual original-time Euler residuals do not depend on the
extension witness along a regular backward path. Lemma 6.8, pp. 108-109,
as used in Lemma 6.72, p. 141. -/
theorem rescalingEuler_extension_independent
    {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
    (E F : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    {s : ℝ} (hs : s ∈ Ioo τ₁ τ₂) (W : G.Horizontal (p.curve s)) :
    M14EulerResidual G p E s W = M14EulerResidual G p F s W := by
  have hd := horizontalCovariantDerivative_extension_independent E F hs
    (isOpen_Ioo.uniqueDiffOn s hs) ((p.curve_regular s hs).mdifferentiableWithinAt (by simp))
  simp only [M14EulerResidual, hd]

/-- The Euler equation of a linked target path implies the source
equation for any actual extension witness. Lemma 6.72, p. 141. -/
theorem eulerEquation_of_rescaling
    {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    (F : M14PullbackExtension (rescalingTransport hM12 hM13 G Q hQ a)
      (rescalingPath hM12 hM13 G Q hQ a p).curve (Ioo (Q * τ₁) (Q * τ₂))
      (rescalingPath hM12 hM13 G Q hQ a p).horizontal_velocity)
    (he : M14EulerEquation (rescalingTransport hM12 hM13 G Q hQ a)
      (rescalingPath hM12 hM13 G Q hQ a p) F) : M14EulerEquation G p E := by
  intro s hs W
  have hs' : Q * s ∈ Ioo (Q * τ₁) (Q * τ₂) :=
    ⟨mul_lt_mul_of_pos_left hs.1 hQ, mul_lt_mul_of_pos_left hs.2 hQ⟩
  have hz : ∀ V : G.Horizontal (p.curve (Q * s / Q)),
      M14EulerResidual G p E (Q * s / Q) V = 0 := by
    intro V
    have hzero := he (Q * s) hs'
      (M13.parabolicSpacetimeHorizontal G.spacetime Q hQ a (p.curve (Q * s / Q)) V)
    rw [rescalingEuler_extension_independent (rescalingTransport hM12 hM13 G Q hQ a)
      (rescalingPath hM12 hM13 G Q hQ a p) F
      (rescalingPathExtension hM12 hM13 G Q hQ a p E) hs',
      rescalingEulerResidual hM12 hM13 G Q hQ a p E hs' V] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (inv_ne_zero hQ.ne')
  rw [mul_div_cancel_left₀ _ hQ.ne'] at hz
  exact hz W

end PoincareMT.M14
