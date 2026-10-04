import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates.Relabeling.Geometry
import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates

/-!
# Scalar geometry and arc derivatives under fixed relabeling

These exact identities transport the quantities in MT2007 Lemma 19.6,
Claim 19.11 and Lemma 19.14, pp. 441-447, retaining the corrected ratio
from the 2015 correction, pp. 8-9. Differentiability witnesses prevent
totalized derivatives from being used as a chain rule without regularity.
See `2026-09-21-fixed-relabeling-geometry.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (d : ℝ → ℝ → M)
  {phi : ℝ → ℝ} {t x : ℝ}

/-- Squared curvature keeps the actual metric and basepoint under relabeling.
MT2007 Lemma 19.6, pp. 441-442. -/
theorem curvatureSquared_comp
    (hd : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t))
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hS : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨d y t, spatialUnitTangent F d t y⟩ : TangentBundle (𝓡 n) M))
      (phi x)) :
    m62CurvatureSquared F (fun y s => d (phi y) s) t x =
      m62CurvatureSquared F d t (phi x) := by
  unfold m62CurvatureSquared
  rw [curvatureVector_comp F d hd hphi hpos hS]

/-- Curvature itself is invariant, including its zero set.
MT2007 Lemma 19.14, p. 447. -/
theorem curvature_comp
    (hd : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t))
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hS : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨d y t, spatialUnitTangent F d t y⟩ : TangentBundle (𝓡 n) M))
      (phi x)) :
    m62Curvature F (fun y s => d (phi y) s) t x = m62Curvature F d t (phi x) := by
  unfold m62Curvature
  rw [curvatureSquared_comp F d hd hphi hpos hS]

/-- Regularization commutes with fixed relabeling for every epsilon.
MT2015Correction Corollary 0.3, pp. 6-7. -/
theorem regularizedCurvature_comp
    (hd : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t))
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hS : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨d y t, spatialUnitTangent F d t y⟩ : TangentBundle (𝓡 n) M))
      (phi x)) (epsilon : ℝ) :
    m62RegularizedCurvature F (fun y s => d (phi y) s) epsilon t x =
      m62RegularizedCurvature F d epsilon t (phi x) := by
  unfold m62RegularizedCurvature
  rw [curvatureSquared_comp F d hd hphi hpos hS]

/-- The Ricci pairing uses the same actual tangent and connection.
MT2007 Lemma 19.6, pp. 441-442. -/
theorem tangentRicci_comp
    (hd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t) (phi x))
    (hphi : DifferentiableAt ℝ phi x) (hpos : 0 < deriv phi x) :
    m62TangentRicci F (fun y s => d (phi y) s) t x =
      m62TangentRicci F d t (phi x) := by
  unfold m62TangentRicci
  rw [spatialUnitTangent_comp F d hd hphi.hasDerivAt hpos]

/-- The scalar arc derivative cancels the positive change-of-parameter
factor with actual derivative witnesses; MT2007 pp. 441-442. -/
theorem arcDerivative_comp {f : ℝ → ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t) (phi x))
    (hphi : DifferentiableAt ℝ phi x) (hpos : 0 < deriv phi x)
    (hf : DifferentiableAt ℝ f (phi x)) :
    m62ArcDerivative F (fun y s => d (phi y) s) t (fun y => f (phi y)) x =
      m62ArcDerivative F d t f (phi x) := by
  unfold m62ArcDerivative
  have hcomp : deriv (fun y => f (phi y)) x = deriv f (phi x) * deriv phi x :=
    deriv_comp x hf hphi
  rw [curveSpeed_comp F d hd hphi.hasDerivAt hpos.le, hcomp]
  rw [mul_inv_rev]
  calc
    (curveSpeed F d t (phi x))⁻¹ * (deriv phi x)⁻¹ * (deriv f (phi x) * deriv phi x) =
        (curveSpeed F d t (phi x))⁻¹ * deriv f (phi x) *
          ((deriv phi x)⁻¹ * deriv phi x) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hpos.ne', mul_one]

/-- Iterated scalar arc differentiation preserves the varying speed
coefficient and requires only first derivatives of the relabeling.
MT2007 Claim 19.11, p. 446; correction Lemma 19.14, pp. 8-9. -/
theorem arcSecondDerivative_comp {f : ℝ → ℝ}
    (hd : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => d y t))
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hf : ∀ y, DifferentiableAt ℝ f (phi y))
    (hDf : DifferentiableAt ℝ (m62ArcDerivative F d t f) (phi x)) :
    m62ArcSecondDerivative F (fun y s => d (phi y) s) t (fun y => f (phi y)) x =
      m62ArcSecondDerivative F d t f (phi x) := by
  have hfirst : m62ArcDerivative F (fun y s => d (phi y) s) t (fun y => f (phi y)) =
      fun y => m62ArcDerivative F d t f (phi y) :=
    funext fun y => arcDerivative_comp F d (hd (phi y)) (hphi y) (hpos y) (hf y)
  unfold m62ArcSecondDerivative
  rw [hfirst]
  exact arcDerivative_comp F d (hd (phi x)) (hphi x) (hpos x) hDf

section CircleProduct

variable {F' : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
  (P : M62.CircleProductData F' circumference) (c : ℝ → ℝ → P.charts.Point)

/-- The actual unit-circle pairing is invariant under a positive relabeling.
MT2007 Claim 19.11 and Definition 19.12, p. 446. -/
theorem slope_comp
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (fun y => c y t) (phi x))
    (hphi : DifferentiableAt ℝ phi x) (hpos : 0 < deriv phi x) :
    m62Slope P (fun y s => c (phi y) s) t x = m62Slope P c t (phi x) := by
  let := P.charts.chartedSpace
  unfold m62Slope
  rw [spatialUnitTangent_comp P.flow c hc hphi.hasDerivAt hpos]

/-- The corrected regularized-curvature/slope ratio retains its exact value.
No positivity is needed for this identity; correction Lemma 19.14, pp. 8-9. -/
theorem rampRatio_comp
    (hc : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (fun y => c y t))
    (hphi : Differentiable ℝ phi) (hpos : ∀ y, 0 < deriv phi y)
    (hS : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)).tangent
      (fun y => (⟨c y t, spatialUnitTangent P.flow c t y⟩ :
        TangentBundle (𝓡 (n + 1)) P.charts.Point)) (phi x)) (epsilon : ℝ) :
    m63RampRatio P (fun y s => c (phi y) s) epsilon t x =
      m63RampRatio P c epsilon t (phi x) := by
  let := P.charts.chartedSpace
  unfold m63RampRatio
  rw [regularizedCurvature_comp P.flow c hc hphi hpos hS,
    slope_comp P c (hc (phi x)) (hphi x) (hpos x)]

end CircleProduct

end PoincareMT.M63
