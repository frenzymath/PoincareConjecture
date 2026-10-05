import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Cone.Ends.TerminalHomothetic
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RadialRegularity
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RadialGradient

/-!
# A locally Lipschitz quadratic potential gives the finite-time obstruction

Regularity and the actual gradient construct the smooth homothetic field
from the potential's geodesic identity on the same carrier and metric.
Source: Kleiner--Lott corrected 2013, Lemma 41.4, pp. 2674-2676;
Morgan--Tian Proposition 4.22; M28 derivations 110 and 148.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- A locally Lipschitz, geodesically quadratic actual terminal potential
contradicts positive scalar in the same finite backward flow. Smoothness
and the homothetic field are conclusions of the lower regularity theorems,
not additional premises. Derivation 148. -/
theorem no_positive_terminal_scalar_of_quadratic_potential
    (P : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow 3 M (Icc a b))
    (hoperator : ∀ t ∈ Icc a b, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    (f : M → ℝ)
    (hLip : ∀ p : M, ∃ U ∈ 𝓝 (extChartAt (𝓡 3) p p), ∃ C : ℝ≥0,
      LipschitzOnWith C (f ∘ (extChartAt (𝓡 3) p).symm) U)
    (hquad : ∀ (γ : ℝ → M) (epsilon : ℝ), 0 < epsilon →
      (F.metric b).IsGeodesicOn γ (Ioo (-epsilon) (1 + epsilon)) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
          (F.metric b).tangentNorm (γ 0)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) ^ 2 / 2)
    (p : M) (hscalar : 0 < (F.connection b).scalarCurvature p) : False := by
  have hf := (F.metric b).contMDiff_of_locally_lipschitz_geodesic_quadratic f hLip hquad
  obtain ⟨hZsmooth, hZ⟩ :=
    (F.connection b).gradient_homothetic_of_geodesic_quadratic hf hquad
  exact no_positive_terminal_scalar_of_homothetic_field P hab F hoperator
    ((F.connection b).gradient f) hZsmooth hZ p hscalar

end PoincareMT.M28
