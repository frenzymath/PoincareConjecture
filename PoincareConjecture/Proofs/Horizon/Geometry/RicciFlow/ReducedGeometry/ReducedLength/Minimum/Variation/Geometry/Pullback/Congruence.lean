import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Pullback.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Extension.Section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff Bundle
universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem curveVelocityWithin_congr {γ δ : ℝ → M} {I : Set ℝ}
    (h : Set.EqOn γ δ I) {s : ℝ} (hs : s ∈ I) :
    curveVelocityWithin (n := n) γ I s = curveVelocityWithin (n := n) δ I s := by
  unfold curveVelocityWithin
  rw [mfderivWithin_congr_of_mem h hs]
  rfl

def transferParametricExtension {C : Set ℝ} {α β : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (α s)} {Z : ∀ s, TangentSpace (𝓡 n) (β s)}
    (hcurve : EqOn α β C) (hfield : ∀ s ∈ C, Y s = Z s)
    (E : ParametricAlongCurveExtensionOn C α Y) :
    ParametricAlongCurveExtensionOn C β Z where
  extension := E.extension
  domain := E.domain
  open_domain := E.open_domain
  graph_mem s hs := by
    rw [← hcurve hs]
    exact E.graph_mem s hs
  smooth := E.smooth
  agrees s hs := by
    rw [← hcurve hs, E.agrees s hs]
    exact hfield s hs

theorem pullbackCovariantDerivative_transfer {J C : Set ℝ}
    (F : RicciFlow n M J) (time : ℝ → ℝ) {α β : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (α s)} {Z : ∀ s, TangentSpace (𝓡 n) (β s)}
    (hcurve : EqOn α β C) (hfield : ∀ s ∈ C, Y s = Z s)
    (E : ParametricAlongCurveExtensionOn C α Y) {s : ℝ} (hs : s ∈ C) :
    pullbackCovariantDerivative F time α Y C E s =
      pullbackCovariantDerivative F time β Z C (transferParametricExtension hcurve hfield E) s := by
  simp only [pullbackCovariantDerivative, transferParametricExtension]
  rw [hcurve hs, curveVelocityWithin_congr hcurve hs]

theorem pullbackCovariantDerivative_congr {J C : Set ℝ}
    (F : RicciFlow n M J) (time : ℝ → ℝ) {α β : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (α s)} {Z : ∀ s, TangentSpace (𝓡 n) (β s)}
    (hcurve : EqOn α β C) (hfield : ∀ s ∈ C, Y s = Z s)
    (E₁ : ParametricAlongCurveExtensionOn C α Y)
    (E₂ : ParametricAlongCurveExtensionOn C β Z) {s : ℝ} (hs : s ∈ C)
    (hC : UniqueDiffWithinAt ℝ C s)
    (hβ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) β s) :
    pullbackCovariantDerivative F time α Y C E₁ s =
      pullbackCovariantDerivative F time β Z C E₂ s := by
  rw [pullbackCovariantDerivative_transfer F time hcurve hfield E₁ hs]
  exact pullbackCovariantDerivative_extension_independent F time
    (transferParametricExtension hcurve hfield E₁) E₂ hs hC hβ

theorem regularizedEulerResidual_congr {J C : Set ℝ}
    (F : RicciFlow n M J) (T : ℝ) {α β : ℝ → M}
    (hcurve : EqOn α β C)
    (E₁ : ParametricAlongCurveExtensionOn C α (curveVelocityWithin (n := n) α C))
    (E₂ : ParametricAlongCurveExtensionOn C β (curveVelocityWithin (n := n) β C))
    {s : ℝ} (hs : s ∈ C) (hC : UniqueDiffWithinAt ℝ C s)
    (hβ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) β s)
    (W : TangentSpace (𝓡 n) (α s)) :
    regularizedEulerResidual F T α C E₁ s W = regularizedEulerResidual F T β C E₂ s W := by
  have hpb := pullbackCovariantDerivative_congr F (fun r ↦ T - r ^ 2) hcurve
    (fun r hr ↦ curveVelocityWithin_congr hcurve hr) E₁ E₂ hs hC hβ
  unfold regularizedEulerResidual scalarCurvatureDifferential
  rw [hpb, hcurve hs, curveVelocityWithin_congr hcurve hs]

theorem curveVelocityWithin_restrict {C D : Set ℝ} (α : ℝ → M) {s : ℝ}
    (hC : UniqueDiffWithinAt ℝ C s) (hD : UniqueDiffWithinAt ℝ D s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    curveVelocityWithin (n := n) α C s = curveVelocityWithin (n := n) α D s := by
  unfold curveVelocityWithin
  rw [mfderivWithin_eq_mfderiv hC.uniqueMDiffWithinAt hα,
    mfderivWithin_eq_mfderiv hD.uniqueMDiffWithinAt hα]

theorem pullbackCovariantDerivative_restrict {J C D : Set ℝ}
    (F : RicciFlow n M J) (time : ℝ → ℝ) {α : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (α s)} (hDC : D ⊆ C)
    (E : ParametricAlongCurveExtensionOn C α Y) {s : ℝ}
    (hC : UniqueDiffWithinAt ℝ C s) (hD : UniqueDiffWithinAt ℝ D s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    pullbackCovariantDerivative F time α Y C E s =
      pullbackCovariantDerivative F time α Y D (restrictParametricSectionExtension hDC E) s := by
  unfold pullbackCovariantDerivative restrictParametricSectionExtension
  rw [curveVelocityWithin_restrict α hC hD hα]

theorem pullbackCovariantDerivative_restrict_congr {J C D : Set ℝ}
    (F : RicciFlow n M J) (time : ℝ → ℝ) {α : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (α s)} (hDC : D ⊆ C)
    (EC : ParametricAlongCurveExtensionOn C α Y)
    (ED : ParametricAlongCurveExtensionOn D α Y) {s : ℝ} (hs : s ∈ D)
    (hC : UniqueDiffWithinAt ℝ C s) (hD : UniqueDiffWithinAt ℝ D s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    pullbackCovariantDerivative F time α Y C EC s =
      pullbackCovariantDerivative F time α Y D ED s := by
  rw [pullbackCovariantDerivative_restrict F time hDC EC hC hD hα]
  exact pullbackCovariantDerivative_extension_independent F time
    (restrictParametricSectionExtension hDC EC) ED hs hD hα

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
