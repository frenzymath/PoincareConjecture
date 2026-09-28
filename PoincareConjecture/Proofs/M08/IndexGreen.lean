import PoincareConjecture.Proofs.M08.IndexQuadratic
import PoincareConjecture.Proofs.M08.IndexMetricPair
import PoincareConjecture.Proofs.M08.IndexContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def pullbackIndexPairDensity {J C : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    {α : ℝ → M} {Y W : ∀ s, TangentSpace (𝓡 n) (α s)}
    (EY : ParametricAlongCurveExtensionOn C α Y)
    (EW : ParametricAlongCurveExtensionOn C α W) (s : ℝ) : ℝ :=
  regularizedIndexPairDensity F T α C s (Y s) (W s)
    (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y C EY s)
    (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α W C EW s)

def pullbackIndexBoundaryPair {J C : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    {α : ℝ → M} {Y : ∀ s, TangentSpace (𝓡 n) (α s)}
    (EY : ParametricAlongCurveExtensionOn C α Y)
    (W : ∀ s, TangentSpace (𝓡 n) (α s)) (s : ℝ) : ℝ :=
  (F.metric (T - s ^ 2)).inner (α s)
    (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y C EY s) (W s)

def pullbackJacobiPairDensity {J C : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    {α : ℝ → M} {Y : ∀ s, TangentSpace (𝓡 n) (α s)}
    (EY : ParametricAlongCurveExtensionOn C α Y)
    (EDY : ParametricAlongCurveExtensionOn C α
      (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y C EY))
    (W : ∀ s, TangentSpace (𝓡 n) (α s)) (s : ℝ) : ℝ :=
  jacobiPairResidual F T α C s (Y s)
    (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y C EY s)
    (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
      (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y C EY) C EDY s) (W s)

theorem pullbackIndexBoundaryPair_hasDerivAt {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ r ∈ Icc a b, T - r ^ 2 ∈ J)
    {U : Set ℝ} (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (Y W : ∀ s, TangentSpace (𝓡 n) (α s))
    (EY : ParametricAlongCurveExtensionOn (Icc a b) α Y)
    (EDY : ParametricAlongCurveExtensionOn (Icc a b) α
      (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y (Icc a b) EY))
    (EW : ParametricAlongCurveExtensionOn (Icc a b) α W)
    {s : ℝ} (hs : s ∈ Ioo a b) :
    HasDerivAt (pullbackIndexBoundaryPair F T EY W)
      (pullbackIndexPairDensity F T EY EW s + pullbackJacobiPairDensity F T EY EDY W s) s := by
  have h := pullback_metric_pair_hasDerivAt F hM04 T hab htime hU hCU α hα
    (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y (Icc a b) EY) W EDY EW hs
  have hid := regularizedIndexPairDensity_green_value (C := Icc a b) F hM04 T α s (Y s) (W s)
    (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y (Icc a b) EY s)
    (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α W (Icc a b) EW s)
    (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
      (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y (Icc a b) EY) (Icc a b) EDY s)
  exact hid.symm ▸ h

theorem pullbackIndexPairDensity_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ r ∈ Icc a b, T - r ^ 2 ∈ J)
    {U : Set ℝ} (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (Y W : ∀ s, TangentSpace (𝓡 n) (α s))
    (EY : ParametricAlongCurveExtensionOn (Icc a b) α Y)
    (EW : ParametricAlongCurveExtensionOn (Icc a b) α W) :
    ContDiffOn ℝ ∞ (pullbackIndexPairDensity F T EY EW) (Icc a b) := by
  exact regularizedIndexPairDensity_contDiffOn F hM04 T hab htime hU hCU α hα Y W _ _
    (parametricExtension_along_contMDiffOn EY (hα.mono hCU))
    (parametricExtension_along_contMDiffOn EW (hα.mono hCU))
    (pullbackCovariantDerivative_contMDiffOn F T hab htime hU hCU α hα Y EY)
    (pullbackCovariantDerivative_contMDiffOn F T hab htime hU hCU α hα W EW)

theorem pullbackJacobiPairDensity_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ r ∈ Icc a b, T - r ^ 2 ∈ J)
    {U : Set ℝ} (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (Y W : ∀ s, TangentSpace (𝓡 n) (α s))
    (EY : ParametricAlongCurveExtensionOn (Icc a b) α Y)
    (EDY : ParametricAlongCurveExtensionOn (Icc a b) α
      (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y (Icc a b) EY))
    (EW : ParametricAlongCurveExtensionOn (Icc a b) α W) :
    ContDiffOn ℝ ∞ (pullbackJacobiPairDensity F T EY EDY W) (Icc a b) := by
  exact jacobiPairResidual_contDiffOn F hM04 T hab htime hU hCU α hα Y _ _ W
    (parametricExtension_along_contMDiffOn EY (hα.mono hCU))
    (parametricExtension_along_contMDiffOn EDY (hα.mono hCU))
    (pullbackCovariantDerivative_contMDiffOn F T hab htime hU hCU α hα _ EDY)
    (parametricExtension_along_contMDiffOn EW (hα.mono hCU))

theorem integral_pullbackIndexPairDensity {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ r ∈ Icc a b, T - r ^ 2 ∈ J)
    {U : Set ℝ} (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (Y W : ∀ s, TangentSpace (𝓡 n) (α s))
    (EY : ParametricAlongCurveExtensionOn (Icc a b) α Y)
    (EDY : ParametricAlongCurveExtensionOn (Icc a b) α
      (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y (Icc a b) EY))
    (EW : ParametricAlongCurveExtensionOn (Icc a b) α W) :
    (∫ s in a..b, pullbackIndexPairDensity F T EY EW s) =
      pullbackIndexBoundaryPair F T EY W b - pullbackIndexBoundaryPair F T EY W a -
        ∫ s in a..b, pullbackJacobiPairDensity F T EY EDY W s := by
  have hB := extension_metric_pair_contDiffOn F T htime α (hα.mono hCU)
    (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y (Icc a b) EY) W EDY EW
  have hI : IntervalIntegrable (pullbackIndexPairDensity F T EY EW) volume a b :=
    (pullbackIndexPairDensity_contDiffOn F hM04 T hab htime hU hCU α hα Y W
      EY EW).continuousOn.intervalIntegrable_of_Icc hab.le
  have hR : IntervalIntegrable (pullbackJacobiPairDensity F T EY EDY W) volume a b :=
    (pullbackJacobiPairDensity_contDiffOn F hM04 T hab htime hU hCU α hα Y W
      EY EDY EW).continuousOn.intervalIntegrable_of_Icc hab.le
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hB.continuousOn
    (fun s hs ↦ pullbackIndexBoundaryPair_hasDerivAt F hM04 T hab htime hU hCU α hα Y W
      EY EDY EW hs) (hI.add hR)
  rw [intervalIntegral.integral_add hI hR] at hFTC
  dsimp only [pullbackIndexBoundaryPair]
  linarith

end PoincareConjecture.M08


