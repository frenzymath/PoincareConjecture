import PoincareConjecture.Proofs.M35.Thm12_28.NeckCurvatureLimit
import PoincareConjecture.Proofs.M35.Thm12_28.ScalarMetricJets

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => StandardCapSpace

theorem cylinder_scalarCurvature_tendsto_of_time_tendsto
    (g : ℕ → RiemannianMetric 3 V) (D : ∀ n, LeviCivitaData (g n))
    (epsilon : ℕ → ℝ) (B : ℕ → RoundCylinderTwoTensor) (q : ℕ → UnitTwoSphere)
    (s u : ℕ → ℝ) (u' : ℝ) (hu' : u' < 1)
    (hs : ∀ n, s n ∈ Set.Ioo (-(epsilon n)⁻¹) (epsilon n)⁻¹)
    (hlo : ∀ n, -1 ≤ u n) (hu : ∀ n, u n < 1)
    (he : ∀ n, 0 < epsilon n) (hk : ∀ n, 2 ≤ ⌊(epsilon n)⁻¹⌋₊)
    (hclose : ∀ n, RoundCylinderClose (epsilon n) (u n) (B n))
    (hlim : Tendsto epsilon atTop (𝓝 0)) (htime : Tendsto u atTop (𝓝 u'))
    (hcoeff : ∀ n (i j : Fin 3),
      (fun p : V => (g n).inner p
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) =ᶠ[𝓝 0]
      (fun p => roundCylinderTensorCoefficient (B n)
        (chartAt (EuclideanSpace ℝ (Fin 2)) (q n))
          (cylinderCoordinateEquiv p + (0, s n)) i j)) :
    Tendsto (fun n => (D n).scalarCurvature 0) atTop (𝓝 (1 / (1 - u'))) := by
  let model := cylinderEuclideanMetric u' hu'
  let modelD := cylinderEuclideanConnection u' hu'
  let varying n := cylinderEuclideanMetric (u n) (hu n)
  have hjet (r : ℕ) (hr : r ≤ 2) (i j : Fin 3) :
      Tendsto (fun n => iteratedFDeriv ℝ r (fun p : V => (g n).inner p
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) 0) atTop
      (𝓝 (iteratedFDeriv ℝ r (fun p : V => model.inner p
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) 0)) := by
    let J (G : RiemannianMetric 3 V) := iteratedFDeriv ℝ r
      (fun p : V => G.inner p (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) 0
    have herr : Tendsto (fun n => J (g n) - J (varying n)) atTop (𝓝 0) := by
      apply tendsto_cylinder_jet_of_components
      intro a
      have hbound (n : ℕ) :
          ‖iteratedFDeriv ℝ r (fun p : V => (g n).inner p
              (EuclideanSpace.basisFun (Fin 3) ℝ i)
              (EuclideanSpace.basisFun (Fin 3) ℝ j)) 0
              (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k)) -
            iteratedFDeriv ℝ r (fun p : V => (varying n).inner p
              (EuclideanSpace.basisFun (Fin 3) ℝ i)
              (EuclideanSpace.basisFun (Fin 3) ℝ j)) 0
              (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))‖ ≤ 52 * epsilon n := by
        have hr' : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
        have hsub := iteratedFDeriv_sub_apply
          ((metric_component_contDiffAt (g n) 0 (EuclideanSpace.basisFun (Fin 3) ℝ i)
            (EuclideanSpace.basisFun (Fin 3) ℝ j)).of_le hr')
          ((metric_component_contDiffAt (varying n) 0 (EuclideanSpace.basisFun (Fin 3) ℝ i)
            (EuclideanSpace.basisFun (Fin 3) ℝ j)).of_le hr')
        have hsv := congrArg (fun T => T
          (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))) hsub
        have hb := (hclose n).euclidean_metric_error_component_abs_lt_shift
          (he n) (hlo n) (hu n) (q n) (s n) (hs n) (hk n) (g n) i j (hcoeff n i j) hr a
        exact ((congrArg abs hsv).symm.trans_lt hb).le
      exact squeeze_zero_norm hbound (by simpa only [mul_zero] using hlim.const_mul 52)
    have hmodel : Tendsto (fun n => J (varying n)) atTop (𝓝 (J model)) :=
      ((continuous_cylinder_metric_jet r 0 (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)).tendsto u').comp htime
    simpa only [sub_add_cancel, zero_add] using herr.add hmodel
  have hscalar := scalarCurvature_tendsto_of_metric_jets
    D modelD 0 (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis hjet
  have hmodel : modelD.scalarCurvature 0 = 1 / (1 - u') := by
    have h := cylinder_scalarCurvature_center u' hu' modelD (q 0) 0
    simpa only [← Prod.zero_eq_mk, map_zero] using h
  exact hmodel ▸ hscalar

end PoincareConjecture.M35
