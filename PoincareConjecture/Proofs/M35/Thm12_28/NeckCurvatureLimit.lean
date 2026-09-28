import PoincareConjecture.Proofs.M35.Thm12_28.NeckMetricJets
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderContractions
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderTimeJets
import Mathlib.LinearAlgebra.Multilinear.Basis

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

theorem tendsto_cylinder_jet_of_components {r : ℕ}
    {F : ℕ → ContinuousMultilinearMap ℝ (fun _ : Fin r => EuclideanSpace ℝ (Fin 3)) ℝ}
    {G : ContinuousMultilinearMap ℝ (fun _ : Fin r => EuclideanSpace ℝ (Fin 3)) ℝ}
    (h : ∀ a : Fin r → Fin 3,
      Tendsto (fun n => F n (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))) atTop
        (𝓝 (G (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))))) :
    Tendsto F atTop (𝓝 G) := by
  let ev : ContinuousMultilinearMap ℝ (fun _ : Fin r => EuclideanSpace ℝ (Fin 3)) ℝ →ₗ[ℝ]
      ((Fin r → Fin 3) → ℝ) :=
    { toFun := fun A a => A (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    intro A B hAB
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    exact Module.Basis.ext_multilinear (fun _ => (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)
      (fun a => congrFun hAB a)
  let : FiniteDimensional ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin r => EuclideanSpace ℝ (Fin 3)) ℝ) :=
    FiniteDimensional.of_injective ev hinj
  have hev := ev.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  apply hev.isInducing.tendsto_nhds_iff.mpr
  exact tendsto_pi_nhds.mpr h

theorem metric_component_contDiffAt
    (g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
    (p v w : EuclideanSpace ℝ (Fin 3)) :
    ContDiffAt ℝ ∞ (fun y => g.inner y v w) p := by
  let E := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let ev : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ w).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v)
  exact ev.contDiff.contDiffAt.comp p (g.contDiffAt_euclideanCoefficients p)

theorem cylinder_curvatureTensorNorm_tendsto_of_time_tendsto
    (g : ℕ → RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
    (D : ∀ n, LeviCivitaData (g n)) (epsilon : ℕ → ℝ)
    (B : ℕ → RoundCylinderTwoTensor) (q : ℕ → UnitTwoSphere)
    (s u : ℕ → ℝ) (u' : ℝ) (hu' : u' < 1)
    (hs : ∀ n, s n ∈ Set.Ioo (-(epsilon n)⁻¹) (epsilon n)⁻¹)
    (hu : ∀ n, u n ∈ Set.Icc (-1) 0)
    (he : ∀ n, 0 < epsilon n) (hk : ∀ n, 2 ≤ ⌊(epsilon n)⁻¹⌋₊)
    (hclose : ∀ n, RoundCylinderClose (epsilon n) (u n) (B n))
    (hlim : Tendsto epsilon atTop (𝓝 0))
    (htime : Tendsto u atTop (𝓝 u'))
    (hcoeff : ∀ n (i j : Fin 3),
      (fun p : EuclideanSpace ℝ (Fin 3) => (g n).inner p
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) =ᶠ[𝓝 0]
      (fun p => roundCylinderTensorCoefficient (B n)
        (chartAt (EuclideanSpace ℝ (Fin 2)) (q n))
          (cylinderCoordinateEquiv p + (0, s n)) i j)) :
    Tendsto (fun n => (D n).curvatureTensorNorm 0) atTop (𝓝 (1 / (1 - u'))) := by
  let model := cylinderEuclideanMetric u' hu'
  let modelD := cylinderEuclideanConnection u' hu'
  have huone (n : ℕ) : u n < 1 := (hu n).2.trans_lt (by norm_num)
  let varying (n : ℕ) := cylinderEuclideanMetric (u n) (huone n)
  have hjet (r : ℕ) (hr : r ≤ 2) (i j : Fin 3) :
      Tendsto (fun n => iteratedFDeriv ℝ r (fun p : EuclideanSpace ℝ (Fin 3) =>
        (g n).inner p (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j)) 0) atTop
      (𝓝 (iteratedFDeriv ℝ r (fun p : EuclideanSpace ℝ (Fin 3) => model.inner p
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) 0)) := by
    let J (G : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) :=
      iteratedFDeriv ℝ r (fun p : EuclideanSpace ℝ (Fin 3) => G.inner p
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) 0
    have herr : Tendsto (fun n => J (g n) - J (varying n)) atTop (𝓝 0) := by
      apply tendsto_cylinder_jet_of_components
      intro a
      have hbound (n : ℕ) :
        ‖iteratedFDeriv ℝ r (fun p : EuclideanSpace ℝ (Fin 3) => (g n).inner p
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j))
            0 (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k)) -
          iteratedFDeriv ℝ r (fun p : EuclideanSpace ℝ (Fin 3) => (varying n).inner p
            (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j))
            0 (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))‖ ≤ 52 * epsilon n := by
        have hr' : (r : ℕ∞ω) ≤ ∞ := by norm_cast; exact le_top
        have hsub := iteratedFDeriv_sub_apply
          ((metric_component_contDiffAt (g n) 0 (EuclideanSpace.basisFun (Fin 3) ℝ i)
            (EuclideanSpace.basisFun (Fin 3) ℝ j)).of_le hr')
          ((metric_component_contDiffAt (varying n) 0 (EuclideanSpace.basisFun (Fin 3) ℝ i)
            (EuclideanSpace.basisFun (Fin 3) ℝ j)).of_le hr')
        have hsv := congrArg (fun A => A (fun k => EuclideanSpace.basisFun (Fin 3) ℝ (a k))) hsub
        have hb := (hclose n).euclidean_metric_error_component_abs_lt_shift
          (he n) (hu n).1 (huone n) (q n) (s n) (hs n) (hk n) (g n) i j (hcoeff n i j) hr a
        have hvalue := (congrArg abs hsv).symm.trans_lt hb
        exact hvalue.le
      exact squeeze_zero_norm hbound (by simpa only [mul_zero] using hlim.const_mul 52)
    have hmodel : Tendsto (fun n => J (varying n)) atTop (𝓝 (J model)) :=
      ((continuous_cylinder_metric_jet r 0 (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)).tendsto u').comp htime
    simpa only [sub_add_cancel, zero_add] using herr.add hmodel
  have hnorm := LeviCivitaData.tendsto_curvatureTensorNorm_of_scalar_metric_jets
    D modelD 0 (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis hjet
  have hmodel : modelD.curvatureTensorNorm 0 = 1 / (1 - u') := by
    have h := cylinder_curvatureTensorNorm_center u' hu' modelD (q 0) 0
    simpa only [← Prod.zero_eq_mk, map_zero] using h
  exact hmodel ▸ hnorm

theorem cylinder_curvatureTensorNorm_tendsto
    (g : ℕ → RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
    (D : ∀ n, LeviCivitaData (g n)) (epsilon : ℕ → ℝ)
    (B : ℕ → RoundCylinderTwoTensor) (q : ℕ → UnitTwoSphere)
    (he : ∀ n, 0 < epsilon n) (hk : ∀ n, 2 ≤ ⌊(epsilon n)⁻¹⌋₊)
    (hclose : ∀ n, RoundCylinderClose (epsilon n) 0 (B n))
    (hlim : Tendsto epsilon atTop (𝓝 0))
    (hcoeff : ∀ n (i j : Fin 3),
      (fun p : EuclideanSpace ℝ (Fin 3) => (g n).inner p
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) =ᶠ[𝓝 0]
      (fun p => roundCylinderTensorCoefficient (B n)
        (chartAt (EuclideanSpace ℝ (Fin 2)) (q n)) (cylinderCoordinateEquiv p) i j)) :
    Tendsto (fun n => (D n).curvatureTensorNorm 0) atTop (𝓝 1) := by
  have hs (n : ℕ) : (0 : ℝ) ∈ Set.Ioo (-(epsilon n)⁻¹) (epsilon n)⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr (he n)), inv_pos.mpr (he n)⟩
  have h := cylinder_curvatureTensorNorm_tendsto_of_time_tendsto g D epsilon B q
    (fun _ => 0) (fun _ => 0) 0 (by norm_num) hs (fun _ => by constructor <;> norm_num)
    he hk hclose hlim tendsto_const_nhds
    (fun n i j => by simpa only [← Prod.zero_eq_mk, add_zero] using hcoeff n i j)
  simpa only [sub_zero, div_one] using h

end PoincareConjecture.M35
