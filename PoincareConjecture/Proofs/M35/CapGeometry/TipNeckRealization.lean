import PoincareConjecture.Proofs.M35.CapGeometry.TipRicciIsotropy
import PoincareConjecture.Proofs.M35.Thm12_28.NeckMetricJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.RicciConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

noncomputable section

open Uniqueness

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "B" => V →L[ℝ] V →L[ℝ] ℝ

local instance tipNeckDualNormedGroup : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
local instance tipNeckDualNormedSpace : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
local instance tipNeckMetricNormedGroup : NormedAddCommGroup B := inferInstance
local instance tipNeckMetricNormedSpace : NormedSpace ℝ B := inferInstance

theorem exists_tip_neck_metric_realization
    (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {length : ℝ} {center : StandardCapSpace} (N : StandardCylinderPatch length center)
    (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-length) length)
    (htip : N.coordinate (q, s) = 0) :
    ∃ (g' : RiemannianMetric 3 V) (D' : LeviCivitaData g'),
      (∀ i j : Fin 3,
        (fun z : V => g'.inner z (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j)) =ᶠ[𝓝 0]
          (fun z => roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate)
            (chartAt (EuclideanSpace ℝ (Fin 2)) q)
              (cylinderCoordinateEquiv z + (0, s)) i j)) ∧
      (∀ u v : V, D'.ricci 0 u u * g'.inner 0 v v =
        D'.ricci 0 v v * g'.inner 0 u u) := by
  let p := cylinderCoordinateEquiv.symm ((0, s) : RoundCylinderCoordinates)
  let shift : V → V := fun z => z + p
  let f := (N.coordinate ∘ cylinderChart q) ∘ shift
  let U : Set V := {z | (cylinderCoordinateEquiv (z + p)).2 ∈ Ioo (-length) length}
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_snd.comp (cylinderCoordinateEquiv.continuous.comp
      (continuous_id.add continuous_const)))
  have hzero : (0 : V) ∈ U := by
    simpa only [U, mem_ofPred_eq, zero_add, p,
      ContinuousLinearEquiv.apply_symm_apply] using hs
  have hdshift (z : V) : mfderiv (𝓡 3) (𝓡 3) shift z = ContinuousLinearMap.id ℝ V := by
    rw [mfderiv_eq_fderiv]
    exact ((hasFDerivAt_id z).add_const p).fderiv
  have hshift : ContMDiff (𝓡 3) (𝓡 3) ∞ shift :=
    (contDiff_id.add contDiff_const).contMDiff
  have hf (z : V) (hz : z ∈ U) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f z :=
    (N.euclideanChart_contMDiffAt q hz).comp z (hshift z)
  have hdf (z : V) (hz : z ∈ U) : mfderiv (𝓡 3) (𝓡 3) f z =
      mfderiv (𝓡 3) (𝓡 3) (N.coordinate ∘ cylinderChart q) (z + p) := by
    rw [mfderiv_comp z ((N.euclideanChart_contMDiffAt q hz).mdifferentiableAt (by simp))
      (hshift.mdifferentiable (by simp) z)]
    change (mfderiv (𝓡 3) (𝓡 3) (N.coordinate ∘ cylinderChart q) (z + p)).comp
      (mfderiv (𝓡 3) (𝓡 3) shift z) = _
    rw [hdshift]
    rfl
  have hi (z : V) (hz : z ∈ U) : (mfderiv (𝓡 3) (𝓡 3) f z).IsInvertible := by
    rw [hdf z hz]
    exact N.euclideanChart_mfderiv_invertible q hz
  obtain ⟨g', D', W, hW, hzeroW, _hWU, hcoeff⟩ :=
    RiemannianMetric.exists_local_realization hU hzero (g.pullbackCoefficients f)
      (fun z hz => (g.contDiffAt_pullbackCoefficients (hf z hz)).contDiffWithinAt)
      (fun z _ u v => g.symm (f z) _ _)
      (fun z hz v hv => by
        apply g.pos (f z)
        intro h
        apply hv
        exact (hi z hz).injective (h.trans (map_zero _).symm))
  have hg : g'.euclideanCoefficients =ᶠ[𝓝 (0 : V)] g.pullbackCoefficients f :=
    Filter.mem_of_superset (hW.mem_nhds hzeroW) hcoeff
  have hm : ∀ᶠ z in 𝓝 (0 : V), ∀ u v : V, g'.inner z u v =
      g.inner (f z) (mfderiv (𝓡 3) (𝓡 3) f z u) (mfderiv (𝓡 3) (𝓡 3) f z v) := by
    filter_upwards [hg] with z hz u v
    exact congrArg (fun A : B => A u v) hz
  have hfzero : f 0 = 0 := by
    have hc : cylinderChart q p = (q, s) := by
      change ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm (cylinderCoordinateEquiv p).1,
        (cylinderCoordinateEquiv p).2) = _
      dsimp only [p]
      rw [ContinuousLinearEquiv.apply_symm_apply]
      apply Prod.ext
      · have hh := (chartAt (EuclideanSpace ℝ (Fin 2)) q).left_inv
          (mem_chart_source (EuclideanSpace ℝ (Fin 2)) q)
        simpa only [sphere_chart_center] using hh
      · rfl
    simpa only [f, shift, Function.comp_apply, zero_add, hc] using htip
  refine ⟨g', D', ?_, ?_⟩
  · intro i j
    filter_upwards [hm, hU.mem_nhds hzero] with z hz hzU
    have h := hz (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j)
    rw [hdf z hzU] at h
    have hchart := N.euclideanChart_coefficient g q hzU i j
    have heq := h.trans hchart
    simpa only [map_add, p, ContinuousLinearEquiv.apply_symm_apply] using heq
  · let A := mfderiv (𝓡 3) (𝓡 3) f 0
    let R (z u v : V) := D.ricci z u v
    let H (z u v : V) := g.inner z u v
    have hmetric (u v : V) : g'.inner 0 u v = g.inner 0 (A u) (A v) := by
      have h := hm.self_of_nhds u v
      change g'.inner 0 u v = H (f 0) (A u) (A v) at h
      rwa [hfzero] at h
    have hricci (u v : V) : D'.ricci 0 u v = D.ricci 0 (A u) (A v) := by
      have h := D'.ricci_eq_pullback_euclidean D (hf 0 hzero)
        (Filter.mem_of_superset (hU.mem_nhds hzero) hi) hm u v
      change D'.ricci 0 u v = R (f 0) (A u) (A v) at h
      rwa [hfzero] at h
    intro u v
    rw [hricci, hricci, hmetric, hmetric]
    exact rotational_tip_ricci_diagonal D hrotation (A u) (A v)

end

end PoincareConjecture.M35
