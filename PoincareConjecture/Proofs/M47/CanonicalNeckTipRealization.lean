import PoincareConjecture.Proofs.M47.CanonicalNeckRotationalTip
import PoincareConjecture.Proofs.M35.Thm12_28.NeckCharts
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.RicciConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "B" => E →L[ℝ] E →L[ℝ] ℝ

theorem exists_native_tip_metric_realization
    (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    {length : ℝ} {center : StandardCapSpace} (N : StandardCylinderPatch length center)
    (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-length) length)
    (htip : N.coordinate (q, s) = 0) :
    ∃ (g1 : RiemannianMetric 3 E) (D1 : LeviCivitaData g1) (W : Set E),
      IsOpen W ∧ M35.cylinderCoordinateEquiv.symm (0, s) ∈ W ∧
      (∀ z ∈ W, ∀ i j : Fin 3,
        g1.inner z (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j) =
        roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate)
          (chartAt E2 q) (M35.cylinderCoordinateEquiv z) i j) ∧
      (∀ u v : E,
        D1.ricci (M35.cylinderCoordinateEquiv.symm (0, s)) u u *
            g1.inner (M35.cylinderCoordinateEquiv.symm (0, s)) v v =
          D1.ricci (M35.cylinderCoordinateEquiv.symm (0, s)) v v *
            g1.inner (M35.cylinderCoordinateEquiv.symm (0, s)) u u) := by
  let p := M35.cylinderCoordinateEquiv.symm ((0, s) : RoundCylinderCoordinates)
  let f := N.coordinate ∘ M35.cylinderChart q
  let U : Set E := {z | (M35.cylinderCoordinateEquiv z).2 ∈ Ioo (-length) length}
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_snd.comp M35.cylinderCoordinateEquiv.continuous)
  have hp : p ∈ U := by
    simpa only [U, mem_ofPred_eq, p, ContinuousLinearEquiv.apply_symm_apply] using hs
  have hf (z : E) (hz : z ∈ U) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f z :=
    N.euclideanChart_contMDiffAt q hz
  have hi (z : E) (hz : z ∈ U) : (mfderiv (𝓡 3) (𝓡 3) f z).IsInvertible :=
    N.euclideanChart_mfderiv_invertible q hz
  obtain ⟨g1, D1, W, hW, hpW, hWU, hcoeff⟩ :=
    RiemannianMetric.exists_local_realization hU hp (g.pullbackCoefficients f)
      (fun z hz => (g.contDiffAt_pullbackCoefficients (hf z hz)).contDiffWithinAt)
      (fun z _ u v => g.symm (f z) _ _)
      (fun z hz v hv => by
        apply g.pos (f z)
        intro h
        apply hv
        exact (hi z hz).injective (h.trans (map_zero _).symm))
  have hm : ∀ᶠ z in 𝓝 p, ∀ u v : E, g1.inner z u v =
      g.inner (f z) (mfderiv (𝓡 3) (𝓡 3) f z u) (mfderiv (𝓡 3) (𝓡 3) f z v) := by
    filter_upwards [hW.mem_nhds hpW] with z hz u v
    exact congrArg (fun A : B => A u v) (hcoeff z hz)
  have hfp : f p = 0 := by
    have hc : M35.cylinderChart q p = (q, s) := by
      change ((chartAt E2 q).symm (M35.cylinderCoordinateEquiv p).1,
        (M35.cylinderCoordinateEquiv p).2) = _
      dsimp only [p]
      rw [ContinuousLinearEquiv.apply_symm_apply]
      apply Prod.ext
      · have h := (chartAt E2 q).left_inv (mem_chart_source E2 q)
        simpa only [M35.sphere_chart_center] using h
      · rfl
    simpa only [f, Function.comp_apply, hc] using htip
  refine ⟨g1, D1, W, hW, hpW, ?_, ?_⟩
  · intro z hz i j
    have h := congrArg (fun A : B =>
      A (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) (hcoeff z hz)
    exact h.trans (N.euclideanChart_coefficient g q (hWU hz) i j)
  · let A := mfderiv (𝓡 3) (𝓡 3) f p
    have hmetric (u v : E) : g1.inner p u v = g.inner 0 (A u) (A v) := by
      have h := hm.self_of_nhds u v
      change g1.inner p u v = g.inner (f p) (A u) (A v) at h
      rwa [hfp] at h
    have hricci (u v : E) : D1.ricci p u v = D.ricci 0 (A u) (A v) := by
      have h := D1.ricci_eq_pullback_euclidean D (hf p hp)
        (Filter.mem_of_superset (hU.mem_nhds hp) hi) hm u v
      change D1.ricci p u v = D.ricci (f p) (A u) (A v) at h
      rwa [hfp] at h
    intro u v
    change D1.ricci p u u * g1.inner p v v = D1.ricci p v v * g1.inner p u u
    rw [hricci, hricci, hmetric, hmetric]
    exact rotational_tip_ricci_isotropic D hrotation (A u) (A v)

end PoincareConjecture.Proofs.M47
