import PoincareConjecture.Proofs.M35.CapGeometry.SelectedCurvatureDerivativeRealization
import PoincareConjecture.Proofs.M35.CapGeometry.RadialSectionalPlane

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

local notation "V" => EuclideanSpace ℝ (Fin 3)

theorem exists_cylinder_radial_plane_realization {J : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J)
    {C : GeneralizedSliceCarrier} {a Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder (generalizedFlow F) C a Q I U)
    (hU : IsOpen U) (hzero : (0 : ℝ) ∈ I) (htime : a + 0 / Q ∈ J)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        (F.metric a).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (F.metric a).inner x u v)
    (q : C.carrier) {p : V}
    (hp : p ∈ (extChartAt (𝓡 3) q).target)
    (hpU : (extChartAt (𝓡 3) q).symm p ∈ U) :
    let f : C.carrier → StandardCapSpace := fun z => (e.forward 0 hzero z).val
    let y := f ((extChartAt (𝓡 3) q).symm p)
    let G := M13.scaleSmoothMetric (F.metric a) Q e.scale_pos
    y ≠ 0 → ∃ (g : RiemannianMetric 3 V) (D : LeviCivitaData g) (u v : V),
      (∀ᶠ z in 𝓝 p, ∀ i j : Fin 3,
        g.euclideanCoefficients z (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j) =
            fixedCylinderMetricCoefficient F C a Q f q i j (0, z)) ∧
      g.inner p u u = 1 ∧ g.inner p v v = 1 ∧ g.inner p u v = 0 ∧
      D.curvatureTensor p u v u v =
        radialMixedCurvatureFactor G ‖y‖ / axisRadialCoefficient G ‖y‖ := by
  let c := extChartAt (𝓡 3) q
  let f : C.carrier → StandardCapSpace := fun z => (e.forward 0 hzero z).val
  let phi := cylinderSpatialCoordinates F e hU 0 hzero htime
  let W := c.target ∩ c.symm ⁻¹' U
  have hW : IsOpen W := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) hU
  have hf (z : V) (hz : z ∈ W) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f (c.symm z) :=
    phi.contMDiffOn_toFun.contMDiffAt (hU.mem_nhds hz.2)
  have hc (z : V) (hz : z ∈ W) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm z :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hz.1)
  have hi (z : V) (hz : z ∈ W) :
      (mfderiv (𝓡 3) (𝓡 3) (f ∘ c.symm) z).IsInvertible := by
    have hfi : (mfderiv (𝓡 3) (𝓡 3) f (c.symm z)).IsInvertible :=
      let hlocal : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ f (c.symm z) :=
        ⟨phi, hz.2, fun _ _ => rfl⟩
      ⟨hlocal.mfderivToContinuousLinearEquiv (by simp), rfl⟩
    have hci : (mfderiv (𝓡 3) (𝓡 3) c.symm z).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm hz.1
    rw [mfderiv_comp z ((hf z hz).mdifferentiableAt (by simp))
      ((hc z hz).mdifferentiableAt (by simp))]
    exact hfi.comp hci
  let G : RiemannianMetric 3 StandardCapSpace := M13.scaleSmoothMetric (F.metric a) Q e.scale_pos
  let DG : LeviCivitaData G := M13.scaleLeviCivitaData (F.connection a) Q e.scale_pos
  change f (c.symm p) ≠ 0 → _
  intro hy
  obtain ⟨u₀, v₀, hu₀, hv₀, huv₀, hcurv₀⟩ := exists_radial_sectional_plane DG
    (scaleSmoothMetric_rotation_invariant hrotation Q e.scale_pos) hy
  obtain ⟨g, D, hcoeff, _hnorm⟩ := exists_local_curvature_derivative_realization
    G DG (f ∘ c.symm) hW ⟨hp, hpU⟩ (fun z hz => (hf z hz).comp z (hc z hz)) hi
  let A := mfderiv (𝓡 3) (𝓡 3) (f ∘ c.symm) p
  let u := A.inverse u₀
  let v := A.inverse v₀
  have hAi : A.IsInvertible := hi p ⟨hp, hpU⟩
  have hm : ∀ᶠ z in 𝓝 p, ∀ u v : V, g.inner z u v =
      G.inner ((f ∘ c.symm) z)
        (mfderiv (𝓡 3) (𝓡 3) (f ∘ c.symm) z u)
        (mfderiv (𝓡 3) (𝓡 3) (f ∘ c.symm) z v) := by
    filter_upwards [hcoeff] with z hz u v
    exact congrArg (fun B : V →L[ℝ] V →L[ℝ] ℝ => B u v) hz
  refine ⟨g, D, u, v, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hcoeff, hW.mem_nhds ⟨hp, hpU⟩] with z hz hzW i j
    have heq := congrArg (fun B : V →L[ℝ] V →L[ℝ] ℝ =>
      B (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) hz
    have hfixed := fixedCylinderMetricCoefficient_eq_pullback F C a Q f q i j
      (0, z) hzW.1 (hf z hzW)
    simp only [zero_div, add_zero] at hfixed
    exact heq.trans hfixed.symm
  · rw [hm.self_of_nhds]
    change G.inner (f (c.symm p)) (A (A.inverse u₀)) (A (A.inverse u₀)) = 1
    rw [hAi.self_apply_inverse]
    exact hu₀
  · rw [hm.self_of_nhds]
    change G.inner (f (c.symm p)) (A (A.inverse v₀)) (A (A.inverse v₀)) = 1
    rw [hAi.self_apply_inverse]
    exact hv₀
  · rw [hm.self_of_nhds]
    change G.inner (f (c.symm p)) (A (A.inverse u₀)) (A (A.inverse v₀)) = 0
    rw [hAi.self_apply_inverse, hAi.self_apply_inverse]
    exact huv₀
  · rw [D.curvatureTensor_eq_pullback_euclidean DG
      ((hf p ⟨hp, hpU⟩).comp p (hc p ⟨hp, hpU⟩))
      (Filter.mem_of_superset (hW.mem_nhds ⟨hp, hpU⟩) hi) hm]
    change DG.curvatureTensor (f (c.symm p)) (A (A.inverse u₀)) (A (A.inverse v₀))
      (A (A.inverse u₀)) (A (A.inverse v₀)) = _
    rw [hAi.self_apply_inverse, hAi.self_apply_inverse]
    exact hcurv₀

end PoincareConjecture.M35.OrdinaryRealization
