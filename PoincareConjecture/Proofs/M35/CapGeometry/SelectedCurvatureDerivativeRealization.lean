import PoincareConjecture.Proofs.M35.CapGeometry.CurvatureDerivativeNorm
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderScalarOperators









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)



theorem exists_local_curvature_derivative_realization
    {M : Type*} [TopologicalSpace M] [ChartedSpace V M]
    [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (f : V → M)
    {U : Set V} (hU : IsOpen U) {p : V} (hp : p ∈ U)
    (hf : ∀ z ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f z)
    (hi : ∀ z ∈ U, (mfderiv (𝓡 3) (𝓡 3) f z).IsInvertible) :
    ∃ (g' : RiemannianMetric 3 V) (D' : LeviCivitaData g'),
      (∀ᶠ z in 𝓝 p, g'.euclideanCoefficients z = g.pullbackCoefficients f z) ∧
      D'.curvatureDerivativeNorm 1 p = D.curvatureDerivativeNorm 1 (f p) := by
  obtain ⟨g', D', W, hWo, hpW, hWU, hcoeff⟩ :=
    RiemannianMetric.exists_local_realization hU hp (g.pullbackCoefficients f)
      (fun z hz => (g.contDiffAt_pullbackCoefficients (hf z hz)).contDiffWithinAt)
      (fun z _ v w => g.symm (f z) _ _)
      (fun z hz v hv => by
        apply g.pos (f z)
        intro heq
        apply hv
        apply (hi z hz).injective
        exact heq.trans (map_zero (mfderiv (𝓡 3) (𝓡 3) f z)).symm)
  have hmetric (z : V) (hz : z ∈ W) (u v : V) :
      g'.inner z u v = g.inner (f z)
        (mfderiv (𝓡 3) (𝓡 3) f z u) (mfderiv (𝓡 3) (𝓡 3) f z v) :=
    congrArg (fun A : V →L[ℝ] V →L[ℝ] ℝ => A u v) (hcoeff z hz)
  refine ⟨g', D', Filter.mem_of_superset (hWo.mem_nhds hpW) hcoeff, ?_⟩
  exact D'.curvatureDerivativeNorm_eq_pullback D hWo
    (fun z hz => (hf z (hWU hz)).contMDiffWithinAt)
    (fun z hz => hi z (hWU hz)) hmetric 1 hpW

namespace OrdinaryRealization



theorem exists_cylinder_curvature_derivative_realization {J : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J)
    {C : GeneralizedSliceCarrier} {a Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder (generalizedFlow F) C a Q I U)
    (hU : IsOpen U) (hzero : (0 : ℝ) ∈ I) (htime : a + 0 / Q ∈ J)
    (q : C.carrier) {p : V}
    (hp : p ∈ (extChartAt (𝓡 3) q).target)
    (hpU : (extChartAt (𝓡 3) q).symm p ∈ U) :
    let f : C.carrier → StandardCapSpace := fun z => (e.forward 0 hzero z).val
    let y := f ((extChartAt (𝓡 3) q).symm p)
    ∃ (g : RiemannianMetric 3 V) (D : LeviCivitaData g),
      (∀ᶠ z in 𝓝 p, ∀ i j : Fin 3,
        g.euclideanCoefficients z (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j) =
            fixedCylinderMetricCoefficient F C a Q f q i j (0, z)) ∧
      D.curvatureDerivativeNorm 1 p =
        (M13.scaleLeviCivitaData (F.connection a) Q e.scale_pos).curvatureDerivativeNorm 1 y := by
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
  obtain ⟨g, D, hcoeff, hnorm⟩ := exists_local_curvature_derivative_realization
    (M13.scaleSmoothMetric (F.metric a) Q e.scale_pos)
    (M13.scaleLeviCivitaData (F.connection a) Q e.scale_pos)
    (f ∘ c.symm) hW ⟨hp, hpU⟩ (fun z hz => (hf z hz).comp z (hc z hz)) hi
  refine ⟨g, D, ?_, hnorm⟩
  filter_upwards [hcoeff, hW.mem_nhds ⟨hp, hpU⟩] with z hz hzW i j
  have heq := congrArg (fun B : V →L[ℝ] V →L[ℝ] ℝ =>
    B (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) hz
  have hfixed := fixedCylinderMetricCoefficient_eq_pullback F C a Q f q i j
    (0, z) hzW.1 (hf z hzW)
  simp only [zero_div, add_zero] at hfixed
  exact heq.trans hfixed.symm

end OrdinaryRealization
end PoincareConjecture.M35
