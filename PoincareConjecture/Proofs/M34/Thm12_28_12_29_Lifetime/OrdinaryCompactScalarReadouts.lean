import PoincareConjecture.Proofs.M34.Standard.ScalarAnalyticJet
import PoincareConjecture.Proofs.M34.Standard.CoordinateScalarGerm
import PoincareConjecture.Proofs.M34.Standard.CoordinateScalarGradient
import PoincareConjecture.Proofs.M34.Standard.CoordinateScalarEvolution
import PoincareConjecture.Proofs.M34.Standard.GeneralizedCylinderCurvature
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckCoordinateSmooth
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence.LocalRealization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private theorem spatialJet_eq_reconstructed_of_germ
    (g : RiemannianMetric 3 E₃) (f : E₃ → Fin 3 → Fin 3 → ℝ) (x : E₃)
    (hg : ∀ᶠ y in 𝓝 x, ∀ a b : Fin 3,
      g.euclideanCoefficients y (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) = f y a b) (m : ℕ) :
    spatialJet m (fun z : ℝ × E₃ => g.euclideanCoefficients z.2) (0, x) =
      spatialJet m (fun z : ℝ × E₃ =>
        ContinuousLinearMap.piLpBilinearFromCoordinates (p := 2) (q := 2) (𝕜 := ℝ)
          (f z.2)) (0, x) := by
  have hcoeff : g.euclideanCoefficients =ᶠ[𝓝 x]
      (fun y => ContinuousLinearMap.piLpBilinearFromCoordinates
        (p := 2) (q := 2) (𝕜 := ℝ) (f y)) := by
    filter_upwards [hg] with y hy
    have hf : f y = fun a b => g.euclideanCoefficients y
        (PiLp.single 2 a 1) (PiLp.single 2 b 1) := by
      funext a b
      simpa only [EuclideanSpace.basisFun_apply] using (hy a b).symm
    rw [hf, ContinuousLinearMap.piLpBilinearFromCoordinates_evaluations]
  funext j
  exact (hcoeff.iteratedFDeriv ℝ j).self_of_nhds

section Limit

variable {J : Set ℝ} (L : BlowupLimitFlow.{u} J)

private local instance : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance : ChartedSpace E₃ L.carrier.carrier := L.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold

theorem limitCoordinateBilinear_scalarAnalyticJet
    (q : L.sliceCarrier.carrier) (s : ℝ) (y : E₃)
    (hy : y ∈ (extChartAt (𝓡 3) q).target) :
    let B := spatialJet 4 (fun z : ℝ × E₃ => limitCoordinateBilinear L q s z.2) (0, y)
    let x := (extChartAt (𝓡 3) q).symm y
    B ∈ curvatureJetDomain 3 2 ∧
      scalarAnalyticJet 3 B =
        ((L.flow.connection s).scalarCurvature x,
          scalarGradientNorm (L.flow.metric s) (L.flow.connection s) x,
          (L.flow.connection s).laplacian (L.flow.connection s).scalarCurvature x +
            2 * (L.flow.connection s).ricciNormSq x) := by
  obtain ⟨g, D, V, hVo, hyV, _, heq⟩ := L.carrier.exists_local_coordinate_realization
    (L.flow.metric s) q s y hy
  have hg : ∀ᶠ z in 𝓝 y, ∀ a b : Fin 3,
      g.euclideanCoefficients z (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) = L.carrier.coordinateCoefficient q
          (fun _ x v w => (L.flow.metric s).inner x v w) a b (s, z) :=
    Filter.Eventually.mono (hVo.mem_nhds hyV) heq
  have hjet := spatialJet_eq_reconstructed_of_germ g _ y hg 4
  change spatialJet 4 (fun z : ℝ × E₃ => g.euclideanCoefficients z.2) (0, y) =
    spatialJet 4 (fun z : ℝ × E₃ => limitCoordinateBilinear L q s z.2) (0, y) at hjet
  dsimp only
  rw [← hjet]
  refine ⟨metric_spatialJet_mem_curvatureJetDomain g 2 y, ?_⟩
  rw [scalarAnalyticJet_spatialJet D, ← scalarGradientNorm_eq_tangentNorm]
  exact Prod.ext
    (L.carrier.scalarCurvature_eq_of_frozen_coordinate_germ (L.flow.metric s)
      (L.flow.connection s) q s y hy g D hg)
    (Prod.ext (L.carrier.scalarGradientNorm_eq_of_coordinate_germ (L.flow.metric s)
      (L.flow.connection s) q s y hy g D hg)
      (L.carrier.scalarEvolution_eq_of_coordinate_germ (L.flow.metric s)
        (L.flow.connection s) q s y hy g D hg))

end Limit

theorem blowupCoordinateBilinear_scalarAnalyticJet
    {J : Set ℝ} {L : BlowupLimitFlow.{u} J} {G : GeneralizedRicciFlowData.{u}}
    {origin scale : ℝ} {K : Set ℝ} {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder G L.sliceCarrier origin scale K U)
    (hU : IsOpen U) (q : L.sliceCarrier.carrier) {s : ℝ} (hs : s ∈ K) (y : E₃)
    (hy : y ∈ (extChartAt (𝓡 3) q).target ∧ (extChartAt (𝓡 3) q).symm y ∈ U) :
    let z := e.pointMap s hs ((extChartAt (𝓡 3) q).symm y)
    scalarAnalyticJet 3
      (spatialJet 4 (fun w : ℝ × E₃ => blowupCoordinateBilinear e q s w.2) (0, y)) =
        (G.scalar z / scale,
          scalarGradientNorm (G.metric z.1) (G.connection z.1) z.2 / scale ^ (3 / 2 : ℝ),
          ((G.connection z.1).laplacian (G.connection z.1).scalarCurvature z.2 +
            2 * (G.connection z.1).ricciNormSq z.2) / scale ^ 2) := by
  obtain ⟨g, D, V, hVo, hyV, _, heq⟩ :=
    e.exists_local_coordinate_realization hU q hs y hy
  have hg : ∀ᶠ w in 𝓝 y, ∀ a b : Fin 3,
      g.euclideanCoefficients w (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) = blowupPullbackCoefficient e q a b (s, w) :=
    Filter.Eventually.mono (hVo.mem_nhds hyV) heq
  have hjet := spatialJet_eq_reconstructed_of_germ g _ y hg 4
  change spatialJet 4 (fun z : ℝ × E₃ => g.euclideanCoefficients z.2) (0, y) =
    spatialJet 4 (fun z : ℝ × E₃ => blowupCoordinateBilinear e q s z.2) (0, y) at hjet
  dsimp only
  rw [← hjet, scalarAnalyticJet_spatialJet D, ← scalarGradientNorm_eq_tangentNorm]
  exact Prod.ext (e.curvatures_eq_of_coordinate_germ hU q hs y hy g D hg).1
    (Prod.ext (e.scalarGradientNorm_eq_of_coordinate_germ hU q hs y hy g D hg)
      (e.scalarEvolution_eq_of_coordinate_germ hU q hs y hy g D hg))

end PoincareConjecture.M34
