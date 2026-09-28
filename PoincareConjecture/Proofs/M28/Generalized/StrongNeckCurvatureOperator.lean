import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundTransfer
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanNorm
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology Uniformity

universe u

namespace PoincareConjecture.M28

open PoincareConjecture.SpacetimeBounds

private abbrev CE := EuclideanSpace ℝ (Fin 3)
private abbrev cb := EuclideanSpace.basisFun (Fin 3) ℝ



def jetCurvatureNorm (J : MetricTwoJet 3) : ℝ :=
  Real.sqrt (∑ a : Fin 4 → Fin 3, ∑ b : Fin 4 → Fin 3,
    (∏ i : Fin 4, EuclideanSpace.proj (b i) (J.1.inverse (EuclideanSpace.proj (a i)))) *
      (jetCurvature J (cb (a 0)) (cb (a 1)) (cb (a 2)) (cb (a 3)) *
        jetCurvature J (cb (b 0)) (cb (b 1)) (cb (b 2)) (cb (b 3))))



theorem continuousAt_jetCurvatureNorm
    {J : MetricTwoJet 3} (hJ : J.1.IsInvertible) :
    ContinuousAt jetCurvatureNorm J := by
  have hI : ContDiffAt ℝ ∞ (fun K : MetricTwoJet 3 => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  have hentry (i j : Fin 3) : ContinuousAt
      (fun K : MetricTwoJet 3 => EuclideanSpace.proj j
        (K.1.inverse (EuclideanSpace.proj i))) J := by
    exact ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp J
      (hI.clm_apply contDiffAt_const)).continuousAt
  unfold ContinuousAt jetCurvatureNorm
  apply Real.continuous_sqrt.continuousAt.tendsto.comp
  apply tendsto_finsetSum
  intro a _
  apply tendsto_finsetSum
  intro b _
  exact (tendsto_finsetProd _ (fun i _ => (hentry (a i) (b i)).tendsto)).mul
    ((contDiffAt_jetCurvature hJ _ _ _ _).continuousAt.tendsto.mul
      (contDiffAt_jetCurvature hJ _ _ _ _).continuousAt.tendsto)



theorem exists_jetCurvatureNorm_uniform_modulus
    {K : Set (MetricTwoJet 3)} (hK : IsCompact K)
    (hInvertible : ∀ J ∈ K, J.1.IsInvertible)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ J ∈ K, ∀ L : MetricTwoJet 3, dist L J < eta →
        |jetCurvatureNorm L - jetCurvatureNorm J| < delta := by
  have hcontinuous : ∀ J ∈ K, ContinuousAt jetCurvatureNorm J := by
    intro J hJ
    exact continuousAt_jetCurvatureNorm (hInvertible J hJ)
  have huniform :
      {p : MetricTwoJet 3 × MetricTwoJet 3 |
        p.1 ∈ K → dist (jetCurvatureNorm p.1)
          (jetCurvatureNorm p.2) < delta} ∈ 𝓤 (MetricTwoJet 3) := by
    exact hK.uniformContinuousAt_of_continuousAt jetCurvatureNorm
      hcontinuous (Metric.dist_mem_uniformity hdelta)
  obtain ⟨eta, heta, hnear⟩ := Metric.mem_uniformity_dist.mp huniform
  refine ⟨eta, heta, ?_⟩
  intro J hJ L hLJ
  have hp : ((J, L) : MetricTwoJet 3 × MetricTwoJet 3) ∈
      {p : MetricTwoJet 3 × MetricTwoJet 3 |
        p.1 ∈ K → dist (jetCurvatureNorm p.1)
          (jetCurvatureNorm p.2) < delta} := by
    exact hnear (by simpa [dist_comm] using hLJ)
  simpa [Real.dist_eq, abs_sub_comm] using hp hJ

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem jetCurvatureNorm_metricTwoJet_eq
    {g : RiemannianMetric 3 CE} (D : LeviCivitaData g) (x : CE) :
    jetCurvatureNorm (metricTwoJet g.euclideanCoefficients x) =
      D.curvatureTensorNorm x := by
  obtain ⟨A, hA⟩ := D.exists_multilinear_curvatureTensor x
  rw [D.curvatureTensorNorm_eq_tensorNormFromComponents x cb.toBasis A hA]
  have hI (i j : Fin 3) :
      EuclideanSpace.proj j
          ((metricTwoJet g.euclideanCoefficients x).1.inverse (EuclideanSpace.proj i)) =
        (Matrix.of (fun a b => g.inner x (cb a) (cb b)))⁻¹ i j :=
    tube.RiemannianMetric.inverseCoefficients_eq_inverse_gram_m28 g x i j
  unfold jetCurvatureNorm tensorNormFromComponents
  simp only [hI, jetCurvature_metricTwoJet D]
  rfl



theorem jetCurvatureNorm_metricTwoJet_pullback
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace CE M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    {U : Set CE} (hU : IsOpen U) {e : CE → M}
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U)
    (hi : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible)
    {x : CE} (hx : x ∈ U) :
    jetCurvatureNorm (metricTwoJet (g.pullbackCoefficients e) x) =
      D.curvatureTensorNorm (e x) := by
  have hcoeff : ContDiffOn ℝ ∞ (g.pullbackCoefficients e) U := fun y hy =>
    (g.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  obtain ⟨gE, DE, V, hV, hxV, hVU, heq⟩ :=
    RiemannianMetric.exists_local_realization hU hx
      (g.pullbackCoefficients e) hcoeff
      (fun y _ v w => g.symm (e y) _ _)
      (fun y hy w hw => by
        apply g.pos (e y)
        intro hz
        apply hw
        apply (hi y hy).injective
        rw [map_zero]
        convert! hz using 1)
  have hmetric (y : CE) (hy : y ∈ V) (v w : CE) :
      gE.inner y v w = g.inner (e y)
        (mfderiv (𝓡 3) (𝓡 3) e y v) (mfderiv (𝓡 3) (𝓡 3) e y w) :=
    congrArg (fun B => B v w) (heq y hy)
  have hB : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients e := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact heq y hy
  rw [← metricTwoJet_congr_of_eventuallyEq hB, jetCurvatureNorm_metricTwoJet_eq DE]
  exact DE.curvatureTensorNorm_eq_of_local_isometry D hV (he.mono hVU) hmetric hxV

end PoincareConjecture.M28
