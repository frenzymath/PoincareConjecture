import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.RegularLevelScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Regularity.Potential
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.PotentialLevels












set_option autoImplicit false

open Set
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology InnerProductSpace BigOperators

noncomputable section

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

private theorem scalar_add_laplacian_threeDimensional
    (S : GradientShrinkingSolitonData 3 M) (x : M) :
    S.connection.scalarCurvature x + S.connection.laplacian S.potential x = 3 / 2 := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : M → Type _) := ⟨S.metric.toRiemannianMetric⟩
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 3)), finrank_euclideanSpace]
    simp
  unfold LeviCivitaData.scalarCurvature LeviCivitaData.laplacian
  rw [← Finset.sum_add_distrib]
  simp_rw [S.soliton_equation]
  have hnorm (i) : S.metric.inner x (S.metric.orthonormalBasis x i)
      (S.metric.orthonormalBasis x i) = 1 :=
    (S.metric.orthonormalBasis x).inner_eq_ite i i |>.trans (if_pos rfl)
  simp only [hnorm, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, hdim, nsmul_eq_mul, Nat.cast_ofNat]
  norm_num


theorem levelMeanCurvature_eq_soliton_trace
    (S : GradientShrinkingSolitonData 3 M) (x : M)
    (hQ : 0 < S.connection.levelQ S.potential x) :
    S.connection.levelMeanCurvature S.potential x =
      (1 - S.connection.scalarCurvature x +
        S.connection.ricci x (S.connection.levelUnitNormal S.potential x)
          (S.connection.levelUnitNormal S.potential x)) /
        Real.sqrt (S.connection.levelQ S.potential x) := by
  have hmean := S.connection.hessian_mean_curvature S.potential_contMDiff x hQ
  change S.connection.levelMeanCurvature S.potential x =
    (S.connection.laplacian S.potential x - S.connection.hessian S.potential x
      (S.connection.levelUnitNormal S.potential x)
      (S.connection.levelUnitNormal S.potential x)) /
        Real.sqrt (S.connection.levelQ S.potential x) at hmean
  have hN : S.metric.inner x
      (S.connection.levelUnitNormal S.potential x)
      (S.connection.levelUnitNormal S.potential x) = 1 := by
    unfold LeviCivitaData.levelUnitNormal
    simp only [map_smul, smul_apply, smul_eq_mul]
    change (Real.sqrt (S.connection.levelQ S.potential x))⁻¹ *
      ((Real.sqrt (S.connection.levelQ S.potential x))⁻¹ *
        S.connection.levelQ S.potential x) = 1
    calc
      _ = S.connection.levelQ S.potential x /
          (Real.sqrt (S.connection.levelQ S.potential x)) ^ 2 := by ring
      _ = 1 := by rw [Real.sq_sqrt hQ.le, div_self hQ.ne']
  have hsol := S.soliton_equation x
    (S.connection.levelUnitNormal S.potential x)
    (S.connection.levelUnitNormal S.potential x)
  rw [hN, mul_one] at hsol
  rw [hmean]
  congr 1
  linarith [scalar_add_laplacian_threeDimensional S x]



theorem levelGaussTerm_le_soliton_trace_sq
    (S : GradientShrinkingSolitonData 3 M) (x : M)
    (hQ : 0 < S.connection.levelQ S.potential x) :
    S.connection.levelGaussTerm S.potential x ≤
      (1 - S.connection.scalarCurvature x +
        S.connection.ricci x (S.connection.levelUnitNormal S.potential x)
          (S.connection.levelUnitNormal S.potential x)) ^ 2 /
        S.connection.levelQ S.potential x := by
  have hle : S.connection.levelGaussTerm S.potential x ≤
      (S.connection.levelMeanCurvature S.potential x) ^ 2 := by
    unfold LeviCivitaData.levelGaussTerm
    exact sub_le_self _ (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg _)
  rw [S.levelMeanCurvature_eq_soliton_trace x hQ, div_pow,
    Real.sq_sqrt hQ.le] at hle
  exact hle




theorem regularLevel_scalarCurvature_le_soliton_trace_sq
    (S : GradientShrinkingSolitonData 3 M)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) S.potential x ≠ 0)
    (c : ℝ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace S.potential_contMDiff U hreg 2 c
    letI := isManifold_openLevelSet S.potential_contMDiff U hreg 2 c
    ∀ (D' : LeviCivitaData
      (RiemannianMetric.regularLevelMetric S.potential_contMDiff U hreg c S.metric))
      (z : openLevelSet S.potential U c),
      let x := openLevelIncl S.potential U c z
      let N := S.connection.levelUnitNormal S.potential x
      D'.scalarCurvature z ≤ S.connection.scalarCurvature x -
        2 * S.connection.ricci x N N +
        (1 - S.connection.scalarCurvature x + S.connection.ricci x N N) ^ 2 /
          S.connection.levelQ S.potential x := by
  intro D' z
  dsimp only
  rw [S.connection.regularLevel_scalarCurvature_gauss S.metric
    S.potential_contMDiff U hreg c D' z]
  have hQ : 0 < S.connection.levelQ S.potential
      (openLevelIncl S.potential U c z) := by
    exact Real.sqrt_pos.mp
      ((S.metric.tangentNorm_gradient_pos_iff S.potential
        (openLevelIncl S.potential U c z)).mpr (hreg _ z.1.2))
  exact add_le_add_right (S.levelGaussTerm_le_soliton_trace_sq _ hQ) _



theorem regularLevel_scalarCurvature_lt_one
    (S : GradientShrinkingSolitonData 3 M)
    (hD : S.connection.CurvatureTensorCalculus)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) S.potential x ≠ 0)
    (c : ℝ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace S.potential_contMDiff U hreg 2 c
    letI := isManifold_openLevelSet S.potential_contMDiff U hreg 2 c
    ∀ (D' : LeviCivitaData
      (RiemannianMetric.regularLevelMetric S.potential_contMDiff U hreg c S.metric))
      (z : openLevelSet S.potential U c),
      let x := openLevelIncl S.potential U c z
      let N := S.connection.levelUnitNormal S.potential x
      S.connection.scalarCurvature x < 1 →
      1 - S.connection.scalarCurvature x + S.connection.ricci x N N <
        S.connection.levelQ S.potential x →
      D'.scalarCurvature z < 1 := by
  intro D' z
  dsimp only
  intro hR hnum
  let x := openLevelIncl S.potential U c z
  let N := S.connection.levelUnitNormal S.potential x
  have hle := S.regularLevel_scalarCurvature_le_soliton_trace_sq U hreg c D' z
  have hQ : 0 < S.connection.levelQ S.potential x := by
    exact Real.sqrt_pos.mp
      ((S.metric.tangentNorm_gradient_pos_iff S.potential x).mpr (hreg x z.1.2))
  have hb : 0 ≤ S.connection.ricci x N N :=
    (S.connection.ricci_bounds_of_nonnegative_curvatureOperator hD x
      (S.nonnegative_curvature x) N).1
  have ha : 0 < 1 - S.connection.scalarCurvature x +
      S.connection.ricci x N N := by linarith
  have hfrac :
      (1 - S.connection.scalarCurvature x + S.connection.ricci x N N) ^ 2 /
          S.connection.levelQ S.potential x <
        1 - S.connection.scalarCurvature x + S.connection.ricci x N N := by
    apply (div_lt_iff₀ hQ).2
    nlinarith [mul_pos ha (sub_pos.mpr hnum)]
  dsimp only at hle
  dsimp only [x, N] at hb hfrac
  linarith



theorem regularLevel_scalarCurvature_lt_one_of_gradient_sq_gt_one
    (S : GradientShrinkingSolitonData 3 M)
    (hD : S.connection.CurvatureTensorCalculus)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) S.potential x ≠ 0)
    (c : ℝ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace S.potential_contMDiff U hreg 2 c
    letI := isManifold_openLevelSet S.potential_contMDiff U hreg 2 c
    ∀ (D' : LeviCivitaData
      (RiemannianMetric.regularLevelMetric S.potential_contMDiff U hreg c S.metric))
      (z : openLevelSet S.potential U c),
      S.connection.scalarCurvature (openLevelIncl S.potential U c z) < 1 →
      1 < S.connection.levelQ S.potential (openLevelIncl S.potential U c z) →
      D'.scalarCurvature z < 1 := by
  intro D' z hR hQ
  apply S.regularLevel_scalarCurvature_lt_one hD U hreg c D' z hR
  let x := openLevelIncl S.potential U c z
  have hQ0 : 0 < S.connection.levelQ S.potential x := lt_trans zero_lt_one hQ
  have hN : S.metric.inner x
      (S.connection.levelUnitNormal S.potential x)
      (S.connection.levelUnitNormal S.potential x) = 1 := by
    unfold LeviCivitaData.levelUnitNormal
    simp only [map_smul, smul_apply, smul_eq_mul]
    change (Real.sqrt (S.connection.levelQ S.potential x))⁻¹ *
      ((Real.sqrt (S.connection.levelQ S.potential x))⁻¹ *
        S.connection.levelQ S.potential x) = 1
    calc
      _ = S.connection.levelQ S.potential x /
          (Real.sqrt (S.connection.levelQ S.potential x)) ^ 2 := by ring
      _ = 1 := by rw [Real.sq_sqrt hQ0.le, div_self hQ0.ne']
  have hb := (S.connection.ricci_bounds_of_nonnegative_curvatureOperator hD x
    (S.nonnegative_curvature x) (S.connection.levelUnitNormal S.potential x)).2
  rw [hN, mul_one] at hb
  dsimp only [x] at hb
  linarith



theorem exists_threshold_regularLevel_scalarCurvature_lt_one
    (S : GradientShrinkingSolitonData 3 M)
    (hD : S.connection.CurvatureTensorCalculus) :
    ∃ a : ℝ, ∀ (U : TopologicalSpace.Opens M)
      (hreg : ∀ x ∈ U, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) S.potential x ≠ 0)
      (c : ℝ), a ≤ c →
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
        ⟨finrank_euclideanSpace_fin⟩
      letI := openLevelSetChartedSpace S.potential_contMDiff U hreg 2 c
      letI := isManifold_openLevelSet S.potential_contMDiff U hreg 2 c
      ∀ (D' : LeviCivitaData
        (RiemannianMetric.regularLevelMetric S.potential_contMDiff U hreg c S.metric))
        (z : openLevelSet S.potential U c),
        S.connection.scalarCurvature (openLevelIncl S.potential U c z) < 1 →
        D'.scalarCurvature z < 1 := by
  obtain ⟨a, ha⟩ := S.exists_gradient_sq_gt_on_superlevel hD 1
  refine ⟨a, ?_⟩
  intro U hreg c hc D' z hR
  apply S.regularLevel_scalarCurvature_lt_one_of_gradient_sq_gt_one hD U hreg c D' z hR
  apply ha
  have hz : S.potential (openLevelIncl S.potential U c z) = c := z.property
  simpa only [hz] using hc

end PoincareConjecture.GradientShrinkingSolitonData
