import PoincareConjecture.Proofs.M35.Thm12_28.TransportedNeckPatch
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderMetricComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

local notation "V" => EuclideanSpace ℝ (Fin 3)

theorem full_euclidean_chart_regular (N : EpsilonNeck g) (q : UnitTwoSphere)
    {p : V} (hp : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (N.coordinate_map ∘ M35.cylinderChart q) p ∧
      (mfderiv (𝓡 3) (𝓡 3) (N.coordinate_map ∘ M35.cylinderChart q) p).IsInvertible := by
  have hc : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      N.coordinate_map (M35.cylinderChart q p) :=
    ⟨N.coordinatePartialDiffeomorph, ⟨mem_univ _, hp⟩, fun _ _ => rfl⟩
  have hi : (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      N.coordinate_map (M35.cylinderChart q p)).IsInvertible :=
    ⟨hc.mfderivToContinuousLinearEquiv (by simp), rfl⟩
  refine ⟨hc.contMDiffAt.comp p (M35.cylinderChart_contMDiff q p), ?_⟩
  rw [mfderiv_comp p (hc.mdifferentiableAt (by simp))
    ((M35.cylinderChart_contMDiff q p).mdifferentiableAt (by simp))]
  exact hi.comp (M35.cylinderChart_mfderiv_invertible q p)

theorem full_euclidean_coefficient (N : EpsilonNeck g) (q : UnitTwoSphere)
    {p : V} (hp : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (a b : Fin 3) :
    (N.scale⁻¹ ^ 2 • g.pullbackCoefficients (N.coordinate_map ∘ M35.cylinderChart q) p)
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      roundCylinderTensorCoefficient (fun z v w => N.scale⁻¹ ^ 2 *
        roundCylinderPullback g N.coordinate_map z v w)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) (M35.cylinderCoordinateEquiv p) a b := by
  have hc := N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show M35.cylinderChart q p ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from
        ⟨mem_univ _, hp⟩))
  have hd := (M35.cylinderChart_contMDiff q p).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp p (hc.mdifferentiableAt (by simp)) hd
  have hv (i : Fin 3) :
      mfderiv (𝓡 3) (𝓡 3) (N.coordinate_map ∘ M35.cylinderChart q) p
        (EuclideanSpace.basisFun (Fin 3) ℝ i) =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (M35.cylinderChart q p)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
          (M35.cylinderCoordinateEquiv p).1 (roundCylinderCoordinateBasis i).1,
          (roundCylinderCoordinateBasis i).2) := by
    have hchart := M35.mfderiv_cylinderChart q p (EuclideanSpace.basisFun (Fin 3) ℝ i)
    rw [M35.cylinderCoordinateEquiv_basis] at hchart
    exact (congrArg (fun L => L (EuclideanSpace.basisFun (Fin 3) ℝ i)) hcomp).trans
      (congrArg (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        N.coordinate_map (M35.cylinderChart q p)) hchart)
  exact congrArg₂ (fun v w => N.scale⁻¹ ^ 2 *
    g.inner (N.coordinate_map (M35.cylinderChart q p)) v w) (hv a) (hv b)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem exists_full_normalized_metric_realization (N : EpsilonNeck g) (q : UnitTwoSphere)
    {p : V} (hp : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ∃ (g' : RiemannianMetric 3 V) (_D' : LeviCivitaData g'),
      ∀ᶠ y in 𝓝 p, g'.euclideanCoefficients y =
        N.scale⁻¹ ^ 2 • g.pullbackCoefficients (N.coordinate_map ∘ M35.cylinderChart q) y := by
  let : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  let U : Set V := {y | (M35.cylinderCoordinateEquiv y).2 ∈
    Ioo (-N.epsilon⁻¹) N.epsilon⁻¹}
  let f := N.coordinate_map ∘ M35.cylinderChart q
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_snd.comp M35.cylinderCoordinateEquiv.continuous)
  have hscale : 0 < N.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  obtain ⟨g', D', W, hW, hpW, _, hcoeff⟩ :=
    RiemannianMetric.exists_local_realization hU hp
      (fun y => N.scale⁻¹ ^ 2 • g.pullbackCoefficients f y)
      (fun y hy => ((g.contDiffAt_pullbackCoefficients
        (N.full_euclidean_chart_regular q hy).1).const_smul _).contDiffWithinAt)
      (fun y _ v w => congrArg (fun a : ℝ => N.scale⁻¹ ^ 2 * a) (g.symm (f y) _ _))
      (fun y hy v hv => mul_pos hscale (g.pos (f y) _ (fun hz => hv
        ((N.full_euclidean_chart_regular q hy).2.injective
          (hz.trans (map_zero (mfderiv (𝓡 3) (𝓡 3) f y)).symm)))))
  exact ⟨g', D', Filter.mem_of_superset (hW.mem_nhds hpW) hcoeff⟩

theorem full_normalized_metric_lower (N : EpsilonNeck g)
    (he : N.epsilon ≤ 1 / 24) (q : UnitTwoSphere) (s : ℝ)
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v : V) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
      (N.scale⁻¹ ^ 2 • g.pullbackCoefficients (N.coordinate_map ∘ M35.cylinderChart q)
        (M35.cylinderCoordinateEquiv.symm (0, s))) v v := by
  let p := M35.cylinderCoordinateEquiv.symm (0, s)
  let B := N.scale⁻¹ ^ 2 • g.pullbackCoefficients (N.coordinate_map ∘ M35.cylinderChart q) p
  let C := M35.cylinderEuclideanCoefficients 0 p
  have hp : M35.cylinderCoordinateEquiv p = (0, s) :=
    M35.cylinderCoordinateEquiv.apply_symm_apply (0, s)
  have hdom : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    simpa only [hp] using hs
  have hB (i j : Fin 3) :
      |(B - C) (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)| ≤ 4 * N.epsilon := by
    have hb := N.metric_comparison.close.component_abs_lt N.epsilon_pos
      (by norm_num) (by norm_num) (z := (q, s)) hs (Nat.zero_le _) ![i, j]
    dsimp only at hb
    rw [M35.sphere_chart_center] at hb
    norm_num [roundCylinderIteratedDerivative] at hb
    have hC := M35.cylinderEuclideanMetric_basis 0 (by norm_num) q p i j
    change C (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) = _ at hC
    change |B (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) -
      C (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)| ≤ _
    rw [hC, N.full_euclidean_coefficient q hdom, hp]
    simpa only [inv_pow] using hb.le
  have herr := M35.abs_bilinear_le_of_components (B - C)
    (mul_nonneg (by norm_num) N.epsilon_pos.le) hB v
  change |B v v - C v v| ≤ 3 * (4 * N.epsilon) * ‖v‖ ^ 2 at herr
  have hmodel := M35.cylinderEuclideanCoefficients_lower (u := 0) le_rfl s v
  have hsmall : 3 * (4 * N.epsilon) * ‖v‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B v v
  have hlo := (abs_le.mp (herr.trans hsmall)).1
  change ‖v‖ ^ 2 ≤ C v v at hmodel
  linarith

end PoincareConjecture.EpsilonNeck
