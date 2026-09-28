import PoincareConjecture.Proofs.M49.NeckCoordinates
import PoincareConjecture.Proofs.M49.NeckMetricComparison
import PoincareConjecture.Proofs.M49.Mathlib.GramScaling
import PoincareConjecture.Proofs.M10.PullbackJacobian
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M49

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

set_option backward.isDefEq.respectTransparency false in

theorem epsilonNeckEuclideanChart_pullback_coefficient
    (N : EpsilonNeck g) (q : UnitTwoSphere) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ (epsilonNeckEuclideanChart N q).source) (i j : Fin 3) :
    M10.pullbackMetricForm g (epsilonNeckEuclideanChart N q) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate_map)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) (cylinderCoordinateEquiv x) i j := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let p := cylinderCoordinateEquiv x
  let L1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp
      cylinderCoordinateEquiv.toContinuousLinearMap
  let L2 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp
      cylinderCoordinateEquiv.toContinuousLinearMap
  let F : EuclideanSpace ℝ (Fin 3) → RoundCylinderSpace :=
    fun y => (c.symm (L1 y), L2 y)
  have hx0 : p.1 ∈ c.target ∧ p.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    simpa only [epsilonNeckEuclideanChart_source, mem_preimage, mem_prod] using hx
  have hL1 : MDifferentiableAt (𝓡 3) (𝓡 2) L1 x :=
    L1.contDiff.contMDiff.mdifferentiable (n := ∞) (by simp) x
  have hL2 : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) L2 x :=
    L2.contDiff.contMDiff.mdifferentiable (n := ∞) (by simp) x
  have hcs : MDifferentiableAt (𝓡 2) (𝓡 2) c.symm (L1 x) :=
    (contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds hx0.1)).mdifferentiableAt
      (n := ∞) (by simp)
  have hF : MDifferentiableAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) F x :=
    (hcs.comp x hL1).prodMk hL2
  have hN : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (F x) :=
    (N.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hx0.2⟩)).mdifferentiableAt
        (by simp)
  have hfirst : mfderiv (𝓡 3) (𝓡 2) (fun y => c.symm (L1 y)) x =
      (mfderiv (𝓡 2) (𝓡 2) c.symm p.1).comp L1 := by
    erw [mfderiv_comp x hcs hL1, mfderiv_eq_fderiv, L1.fderiv]
    rfl
  have hDF : mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) F x =
      ((mfderiv (𝓡 2) (𝓡 2) c.symm p.1).comp L1).prod L2 := by
    erw [mfderiv_prodMk (hcs.comp x hL1) hL2, hfirst, mfderiv_eq_fderiv, L2.fderiv]
  have hD : mfderiv (𝓡 3) (𝓡 3) (epsilonNeckEuclideanChart N q) x =
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (F x)).comp
        (((mfderiv (𝓡 2) (𝓡 2) c.symm p.1).comp L1).prod L2) := by
    change mfderiv (𝓡 3) (𝓡 3) (N.coordinate_map ∘ F) x = _
    rw [mfderiv_comp x hN hF, hDF]
  have h1 (k : Fin 3) : L1 (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      (roundCylinderCoordinateBasis k).1 :=
    congrArg Prod.fst (cylinderCoordinateEquiv_basis k)
  have h2 (k : Fin 3) : L2 (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      (roundCylinderCoordinateBasis k).2 :=
    congrArg Prod.snd (cylinderCoordinateEquiv_basis k)
  have hDeval (k : Fin 3) :
      mfderiv (𝓡 3) (𝓡 3) (epsilonNeckEuclideanChart N q) x
          (EuclideanSpace.basisFun (Fin 3) ℝ k) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (F x)
          (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 (roundCylinderCoordinateBasis k).1,
            (roundCylinderCoordinateBasis k).2) := by
    rw [hD]
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (F x)
      (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 (L1 (EuclideanSpace.basisFun (Fin 3) ℝ k)),
        L2 (EuclideanSpace.basisFun (Fin 3) ℝ k)) = _
    rw [h1, h2]
  simp only [M10.pullbackMetricForm, ContinuousLinearMap.bilinearComp_apply]
  erw [hDeval i, hDeval j]
  rfl

theorem epsilonNeck_coefficient_error_le (N : EpsilonNeck g)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) (hp : p.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (i j : Fin 3) :
    |N.scale⁻¹ ^ 2 * roundCylinderTensorCoefficient
        (roundCylinderPullback g N.coordinate_map) c p i j - roundCylinderGram 0 c p i j| ≤
      N.epsilon * Real.sqrt (roundCylinderGram 0 c p i i) *
        Real.sqrt (roundCylinderGram 0 c p j j) := by
  exact epsilonNeck_bilinear_error_le N (c.symm p.1, p.2) hp
    (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 (roundCylinderCoordinateBasis i).1,
      (roundCylinderCoordinateBasis i).2)
    (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 (roundCylinderCoordinateBasis j).1,
      (roundCylinderCoordinateBasis j).2)

theorem epsilonNeckEuclideanChart_jacobian_eq
    (N : EpsilonNeck g) (q : UnitTwoSphere) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ (epsilonNeckEuclideanChart N q).source) :
    M10.pullbackJacobian g (epsilonNeckEuclideanChart N q) x =
      N.scale ^ 3 * Real.sqrt (Matrix.det (fun i j : Fin 3 =>
        N.scale⁻¹ ^ 2 * roundCylinderTensorCoefficient
          (roundCylinderPullback g N.coordinate_map)
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) (cylinderCoordinateEquiv x) i j)) := by
  let Q : Matrix (Fin 3) (Fin 3) ℝ := roundCylinderTensorCoefficient
    (roundCylinderPullback g N.coordinate_map)
    (chartAt (EuclideanSpace ℝ (Fin 2)) q) (cylinderCoordinateEquiv x)
  have hQ : (fun i j : Fin 3 => M10.pullbackMetricForm g
      (epsilonNeckEuclideanChart N q) x (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) = Q := by
    funext i j
    exact epsilonNeckEuclideanChart_pullback_coefficient N q x hx i j
  rw [M10.pullbackJacobian, hQ]
  change Real.sqrt Q.det = N.scale ^ 3 * Real.sqrt ((N.scale⁻¹ ^ 2) • Q).det
  rw [Matrix.sqrt_det_smul_sq Q (inv_nonneg.mpr N.scale_pos.le)]
  simp only [Fintype.card_fin, inv_pow]
  field_simp [N.scale_pos.ne']

end PoincareConjecture.M49
