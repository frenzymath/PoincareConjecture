import PoincareConjecture.Proofs.M25.AppA_1_Necks.RoundCylinderReflectionJets
import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderCoefficients










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



noncomputable def roundCylinderAxialReflection :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞ where
  toFun := fun z => (z.1, -z.2)
  invFun := fun z => (z.1, -z.2)
  left_inv := by intro z; simp
  right_inv := by intro z; simp
  contMDiff_toFun := contMDiff_fst.prodMk
    (contDiff_neg.contMDiff.comp contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk
    (contDiff_neg.contMDiff.comp contMDiff_snd)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]


set_option backward.isDefEq.respectTransparency false in


theorem roundCylinderTensorCoefficient_smul_pullback_axialReflection
    (g : RiemannianMetric 3 M) (a : ℝ) (f : RoundCylinderSpace → M)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates)
    (hf : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, -p.2))
    (i j : Fin 3) :
    roundCylinderTensorCoefficient
        (fun z v w => a * roundCylinderPullback g
          (fun y => f (roundCylinderAxialReflection y)) z v w)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j =
      roundCylinderAxialSign i * roundCylinderAxialSign j *
        roundCylinderTensorCoefficient
          (fun z v w => a * roundCylinderPullback g f z v w)
          (chartAt (EuclideanSpace ℝ (Fin 2)) q)
          (roundCylinderCoordinateReflection p) i j := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let ψ : RoundCylinderCoordinates → RoundCylinderSpace := fun y => (c.symm y.1, y.2)
  let F : RoundCylinderCoordinates → M := f ∘ ψ
  let J := roundCylinderCoordinateReflection
  have hρ : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      roundCylinderAxialReflection (ψ p) :=
    roundCylinderAxialReflection.contMDiff.mdifferentiable (by simp) _
  have hfr : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      (fun z => f (roundCylinderAxialReflection z)) (ψ p) := hf.comp (ψ p) hρ
  have hF : MDifferentiableAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) F (J p) :=
    hf.comp (J p) ((cylinderChart_symm_smooth q).mdifferentiable (by simp) _)
  change a * roundCylinderTensorCoefficient
      (roundCylinderPullback g (fun z => f (roundCylinderAxialReflection z))) c p i j =
    roundCylinderAxialSign i * roundCylinderAxialSign j *
      (a * roundCylinderTensorCoefficient (roundCylinderPullback g f) c (J p) i j)
  rw [roundCylinderTensorCoefficient_pullback_eq g q _ p hfr i j,
    roundCylinderTensorCoefficient_pullback_eq g q f (J p) hf i j]
  change a * g.inner (F (J p))
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (F ∘ J) p
        (roundCylinderCoordinateBasis i))
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (F ∘ J) p
        (roundCylinderCoordinateBasis j)) =
    roundCylinderAxialSign i * roundCylinderAxialSign j *
      (a * g.inner (F (J p))
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) F (J p)
          (roundCylinderCoordinateBasis i))
        (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) F (J p)
          (roundCylinderCoordinateBasis j)))
  have hD (v : RoundCylinderCoordinates) :
      mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (F ∘ J) p v =
        mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) F (J p) (J v) := by
    rw [mfderiv_comp_apply p hF J.mdifferentiableAt, J.mfderiv_eq]
    rfl
  rw [hD, hD]
  simp only [J,
    roundCylinderCoordinateReflection_basis, map_smul, smul_apply, smul_eq_mul]
  ring



theorem NeckMetricJetComparison.axialReflection
    {g : RiemannianMetric 3 M} {epsilon scale : ℝ} {f : RoundCylinderSpace → M}
    (h : NeckMetricJetComparison g epsilon scale f)
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹)) :
    NeckMetricJetComparison g epsilon scale
      (fun z => f (roundCylinderAxialReflection z)) := by
  refine ⟨h.close.axialReflection ?_⟩
  intro q p hp i j
  have hmem : ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, -p.2) ∈
      (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ : Set RoundCylinderSpace) := by
    refine ⟨mem_univ _, ?_⟩
    constructor <;> linarith [hp.2.1, hp.2.2]
  exact roundCylinderTensorCoefficient_smul_pullback_axialReflection g (scale⁻¹ ^ 2)
    f q p ((hf.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hmem)).mdifferentiableAt
      (by simp)) i j

end PoincareConjecture
