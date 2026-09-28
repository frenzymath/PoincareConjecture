import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.CompetitorGramBound
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiEnergy
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped Manifold ContDiff Bundle Matrix.Norms.Elementwise

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]




theorem m65SpanningDisk_energy_integrable [T2Space M]
    {g : RiemannianMetric 3 M} {γ : C1FreeLoopSpace (M := M)}
    (D : LipschitzSpanningDisk g γ) :
    IntegrableOn (m60AreaGram g D.map) loopDiskSet volume ∧
      IntegrableOn (m60EnergyDensity g D.map) loopDiskSet volume := by
  let : IsFiniteMeasure (volume.restrict loopDiskSet) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : LoopPlane) 1).measure_ne_top
  have hm := m65AreaGram_aestronglyMeasurable g (isCompact_closedBall 0 1)
    D.continuous_on_disk D.ae_manifold_differentiable
  have hi : IntegrableOn (m60AreaGram g D.map) loopDiskSet volume :=
    (integrable_const ((2 * D.lipschitz_constant) ^ 2)).mono' hm
      (m65SpanningDisk_gram_bound D)
  let ev (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))
  have he (i : Fin 2) : IntegrableOn (fun z => m60AreaGram g D.map z i i)
      loopDiskSet volume := (ev i).integrable_comp hi
  refine ⟨hi, ?_⟩
  change Integrable (fun z => (1 / 2 : ℝ) * (m60AreaGram g D.map z).trace)
    (volume.restrict loopDiskSet)
  simpa only [Matrix.trace, Fin.sum_univ_two,
    Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply] using!
      ((he 0).add (he 1)).const_mul (1 / 2 : ℝ)




theorem m65AreaGram_comp (g : RiemannianMetric 3 M)
    (f : LoopPlane → M) (φ : LoopPlane → LoopPlane) (z : LoopPlane)
    (hf : MDifferentiableAt (𝓡 2) (𝓡 3) f (φ z))
    (hφ : DifferentiableAt ℝ φ z) :
    let B := LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (fderiv ℝ φ z).toLinearMap
    m60AreaGram g (f ∘ φ) z = B.transpose * m60AreaGram g f (φ z) * B := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let d := mfderiv (𝓡 2) (𝓡 3) f (φ z)
  let A := fderiv ℝ φ z
  let B := LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap
  have hB (i j : Fin 2) : B i j = (A (b j)) i := by
    simp only [B, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, b, EuclideanSpace.basisFun_repr]
    rfl
  have hrep (v : LoopPlane) : d v = v 0 • d (b 0) + v 1 • d (b 1) := by
    have hv : v = v 0 • b 0 + v 1 • b 1 := by
      simpa only [Fin.sum_univ_two, EuclideanSpace.basisFun_repr] using
        ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr v).symm
    calc
      d v = d (v 0 • b 0 + v 1 • b 1) := congrArg d hv
      _ = _ := by rw [map_add, map_smul, map_smul]
  change m60AreaGram g (f ∘ φ) z = B.transpose * m60AreaGram g f (φ z) * B
  ext i j
  simp only [m60AreaGram, mfderiv_comp z hf hφ.mdifferentiableAt, mfderiv_eq_fderiv]
  change inner ℝ (d (A (b i))) (d (A (b j))) = _
  rw [hrep (A (b i)), hrep (A (b j))]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, hB]
  change _ =
    ((A (b i)) 0 * inner ℝ (d (b 0)) (d (b 0)) +
      (A (b i)) 1 * inner ℝ (d (b 1)) (d (b 0))) * (A (b j)) 0 +
    ((A (b i)) 0 * inner ℝ (d (b 0)) (d (b 1)) +
      (A (b i)) 1 * inner ℝ (d (b 1)) (d (b 1))) * (A (b j)) 1
  ring

end PoincareConjecture
