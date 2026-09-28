import PoincareConjecture.Proofs.M65.Sec19_5_Limits.AreaContinuity.ContractionDerivative

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

open Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m65ContractionAnnulusMap_diagonal_density (g : RiemannianMetric 3 M)
    (C : ℝ × (M × M) → M) (hdiag : ∀ s p, C (s, p, p) = p)
    (gamma : C1FreeLoopSpace (M := M)) (p : LoopPlane) :
    m60AreaDensity g (m65ContractionAnnulusMap C gamma gamma) p = 0 := by
  have heq : m65ContractionAnnulusMap C gamma gamma =
      periodicFreeLoop gamma ∘ (fun q : LoopPlane => q 0) :=
    funext fun q => hdiag _ _
  rw [heq]
  have hcoord : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ)
      (fun q : LoopPlane => q 0) p :=
    (show DifferentiableAt ℝ (fun q : LoopPlane => q 0) p from
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).differentiableAt).mdifferentiableAt
  have hd : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun q : LoopPlane => q 0) p
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0 := by
    rw [mfderiv_eq_fderiv]
    change (fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) p)
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0
    rw [(EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).fderiv]
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single]
  have hzero : mfderiv (𝓡 2) (𝓡 3)
      (periodicFreeLoop gamma ∘ (fun q : LoopPlane => q 0)) p
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0 := by
    erw [mfderiv_comp_apply p
      ((contMDiff_periodicFreeLoop gamma).mdifferentiableAt one_ne_zero) hcoord, hd, map_zero]
  unfold m60AreaDensity m60AreaGram
  dsimp only
  erw [Matrix.det_fin_two, hzero]
  simp

end PoincareConjecture
