import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityCoordinates
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Coordinates.Coefficients










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}

private theorem inverseChart_bijective (p : M) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (extChartAt (𝓡 3) p).target) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) p).symm x) := by
  have hleft := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hx
  have hright := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hx
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hleft hright
  have hi := ContinuousLinearMap.IsInvertible.of_inverse hright hleft
  exact hi.bijective




theorem m65EmbeddingMetric_coordinate (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (psi : EuclideanSpace ℝ (Fin 3) → M)
    (x : EuclideanSpace ℝ (Fin 3))
    (he : MDifferentiableAt (𝓡 3) (𝓡 N) e (psi x))
    (hpsi : MDifferentiableAt (𝓡 3) (𝓡 3) psi x)
    (hinj : Function.Injective (mfderiv (𝓡 3) (𝓡 N) e (psi x)))
    (hbij : Function.Bijective (mfderiv (𝓡 3) (𝓡 3) psi x)) :
    m65EmbeddingMetric g e (psi x) =
      M65Interior.coordinateMetric (fderiv ℝ (e ∘ psi) x) (g.pullbackCoefficients psi x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have : FiniteDimensional ℝ (TangentSpace (𝓡 3) (psi x)) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) (psi x)
  have : CompleteSpace (TangentSpace (𝓡 3) (psi x)) := FiniteDimensional.complete ℝ _
  let A : TangentSpace (𝓡 3) (psi x) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    mfderiv (𝓡 3) (𝓡 N) e (psi x)
  let D : EuclideanSpace ℝ (Fin 3) →L[ℝ] TangentSpace (𝓡 3) (psi x) :=
    mfderiv (𝓡 3) (𝓡 3) psi x
  let J : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] TangentSpace (𝓡 3) (psi x) :=
    (LinearEquiv.ofBijective D.toLinearMap hbij).toContinuousLinearEquiv
  have hdf : fderiv ℝ (e ∘ psi) x = A.comp (J : EuclideanSpace ℝ (Fin 3) →L[ℝ] _) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp x he hpsi
  have hmetric : g.pullbackCoefficients psi x =
      ContinuousLinearMap.bilinearComp (innerSL ℝ)
        (J : EuclideanSpace ℝ (Fin 3) →L[ℝ] TangentSpace (𝓡 3) (psi x))
        (J : EuclideanSpace ℝ (Fin 3) →L[ℝ] TangentSpace (𝓡 3) (psi x)) := by
    ext v w
    rfl
  change M65Interior.ambientMetric A = _
  rw [hdf, hmetric]
  exact M65Interior.ambientMetric_eq_coordinateMetric A hinj J




theorem m65EmbeddingMetric_contDiffOn_chart (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p)) (p : M) :
    ContDiffOn ℝ ∞ (fun x => m65EmbeddingMetric g e ((extChartAt (𝓡 3) p).symm x))
      (extChartAt (𝓡 3) p).target := by
  let psi := (extChartAt (𝓡 3) p).symm
  have hpsi (x) (hx : x ∈ (extChartAt (𝓡 3) p).target) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ psi x :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds hx)
  intro x hx
  have hcomp : ContDiffAt ℝ ∞ (e ∘ psi) x :=
    contMDiffAt_iff_contDiffAt.mp (he.contMDiffAt.comp x (hpsi x hx))
  have hA : ContDiffAt ℝ ∞ (fderiv ℝ (e ∘ psi)) x := hcomp.fderiv_right (by simp)
  have hG := g.contDiffAt_pullbackCoefficients (hpsi x hx)
  have hAi : Function.Injective (fderiv ℝ (e ∘ psi) x) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp x (he.contMDiffAt.mdifferentiableAt (by simp))
      ((hpsi x hx).mdifferentiableAt (by simp))]
    exact (hinj _).comp (inverseChart_bijective p hx).injective
  have hcoordinate := M65Interior.contDiffAt_coordinateMetric hA hG hAi
  have hsame : (fun y => m65EmbeddingMetric g e (psi y)) =ᶠ[𝓝 x]
      (fun y => M65Interior.coordinateMetric (fderiv ℝ (e ∘ psi) y)
        (g.pullbackCoefficients psi y)) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds hx] with y hy
    exact m65EmbeddingMetric_coordinate g e psi y
      (he.contMDiffAt.mdifferentiableAt (by simp)) ((hpsi y hy).mdifferentiableAt (by simp))
      (hinj _) (inverseChart_bijective p hy)
  exact (hcoordinate.congr_of_eventuallyEq hsame).contDiffWithinAt




theorem m65EmbeddingMetric_contMDiff (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p)) :
    ContMDiff (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin N) →L[ℝ]
      EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) ∞ (m65EmbeddingMetric g e) := by
  intro p
  have hx : extChartAt (𝓡 3) p p ∈ (extChartAt (𝓡 3) p).target :=
    (extChartAt (𝓡 3) p).map_source (mem_extChartAt_source p)
  have hc := (m65EmbeddingMetric_contDiffOn_chart g e he hinj p).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds hx)
  have hsame : m65EmbeddingMetric g e =ᶠ[𝓝 p]
      (fun q => m65EmbeddingMetric g e ((extChartAt (𝓡 3) p).symm (extChartAt (𝓡 3) p q))) := by
    filter_upwards [(isOpen_extChartAt_source (I := 𝓡 3) p).mem_nhds
      (mem_extChartAt_source (I := 𝓡 3) p)] with q hq
    rw [(extChartAt (𝓡 3) p).left_inv hq]
  exact (hc.contMDiffAt.comp p contMDiffAt_extChartAt).congr_of_eventuallyEq hsame

end PoincareConjecture
