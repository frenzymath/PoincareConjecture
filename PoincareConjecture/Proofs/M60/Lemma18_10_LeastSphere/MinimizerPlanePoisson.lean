import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerPoissonComparison
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakHessian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Euclidean










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace

noncomputable section

namespace PoincareConjecture.M60

open LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.NirenbergEuclidean

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "gEucl" => RiemannianMetric.euclideanMetric 2



def suPlaneLaplaceForm : SmoothEllipticBilinearForm 2 (univ : Set Plane) where
  a := fun _ => 1
  c := fun _ => 0
  symm := by intro x i j; simp [Matrix.one_apply, eq_comm]
  smooth_a := by intro i j; exact contDiff_const
  smooth_c := contDiff_const
  lam := 1
  capLam := 1
  hlam_pos := by norm_num
  hlam_le_capLam := le_rfl
  coercive := by
    intro x _ v
    simp [matMulE]



theorem suPlane_volumeDensity (x : Plane) :
    (gEucl).pullbackVolumeDensity (OpenPartialHomeomorph.refl Plane) x = 1 := by
  have h := (gEucl).pullbackVolumeDensity_id_bounds x
    (show (0 : ℝ) < 1 by norm_num) (b := 1) (by
      intro v
      change 1 * ‖v‖ ^ 2 ≤ (gEucl).inner x v v ∧
        (gEucl).inner x v v ≤ 1 * ‖v‖ ^ 2
      simp)
  have he : (gEucl).pullbackVolumeDensity id x = 1 :=
    le_antisymm (by simpa using h.2) (by simpa using h.1)
  exact he



theorem suPlane_divergenceCoefficients (x : Plane) (i j : Fin 2) :
    divergenceCoefficients gEucl (OpenPartialHomeomorph.refl Plane) x i j =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  have hb : (gEucl).pullbackCoefficients (OpenPartialHomeomorph.refl Plane) x =
      innerSL ℝ := by
    ext v w
    simp [RiemannianMetric.pullbackCoefficients]
    rfl
  have hp : EuclideanSpace.proj j = (innerSL ℝ) (EuclideanSpace.single j 1) := by
    ext v
    simp [EuclideanSpace.inner_single_left]
  have hi : (innerSL ℝ : Plane →L[ℝ] Plane →L[ℝ] ℝ).IsInvertible :=
    (gEucl).inner_isInvertible x
  rw [divergenceCoefficients, suPlane_volumeDensity, one_mul, hb, hp,
    hi.inverse_apply_self]
  simp [Matrix.one_apply]



theorem suPlane_poisson_equation
    (D : LeviCivitaData gEucl) {Ω K O : Set Plane} (hK : IsCompact K)
    (hOK : O ⊆ K) (hOΩ : O ⊆ Ω) (w : H1Zero D Ω)
    (F : Lp ℝ 2 (gEucl).volumeMeasure)
    (hw : ∀ v, gradientEnergy D Ω w v = inner ℝ F (toL2 D Ω v))
    {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) :
    (∫ x in O, ∑ j : Fin 2,
      coordinateDerivative (OpenPartialHomeomorph.refl Plane)
        contMDiffOn_id contMDiffOn_id hK (subset_univ _)
        (EuclideanSpace.single j 1) w x *
          fderiv ℝ φ x (EuclideanSpace.single j 1)) = ∫ x in O, F x * φ x := by
  have h := weakPoisson_divergence_local (OpenPartialHomeomorph.refl Plane)
    contMDiffOn_id contMDiffOn_id hK (subset_univ _) hOK (by simpa using hOΩ)
    w F hw hφ hφc hφO
  have hd (x : Plane) : (gEucl).pullbackVolumeDensity id x = 1 := suPlane_volumeDensity x
  have h' : (∫ x in O, ∑ j : Fin 2,
      localCoordinateDerivative (OpenPartialHomeomorph.refl Plane)
        contMDiffOn_id contMDiffOn_id hK (subset_univ _) hOK
        (EuclideanSpace.single j 1) w x *
          fderiv ℝ φ x (EuclideanSpace.single j 1)) = ∫ x in O, F x * φ x := by
    simpa [suPlane_divergenceCoefficients, hd, Matrix.one_apply] using h
  have hae : ∀ᵐ x ∂volume.restrict O, ∀ j : Fin 2,
      localCoordinateDerivative (OpenPartialHomeomorph.refl Plane)
        contMDiffOn_id contMDiffOn_id hK (subset_univ _) hOK
        (EuclideanSpace.single j 1) w x =
      coordinateDerivative (OpenPartialHomeomorph.refl Plane)
        contMDiffOn_id contMDiffOn_id hK (subset_univ _)
        (EuclideanSpace.single j 1) w x := by
    apply ae_all_iff.mpr
    intro j
    exact Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp)
      (by simpa only [one_smul] using Measure.restrict_mono hOK (le_refl volume)) _
  refine Eq.trans ?_ h'
  apply integral_congr_ae
  filter_upwards [hae] with x hx
  simp only [hx]



theorem suPlane_coordinate_weak
    (D : LeviCivitaData gEucl) {Ω K O : Set Plane} (hK : IsCompact K)
    (hO : IsOpen O) (hOK : O ⊆ K) (w : H1Zero D Ω) (i : Fin 2) :
    HasWeakPartialDeriv i
      (coordinateDerivative (OpenPartialHomeomorph.refl Plane)
        contMDiffOn_id contMDiffOn_id hK (subset_univ _)
        (EuclideanSpace.single i 1) w) (toL2 D Ω w) O := by
  intro φ hφ hφc hφO
  have h := localCoordinateDerivative_weak (OpenPartialHomeomorph.refl Plane)
    contMDiffOn_id contMDiffOn_id hK (subset_univ _) hOK hO w i hφ hφc hφO
  have hae : (localCoordinateDerivative (OpenPartialHomeomorph.refl Plane)
      contMDiffOn_id contMDiffOn_id hK (subset_univ _) hOK
      (EuclideanSpace.single i 1) w : Plane → ℝ) =ᵐ[volume.restrict O]
      coordinateDerivative (OpenPartialHomeomorph.refl Plane)
        contMDiffOn_id contMDiffOn_id hK (subset_univ _)
        (EuclideanSpace.single i 1) w :=
    Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp)
      (by simpa only [one_smul] using Measure.restrict_mono hOK (le_refl volume)) _
  exact h.trans (congrArg Neg.neg (integral_congr_ae (hae.mul EventuallyEq.rfl)))

end PoincareConjecture.M60

end
