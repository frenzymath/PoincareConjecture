import PoincareConjecture.Proofs.M35.RadialGauge.TensionEquivariance
import PoincareConjecture.Proofs.M35.RadialGauge.TensionContinuity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.RadialGauge

open Uniqueness

private theorem vector_eq_zero_of_rotations (v : StandardCapSpace)
    (hv : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, standardRotation A v = v) :
    v = 0 := by
  obtain ⟨A, hA⟩ := exists_axis_rotation v
  obtain ⟨B, hB⟩ := exists_axis_rotation (-v)
  rw [norm_neg] at hB
  have hAi : standardRotation A⁻¹ v = ‖v‖ • EuclideanSpace.single 2 1 := by
    have h := standardRotation_inv_apply A⁻¹ (‖v‖ • EuclideanSpace.single 2 1)
    rw [inv_inv, hA] at h
    exact h
  have hneg : v = -v := by
    calc
      v = standardRotation (B * A⁻¹) v := (hv (B * A⁻¹)).symm
      _ = -v := by rw [standardRotation_mul, hAi, hB]
  have hz : (2 : ℝ) • v = 0 := by
    calc
      (2 : ℝ) • v = v + v := two_smul ℝ v
      _ = v + -v := congrArg (fun z => v + z) hneg
      _ = 0 := add_neg_cancel v
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)



theorem mapTension_radialScale_rotation_all
    {g b : RiemannianMetric 3 StandardCapSpace}
    (D : LeviCivitaData g) (B : LeviCivitaData b)
    (hg : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hb : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        b.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = b.inner x u v)
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (he : Function.Even h)
    (hp : ∀ r, 0 < h r) (x : StandardCapSpace) :
    mapTension D B (radialScaleMap h) (standardRotation A x) =
      standardRotation A (mapTension D B (radialScaleMap h) x) := by
  have ht : Continuous (mapTension D B (radialScaleMap h)) :=
    (mapTension_contDiff D B (radialScaleMap_contDiff hh he)).continuous
  have hA : Continuous (standardRotation A) :=
    (Matrix.toEuclideanLin A.1).continuous_of_finiteDimensional
  have heq : (fun x => mapTension D B (radialScaleMap h) (standardRotation A x)) =
      fun x => standardRotation A (mapTension D B (radialScaleMap h) x) := by
    apply Continuous.ext_on (dense_compl_singleton (0 : StandardCapSpace))
      (ht.comp hA) (hA.comp ht)
    intro y hy
    exact mapTension_radialScale_rotation D B hg hb A hh he
      (by simpa only [mem_compl_iff, mem_singleton_iff] using hy) (hp ‖y‖)
  exact congrFun heq x



theorem mapTension_radialScale_zero
    {g b : RiemannianMetric 3 StandardCapSpace}
    (D : LeviCivitaData g) (B : LeviCivitaData b)
    (hg : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hb : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        b.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = b.inner x u v)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (he : Function.Even h)
    (hp : ∀ r, 0 < h r) : mapTension D B (radialScaleMap h) 0 = 0 := by
  apply vector_eq_zero_of_rotations
  intro A
  have h := mapTension_radialScale_rotation_all D B hg hb A hh he hp 0
  rw [show standardRotation A 0 = 0 from map_zero (Matrix.toEuclideanLin A.1)] at h
  exact h.symm

end PoincareConjecture.M35.RadialGauge
