import PoincareConjecture.Proofs.M34.Standard.RotationOrbit
import PoincareConjecture.Proofs.M13.ContractionTransport









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Matrix

namespace PoincareConjecture.Proofs.M47

private theorem rotation_mul (A B : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (x : StandardCapSpace) :
    standardRotation (A * B) x = standardRotation A (standardRotation B x) := by
  change WithLp.toLp 2 ((A.1 * B.1) *ᵥ x.ofLp) =
    WithLp.toLp 2 (A.1 *ᵥ (B.1 *ᵥ x.ofLp))
  rw [Matrix.mulVec_mulVec]

private theorem rotation_one (x : StandardCapSpace) : standardRotation 1 x = x := by
  change Matrix.toEuclideanLin (1 : Matrix (Fin 3) (Fin 3) ℝ) x = x
  simp

private theorem rotation_inv_apply
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x : StandardCapSpace) :
    standardRotation A (standardRotation A⁻¹ x) = x := by
  rw [← rotation_mul, mul_inv_cancel, rotation_one]

private noncomputable def rotationDiffeomorph
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ where
  toFun := standardRotation A
  invFun := standardRotation A⁻¹
  left_inv := by
    intro x
    simpa only [inv_inv] using rotation_inv_apply A⁻¹ x
  right_inv := rotation_inv_apply A
  contMDiff_toFun := contMDiff_iff_contDiff.mpr
    (Matrix.toEuclideanLin A.1).toContinuousLinearMap.contDiff
  contMDiff_invFun := contMDiff_iff_contDiff.mpr
    (Matrix.toEuclideanLin (A⁻¹).1).toContinuousLinearMap.contDiff

private theorem rotation_mfderiv
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x : StandardCapSpace) :
    mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x =
      (Matrix.toEuclideanLin A.1).toContinuousLinearMap := by
  rw [mfderiv_eq_fderiv]
  exact (Matrix.toEuclideanLin A.1).toContinuousLinearMap.hasFDerivAt.fderiv



theorem rotational_tip_ricci_isotropic
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (u v : StandardCapSpace) :
    D.ricci 0 u u * g.inner 0 v v = D.ricci 0 v v * g.inner 0 u u := by
  have hR (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (a b : StandardCapSpace) :
      D.ricci 0 (standardRotation A a) (standardRotation A b) = D.ricci 0 a b := by
    let f := rotationDiffeomorph A
    have hf : MetricHomothety g g f 1 := by
      intro y c d
      change g.inner (standardRotation A y)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) y c)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) y d) = _
      simpa only [one_mul] using hrotation A y c d
    have h := M13.homothety_ricci_eq g g f 1 zero_lt_one hf D D 0 a b
    change D.ricci (standardRotation A 0)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) 0 a)
      (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) 0 b) = D.ricci 0 a b at h
    rw [rotation_mfderiv] at h
    change D.ricci (Matrix.toEuclideanLin A.1 0)
      (standardRotation A a) (standardRotation A b) = D.ricci 0 a b at h
    rwa [map_zero] at h
  have hG (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (a b : StandardCapSpace) :
      g.inner 0 (standardRotation A a) (standardRotation A b) = g.inner 0 a b := by
    have h := hrotation A 0 a b
    rw [rotation_mfderiv] at h
    change g.inner (Matrix.toEuclideanLin A.1 0)
      (standardRotation A a) (standardRotation A b) = g.inner 0 a b at h
    rwa [map_zero] at h
  let e0 : StandardCapSpace := EuclideanSpace.single 0 1
  have hdiag (w : StandardCapSpace) :
      D.ricci 0 w w = ‖w‖ ^ 2 * D.ricci 0 e0 e0 ∧
        g.inner 0 w w = ‖w‖ ^ 2 * g.inner 0 e0 e0 := by
    obtain ⟨A, hA⟩ := M34.exists_standardRotation_axis w
    have haxis : EuclideanSpace.single (0 : Fin 3) ‖w‖ = ‖w‖ • e0 := by
      ext i
      simp [e0, EuclideanSpace.single]
    rw [haxis] at hA
    have hRic := hR A (‖w‖ • e0) (‖w‖ • e0)
    have hMetric := hG A (‖w‖ • e0) (‖w‖ • e0)
    rw [hA] at hRic hMetric
    constructor
    · change M13.ricciLinear D 0 w w = _
      change M13.ricciLinear D 0 w w =
        M13.ricciLinear D 0 (‖w‖ • e0) (‖w‖ • e0) at hRic
      rw [hRic]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, M13.ricciLinear_apply]
      ring
    · rw [hMetric]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
  rw [(hdiag u).1, (hdiag v).1, (hdiag u).2, (hdiag v).2]
  ring

end PoincareConjecture.Proofs.M47
