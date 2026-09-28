import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawTimePrincipal
import PoincareConjecture.Proofs.M35.Thm12_28.ScalarMetricJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence
import PoincareConjecture.Proofs.M04.CurvatureSymmetries









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Topology Matrix.Norms.Elementwise

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)


theorem raw_volumeDensity_eq (g : RiemannianMetric n V) (x : V) :
    g.pullbackVolumeDensity id x = Real.sqrt (rawCoordinateGram g x).det := by
  simp only [RiemannianMetric.pullbackVolumeDensity, mfderiv_id,
    ContinuousLinearMap.id_apply, id_eq, EuclideanSpace.basisFun_apply]
  rfl


theorem raw_scalar_eq_inverse_gram {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (x : V) :
    D.scalarCurvature x = ∑ i, ∑ j, (rawCoordinateGram g x)⁻¹ i j *
      D.ricci x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  let b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hb (i : Fin n) : b i =
      EuclideanSpace.single i 1 := EuclideanSpace.basisFun_apply (Fin n) ℝ i
  have hg : (Matrix.of fun i j => g.inner x (b i) (b j)) = rawCoordinateGram g x := by
    ext i j
    change g.inner x (b i) (b j) =
      g.inner x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    rw [hb, hb]
  have h := scalarCurvature_eq_inverse_gram D x b
  rw [hg] at h
  simp only [hb] at h
  exact h

private theorem sqrt_det_hasDerivWithinAt
    {S : Set ℝ} {t : ℝ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, HasDerivWithinAt (fun s => A s i j) (B i j) S t)
    (hpos : 0 < (A t).det) :
    HasDerivWithinAt (fun s => Real.sqrt (A s).det)
      ((1 / 2) * Matrix.trace ((A t)⁻¹ * B) * Real.sqrt (A t).det) S t := by
  have hentry (i j : Fin n) :
      DifferentiableAt ℝ (fun C : Matrix (Fin n) (Fin n) ℝ => C i j) (A t) := by
    fun_prop
  have hdiff : DifferentiableAt ℝ
      (fun C : Matrix (Fin n) (Fin n) ℝ => Real.sqrt C.det) (A t) :=
    (Poincare.Matrix.differentiableAt_det hentry).sqrt hpos.ne'
  have hcurve : HasDerivWithinAt A B S t :=
    hasDerivWithinAt_pi.mpr fun i => hasDerivWithinAt_pi.mpr (hA i)
  have h := hdiff.hasFDerivAt.comp_hasDerivWithinAt t hcurve
  have heval (i j : Fin n) :
      fderiv ℝ (fun C : Matrix (Fin n) (Fin n) ℝ => C i j) (A t) B = B i j := by
    let p : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
      (Matrix.entryLinearMap (R := ℝ) (α := ℝ) i j).toContinuousLinearMap
    exact congrArg (fun L => L B) (p.hasFDerivAt.fderiv (x := A t))
  rw [Poincare.Matrix.fderiv_sqrt_det hentry hpos B] at h
  simpa only [heval, Matrix.of_apply, Function.comp_def] using! h



theorem raw_volumeDensity_hasDerivWithinAt {J : Set ℝ} (F : RicciFlow n V J)
    {t : ℝ} (ht : t ∈ J) (x : V) :
    HasDerivWithinAt (fun s => (F.metric s).pullbackVolumeDensity id x)
      (-(F.connection t).scalarCurvature x * (F.metric t).pullbackVolumeDensity id x)
      J t := by
  let B : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    -2 * (F.connection t).ricci x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have h := sqrt_det_hasDerivWithinAt (fun s => rawCoordinateGram (F.metric s) x) B
    (fun i j => F.equation t ht x _ _) (rawCoordinateGram_posDef (F.metric t) x).det_pos
  have htrace : Matrix.trace ((rawCoordinateGram (F.metric t) x)⁻¹ * B) =
      -2 * (F.connection t).scalarCurvature x := by
    rw [raw_scalar_eq_inverse_gram (F.connection t) x]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, B, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [M04.ricci_symm (F.connection t) x (EuclideanSpace.single j 1)]
    ring
  simp only [htrace, ← raw_volumeDensity_eq] at h
  convert h using 1
  ring


theorem raw_volumeDensity_continuousOn {J : Set ℝ} (F : RicciFlow n V J) :
    ContinuousOn (fun p : ℝ × V => (F.metric p.1).pullbackVolumeDensity id p.2)
      (J ×ˢ univ) := by
  simp only [raw_volumeDensity_eq]
  exact ((continuous_id.matrix_det).comp_continuousOn
    (rawCoordinateGram_family_continuousOn F)).sqrt

end PoincareConjecture.M35.Uniqueness.Heat
