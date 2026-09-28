import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.RoundSphere








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture

theorem roundCylinder_sphereChart_target (q : UnitTwoSphere) :
    (chartAt (EuclideanSpace ℝ (Fin 2)) q).target = univ := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  change (stereographic' 2 (-q)).target = univ
  exact stereographic'_target (-q)

private theorem sphereChart_symm_smooth (q : UnitTwoSphere) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm := by
  have h : ContMDiffOn (𝓡 2) (𝓡 2) ∞
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).target := contMDiffOn_chart_symm
  rw [roundCylinder_sphereChart_target] at h
  exact contMDiffOn_univ.mp h

private theorem sphereChart_symm_injective_derivative (q : UnitTwoSphere)
    (x : EuclideanSpace ℝ (Fin 2)) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 2)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x) := by
  have hx : x ∈ (extChartAt (𝓡 2) q).target := by
    simp [roundCylinder_sphereChart_target]
  simpa only [mfld_simps] using
    (isInvertible_mfderivWithin_extChartAt_symm hx).injective

private theorem roundCylinderGram_eq_spherePullback
    (u : ℝ) (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (a b : Fin 3) :
    roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b =
      2 * (1 - u) * (roundSphereMetric 2).inner
        ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1
          (roundCylinderCoordinateBasis a).1)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1
          (roundCylinderCoordinateBasis b).1) +
        (roundCylinderCoordinateBasis a).2 * (roundCylinderCoordinateBasis b).2 := by
  rfl


theorem contDiff_roundCylinderGram (u : ℝ) (q : UnitTwoSphere) (a b : Fin 3) :
    ContDiff ℝ ∞ (fun p =>
      roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) := by
  have h (v w : EuclideanSpace ℝ (Fin 2)) : ContDiff ℝ ∞ (fun x =>
      (roundSphereMetric 2).inner ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x v)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm x w)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (roundSphereMetric 2).contDiffAt_pullback_inner
      (sphereChart_symm_smooth q x) v w
  simp_rw [roundCylinderGram_eq_spherePullback]
  exact (contDiff_const.mul ((h _ _).comp contDiff_fst)).add contDiff_const


theorem roundCylinderGram_det_ne_zero {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) :
    (roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p).det ≠ 0 := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let A := mfderiv (𝓡 2) (𝓡 2) c.symm p.1
  let H : Matrix (Fin 2) (Fin 2) ℝ := fun a b =>
    (roundSphereMetric 2).inner (c.symm p.1)
      (A (EuclideanSpace.basisFun (Fin 2) ℝ a))
      (A (EuclideanSpace.basisFun (Fin 2) ℝ b))
  have hH : H.det ≠ 0 := (roundSphereMetric 2).pullback_gram_det_ne_zero
    (c.symm p.1) A.toLinearMap (sphereChart_symm_injective_derivative q p.1)
  have heq : (roundCylinderGram u c p).det = (2 * (1 - u)) ^ 2 * H.det := by
    rw [Matrix.det_fin_three, Matrix.det_fin_two]
    simp [c, roundCylinderGram_eq_spherePullback, roundCylinderCoordinateBasis, H, A]
    ring
  rw [heq]
  exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hu.ne'))) hH

private theorem contDiff_matrix_det
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : E → Matrix ι ι ℝ}
    (hA : ∀ a b, ContDiff ℝ ∞ (fun x => A x a b)) :
    ContDiff ℝ ∞ (fun x => (A x).det) := by
  have heq : (fun x => (A x).det) = fun x =>
      ∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℝ) * ∏ i, A x (σ i) i := by
    funext x
    simp [Matrix.det_apply, Units.smul_def]
  rw [heq]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hA (σ i) i)

private theorem contDiff_matrix_inv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : E → Matrix ι ι ℝ}
    (hA : ∀ a b, ContDiff ℝ ∞ (fun x => A x a b))
    (hdet : ∀ x, (A x).det ≠ 0) (a b : ι) :
    ContDiff ℝ ∞ (fun x => (A x)⁻¹ a b) := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv',
    Matrix.adjugate_apply]
  apply ((contDiff_matrix_det hA).inv hdet).mul
  apply contDiff_matrix_det
  intro i j
  by_cases hi : i = b
  · subst i
    simpa only [Matrix.updateRow_self] using
      (contDiff_const (c := (Pi.single a (1 : ℝ) : ι → ℝ) j) :
        ContDiff ℝ ∞ (fun _ : E => (Pi.single a (1 : ℝ) : ι → ℝ) j))
  · simpa only [Matrix.updateRow_ne hi] using hA i j


theorem contDiff_roundCylinderGram_inv {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (a b : Fin 3) :
    ContDiff ℝ ∞ (fun p =>
      (roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p)⁻¹ a b) :=
  contDiff_matrix_inv (contDiff_roundCylinderGram u q)
    (roundCylinderGram_det_ne_zero hu q) a b



theorem contDiff_roundCylinderChristoffel {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (a b d : Fin 3) :
    ContDiff ℝ ∞ (fun p =>
      roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) := by
  have hd (i j k : Fin 3) : ContDiff ℝ ∞ (fun p =>
      fderiv ℝ (fun z => roundCylinderGram u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) z i j) p
        (roundCylinderCoordinateBasis k)) :=
    ((contDiff_roundCylinderGram u q i j).fderiv_right (by simp)).clm_apply contDiff_const
  unfold roundCylinderChristoffel
  exact contDiff_const.mul (ContDiff.sum fun j _ =>
    (contDiff_roundCylinderGram_inv hu q a j).mul ((hd d j b).add (hd b j d) |>.sub (hd b d j)))

end PoincareConjecture
