import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationIsothermalMetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

noncomputable section

namespace PoincareConjecture.M60

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private def conjugateCoordinateLinear (g : RiemannianMetric 2 Plane)
    (D : LeviCivitaData g) (x : Plane) : Plane →L[ℝ] Plane :=
  (EuclideanSpace.proj 0).smulRight (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
    (conjugateMetricForm g D x).smulRight (EuclideanSpace.basisFun (Fin 2) ℝ 1)

private theorem conjugateCoordinateLinear_metric (g : RiemannianMetric 2 Plane)
    (D : LeviCivitaData g) (x v w : Plane) :
    g.inner x v w = (firstCoordinateGradient g D x 0)⁻¹ *
      inner ℝ (conjugateCoordinateLinear g D x v) (conjugateCoordinateLinear g D x w) := by
  rw [metric_eq_conjugate_coordinates]
  congr 1
  simp only [conjugateCoordinateLinear, add_apply, ContinuousLinearMap.smulRight_apply,
    EuclideanSpace.coe_proj, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, conj_trivial,
    (EuclideanSpace.basisFun (Fin 2) ℝ).inner_eq_ite]
  norm_num
  ring

private theorem conjugateCoordinateLinear_invertible (g : RiemannianMetric 2 Plane)
    (D : LeviCivitaData g) (x : Plane) : (conjugateCoordinateLinear g D x).IsInvertible := by
  let L := conjugateCoordinateLinear g D x
  have hinj : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have he := conjugateCoordinateLinear_metric g D x v v
    change L v = 0 at hv
    change g.inner x v v = _ * inner ℝ (L v) (L v) at he
    rw [hv, inner_zero_left, mul_zero] at he
    by_contra hne
    exact (g.pos x v hne).ne' he
  exact ⟨(LinearEquiv.ofInjectiveEndo L.toLinearMap hinj).toContinuousLinearEquiv, rfl⟩




theorem exists_isothermal_coordinates_of_harmonic
    (g : RiemannianMetric 2 Plane) (D : LeviCivitaData g)
    {S : Set Plane} (hS : IsOpen S) (hstar : StarConvex ℝ 0 S) (hzero : 0 ∈ S)
    (hharmonic : ∀ x ∈ S, D.laplacian (fun y : Plane => y 0) x = 0) :
    ∃ e : OpenPartialHomeomorph Plane Plane,
      0 ∈ e.source ∧ e.source ⊆ S ∧ ContDiff ℝ ∞ e ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ x ∈ e.source, (fderiv ℝ e x).IsInvertible ∧ ∀ v w : Plane,
        g.inner x v w = (firstCoordinateGradient g D x 0)⁻¹ *
          inner ℝ (fderiv ℝ e x v) (fderiv ℝ e x w) := by
  obtain ⟨V, hV, hdV⟩ := exists_conjugate_of_harmonic_coordinate g D hstar hharmonic
  let H : Plane → Plane := fun x =>
    x 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
      V x • EuclideanSpace.basisFun (Fin 2) ℝ 1
  have hH : ContDiff ℝ ∞ H :=
    ((show Plane →L[ℝ] ℝ from EuclideanSpace.proj 0).contDiff.smul contDiff_const).add
      (hV.smul contDiff_const)
  have hdH (x : Plane) (hx : x ∈ S) :
      HasFDerivAt H (conjugateCoordinateLinear g D x) x := by
    exact ((show Plane →L[ℝ] ℝ from EuclideanSpace.proj 0).hasFDerivAt.smul_const
      (EuclideanSpace.basisFun (Fin 2) ℝ 0)).add
      ((hdV x hx).smul_const (EuclideanSpace.basisFun (Fin 2) ℝ 1))
  obtain ⟨L, hL⟩ := conjugateCoordinateLinear_invertible g D 0
  have hd0 : HasFDerivAt H (L : Plane →L[ℝ] Plane) 0 := by
    rw [hL]
    exact hdH 0 hzero
  let e0 := hH.contDiffAt.toOpenPartialHomeomorph H hd0 (by simp)
  let e := e0.restr S
  have heH : (e : Plane → Plane) = H := rfl
  have hesource : e.source = e0.source ∩ S := e0.restr_source' S hS
  have hsub : e.source ⊆ S := by rw [hesource]; exact inter_subset_right
  refine ⟨e, ?_, hsub, ?_, ?_, ?_⟩
  · rw [hesource]
    exact ⟨hH.contDiffAt.mem_toOpenPartialHomeomorph_source hd0 (by simp), hzero⟩
  · rwa [heH]
  · intro y hy
    have hx := hsub (e.map_target hy)
    obtain ⟨Ly, hLy⟩ := conjugateCoordinateLinear_invertible g D (e.symm y)
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm (f₀' := Ly) hy
    · rw [heH, hLy]
      exact hdH _ hx
    · rw [heH]
      exact hH.contDiffAt
  · intro x hx
    rw [heH, (hdH x (hsub hx)).fderiv]
    exact ⟨conjugateCoordinateLinear_invertible g D x,
      conjugateCoordinateLinear_metric g D x⟩

end PoincareConjecture.M60

end
