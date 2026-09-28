import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarConjugate













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)






def scalarConjugateLinear (H : Plane → ℝ) (x : Plane) : Plane →L[ℝ] Plane :=
  (fderiv ℝ H x).smulRight (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
    (scalarConjugateForm D H x).smulRight (EuclideanSpace.basisFun (Fin 2) ℝ 1)







theorem scalar_gradient_energy_coordinates (H : Plane → ℝ) (x : Plane) :
    g.inner x (D.gradient H x) (D.gradient H x) =
      fderiv ℝ H x (EuclideanSpace.basisFun (Fin 2) ℝ 0) * WithLp.ofLp (D.gradient H x) 0 +
        fderiv ℝ H x (EuclideanSpace.basisFun (Fin 2) ℝ 1) *
          WithLp.ofLp (D.gradient H x) 1 := by
  have heq : mvfderiv (𝓡 2) H x (D.gradient H x) =
      fderiv ℝ H x (D.gradient H x) := by
    simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    rfl
  rw [D.inner_gradient, heq]
  exact M60.plane_form_apply (fderiv ℝ H x) (D.gradient H x)








theorem scalarConjugateLinear_invertible (H : Plane → ℝ) {x : Plane}
    (hgrad : D.gradient H x ≠ 0) : (scalarConjugateLinear D H x).IsInvertible := by
  let L := scalarConjugateLinear D H x
  let Z : Plane := D.gradient H x
  let rho := g.pullbackVolumeDensity id x
  let p0 := fderiv ℝ H x (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  let p1 := fderiv ℝ H x (EuclideanSpace.basisFun (Fin 2) ℝ 1)
  have hrho : 0 < rho := (g.contDiffAt_pullbackVolumeDensity (f := id)
    contMDiffAt_id (by simpa using Function.injective_id)).2
  have he : 0 < p0 * Z 0 + p1 * Z 1 := by
    rw [← scalar_gradient_energy_coordinates D H x]
    exact g.pos x _ hgrad
  have hinj : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    change L v = 0 at hv
    have h0 : p0 * v 0 + p1 * v 1 = 0 := by
      have h : fderiv ℝ H x v = 0 := by
        simpa [L, scalarConjugateLinear] using congrArg (fun z : Plane => z 0) hv
      simpa only [p0, p1, M60.plane_form_apply (fderiv ℝ H x) v] using h
    have h1 : -(rho * Z 1) * v 0 + (rho * Z 0) * v 1 = 0 := by
      have h := congrArg (fun z : Plane => z 1) hv
      simpa [L, scalarConjugateLinear, scalarConjugateForm, M60.rotatedFlux,
        scalarMetricFlux, rho, Z] using h
    have hflux : -Z 1 * v 0 + Z 0 * v 1 = 0 := by
      have hfactor : rho * (-Z 1 * v 0 + Z 0 * v 1) = 0 := by
        linear_combination h1
      exact (mul_eq_zero.mp hfactor).resolve_left hrho.ne'
    have hv0 : v 0 = 0 := by
      apply (mul_eq_zero.mp (show (p0 * Z 0 + p1 * Z 1) * v 0 = 0 from ?_)).resolve_left
        he.ne'
      linear_combination Z 0 * h0 - p1 * hflux
    have hv1 : v 1 = 0 := by
      apply (mul_eq_zero.mp (show (p0 * Z 0 + p1 * Z 1) * v 1 = 0 from ?_)).resolve_left
        he.ne'
      linear_combination Z 1 * h0 + p0 * hflux
    ext i
    fin_cases i
    · exact hv0
    · exact hv1
  exact ⟨(LinearEquiv.ofInjectiveEndo L.toLinearMap hinj).toContinuousLinearEquiv, rfl⟩

end PoincareConjecture.M64Uniformization
