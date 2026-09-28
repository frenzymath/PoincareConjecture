import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryRadialPositive
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverJacobian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private theorem conjugate_positive_of_transverse_positive
    (g : RiemannianMetric 2 Plane) (J : Plane → Plane →L[ℝ] ℝ) (x v w : Plane)
    (htrans : 0 < J x v) (htan : J x w = 0)
    (hdet : 0 < v 0 * w 1 - v 1 * w 0) :
    0 < scalarConjugateFormOfDifferential g J x w := by
  let Z := (g.euclideanCoefficients x).inverse (J x)
  let rho := g.pullbackVolumeDensity id x
  have hinv : (g.euclideanCoefficients x).IsInvertible := by
    convert! g.inner_isInvertible x
  have hdual : g.inner x Z Z = J x Z := by
    exact congrArg (fun A : Plane →L[ℝ] ℝ => A Z) (hinv.self_apply_inverse (J x))
  have hZne : Z ≠ 0 := by
    intro hz
    have h := hinv.self_apply_inverse (J x)
    change g.euclideanCoefficients x Z = J x at h
    rw [hz, map_zero] at h
    have hv := congrArg (fun A : Plane →L[ℝ] ℝ => A v) h
    simp only [zero_apply] at hv
    exact htrans.ne' hv.symm
  have hE : 0 < J x Z := by
    rw [← hdual]
    exact g.pos x Z hZne
  have hrho : 0 < rho := (g.contDiffAt_pullbackVolumeDensity (f := id)
    contMDiffAt_id (by simpa using Function.injective_id)).2
  have hwedge :
      J x v * scalarConjugateFormOfDifferential g J x w -
        J x w * scalarConjugateFormOfDifferential g J x v =
      (v 0 * w 1 - v 1 * w 0) * rho * J x Z := by
    rw [M60.plane_form_apply (J x) v, M60.plane_form_apply (J x) w,
      M60.plane_form_apply (J x) Z]
    simp only [scalarConjugateFormOfDifferential, M60.rotatedFlux,
      add_apply, smul_apply, smul_eq_mul, EuclideanSpace.coe_proj]
    change _ = (v 0 * w 1 - v 1 * w 0) * rho *
      (J x (EuclideanSpace.basisFun (Fin 2) ℝ 0) * Z 0 +
        J x (EuclideanSpace.basisFun (Fin 2) ℝ 1) * Z 1)
    dsimp only [Z, rho]
    ring
  rw [htan, zero_mul, sub_zero] at hwedge
  have hproduct : 0 < J x v * scalarConjugateFormOfDifferential g J x w := by
    rw [hwedge]
    exact mul_pos (mul_pos hdet hrho) hE
  exact (mul_pos_iff_of_pos_left htrans).mp hproduct

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem scalarCoverForm_boundary_angular_pos
    {H : Plane → ℝ} {J : Plane → Plane →L[ℝ] ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hJc : ContinuousOn J (closure scalarAnnulus))
    (hJeq : EqOn J (fderiv ℝ H) scalarAnnulus)
    {r : ℝ} (hr : r = 1 ∨ r = 2) (t : ℝ) :
    0 < scalarCoverFormOfDifferential g J (r, t) (0, 1) := by
  have hrad := scalarCoverPotential_boundary_radial_pos D hHc hHs hlap hinner houter
    hJc hJeq hr t
  have htan := scalarCoverPotential_boundary_angular_zero hHc hHs hinner houter
    hJc hJeq hr t
  apply conjugate_positive_of_transverse_positive g J (scalarCoverMap (r, t))
    (fderiv ℝ scalarCoverMap (r, t) (1, 0))
    (fderiv ℝ scalarCoverMap (r, t) (0, 1)) hrad htan
  rw [scalarCoverMap_column_determinant]
  have hrpos : 0 < r := by rcases hr with rfl | rfl <;> norm_num
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) hrpos

end PoincareConjecture.M64Uniformization
