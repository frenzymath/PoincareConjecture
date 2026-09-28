import PoincareConjecture.Proofs.M34.Standard.CapNeckImage









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M47

local notation "E₃" => EuclideanSpace ℝ (Fin 3)



theorem terminalCurvature_exists_centered_double_neck
    {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
    [ChartedSpace E₃ M] [ChartedSpace E₃ X]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
    {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}
    (N : EpsilonNeck g) (D : LeviCivitaData h)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞)
    (hsmall : 2 * N.epsilon < 1 / 2)
    (hsource : N.region (-(2 * N.epsilon)⁻¹) (2 * N.epsilon)⁻¹ ⊆ phi.source)
    (hR : 0 < D.scalarCurvature (phi N.center))
    (hclose : RoundCylinderClose (2 * N.epsilon) 0 (fun z u u' =>
      D.scalarCurvature (phi N.center) * roundCylinderPullback h (phi ∘ N.coordinate_map) z u u')) :
    ∃ E : EpsilonNeck h,
      E.epsilon = 2 * N.epsilon ∧ E.center = phi N.center ∧ E.connection = D ∧
      E.carrier = phi '' N.region (-(2 * N.epsilon)⁻¹) (2 * N.epsilon)⁻¹ ∧
      E.coordinate_map = phi ∘ N.coordinate_map := by
  classical
  have hcenter := N.center_on_central_sphere
  rw [N.central_sphere_eq] at hcenter
  obtain ⟨⟨q, z⟩, hz, hq⟩ := hcenter
  have hz0 : z = 0 := hz.2
  subst z
  let r := D.scalarCurvature (phi N.center) ^ (-1 / 2 : ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos hR _
  have hscale : r⁻¹ ^ 2 = D.scalarCurvature (phi N.center) := by
    dsimp only [r]
    rw [inv_pow, ← Real.rpow_mul_natCast hR.le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
  have hepsilon : 0 < 2 * N.epsilon := mul_pos (by norm_num) N.epsilon_pos
  have hinv : (2 * N.epsilon)⁻¹ ≤ N.epsilon⁻¹ :=
    inv_anti₀ N.epsilon_pos (by linarith [N.epsilon_pos])
  have hdom : Ioo (-(2 * N.epsilon)⁻¹ + 0) ((2 * N.epsilon)⁻¹ + 0) ⊆
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    simp only [add_zero]
    exact fun _ hz => ⟨(neg_le_neg hinv).trans_lt hz.1, hz.2.trans_le hinv⟩
  have hsource' : N.region (-(2 * N.epsilon)⁻¹ + 0) ((2 * N.epsilon)⁻¹ + 0) ⊆
      phi.source := by simpa only [add_zero] using hsource
  have hR' : 0 < D.scalarCurvature (phi (N.coordinate_map (q, 0))) := by
    simpa only [hq] using hR
  have hr' : r = D.scalarCurvature (phi (N.coordinate_map (q, 0))) ^ (-1 / 2 : ℝ) := by
    rw [hq]
  have hclose' : RoundCylinderClose (2 * N.epsilon) 0 (fun z u u' => r⁻¹ ^ 2 *
      roundCylinderPullback h (fun z => phi (N.coordinate_map (z.1, z.2 + 0))) z u u') := by
    simpa only [add_zero, hscale, Function.comp_def, Prod.mk.eta] using hclose
  let E := N.imageShift phi.toOpenPartialHomeomorph phi.contMDiffOn_toFun
    phi.contMDiffOn_invFun hepsilon hsmall hdom hsource' D q hr hR' hr' hclose'
  refine ⟨E, rfl, congrArg phi hq, rfl, ?_, ?_⟩
  · change phi '' N.region (-(2 * N.epsilon)⁻¹ + 0) ((2 * N.epsilon)⁻¹ + 0) = _
    simp only [add_zero]
  · funext z
    change phi (N.coordinate_map (z.1, z.2 + 0)) = phi (N.coordinate_map z)
    simp only [add_zero]

end PoincareConjecture.M47
