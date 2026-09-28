import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Hemisphere
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Local
import Mathlib.Analysis.SpecialFunctions.Log.Deriv









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)


def unitBallBoundaryHalfSpace (v : E3) : Opens E3 :=
  ⟨{y | 0 < inner Real v y}, isOpen_lt continuous_const (innerSL Real v).continuous⟩

private theorem unitBallBoundaryHalfSpace_ne_zero {v : E3}
    (y : unitBallBoundaryHalfSpace v) : (y : E3) ≠ 0 := by
  intro h
  have hy := y.property
  change 0 < inner Real v (y : E3) at hy
  simp only [h, inner_zero_right, lt_self_iff_false] at hy



def unitBallBoundaryParametrization {v : E3} (hv : ‖v‖ = 1) :
    Diffeomorph 𝓘(Real, Hemisphere.Plane v × Real) (𝓡 3)
      (Hemisphere.Plane v × Real) (unitBallBoundaryHalfSpace v) ∞ := by
  let f : Hemisphere.Plane v × Real → unitBallBoundaryHalfSpace v := fun z =>
    ⟨Real.exp z.2 • (Hemisphere.toSphere hv z.1 : E3), by
      change 0 < inner Real v (Real.exp z.2 • (Hemisphere.toSphere hv z.1 : E3))
      rw [inner_smul_right]
      exact mul_pos (Real.exp_pos _) (Hemisphere.toSphere_mem_hemisphere hv _)⟩
  let g : unitBallBoundaryHalfSpace v → Hemisphere.Plane v × Real := fun y =>
    ((inner Real v (y : E3))⁻¹ • (Hemisphere.Plane v).orthogonalProjectionOnto (y : E3),
      Real.log ‖(y : E3)‖)
  have hfNorm (z : Hemisphere.Plane v × Real) : ‖(f z : E3)‖ = Real.exp z.2 := by
    simp [f, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hleft : Function.LeftInverse g f := by
    rintro ⟨x, t⟩
    apply Prod.ext
    · change (inner Real v (Real.exp t • (Hemisphere.toSphere hv x : E3)))⁻¹ •
        (Hemisphere.Plane v).orthogonalProjectionOnto
          (Real.exp t • (Hemisphere.toSphere hv x : E3)) = x
      rw [inner_smul_right, map_smul, mul_inv_rev, smul_smul]
      have hc : (inner Real v (Hemisphere.toSphere hv x : E3))⁻¹ *
          (Real.exp t)⁻¹ * Real.exp t = (inner Real v (Hemisphere.toSphere hv x : E3))⁻¹ := by
        rw [mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero t), mul_one]
      rw [hc]
      exact Hemisphere.fromSphere_toSphere hv x
    · change Real.log ‖(f (x, t) : E3)‖ = t
      rw [hfNorm, Real.log_exp]
  have hright : Function.RightInverse g f := by
    intro y
    have hy : 0 < inner Real v (y : E3) := y.property
    have hyn : 0 < ‖(y : E3)‖ := norm_pos_iff.mpr (unitBallBoundaryHalfSpace_ne_zero y)
    have hsplit : (y : E3) = inner Real v (y : E3) • v +
        ((Hemisphere.Plane v).orthogonalProjectionOnto (y : E3) : E3) := by
      nth_rw 1 [← ((Real ∙ v).starProjection_add_starProjection_orthogonal (y : E3))]
      rw [Submodule.starProjection_unit_singleton Real hv (y : E3)]
      rfl
    have heq : (((g y).1 : Hemisphere.Plane v) : E3) + v =
        (inner Real v (y : E3))⁻¹ • (y : E3) := by
      nth_rw 2 [hsplit]
      simp only [g, Submodule.coe_smul, smul_add, smul_smul,
        inv_mul_cancel₀ hy.ne', one_smul]
      exact add_comm _ _
    apply Subtype.ext
    change Real.exp (Real.log ‖(y : E3)‖) •
      (‖(((g y).1 : Hemisphere.Plane v) : E3) + v‖⁻¹ •
        ((((g y).1 : Hemisphere.Plane v) : E3) + v)) = (y : E3)
    rw [Real.exp_log hyn, heq, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hy, mul_inv_rev, inv_inv, smul_smul, smul_smul]
    have hc : ‖(y : E3)‖ * (‖(y : E3)‖⁻¹ * inner Real v (y : E3)) *
        (inner Real v (y : E3))⁻¹ = 1 := by field_simp
    rw [hc, one_smul]
  have hf : ContMDiff 𝓘(Real, Hemisphere.Plane v × Real) (𝓡 3) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff (unitBallBoundaryHalfSpace v) f).mp
    exact ((Real.contDiff_exp.comp contDiff_snd).smul
      ((Hemisphere.contDiff_toSphere_coe hv).comp contDiff_fst)).contMDiff
  have hg : ContMDiff (𝓡 3) 𝓘(Real, Hemisphere.Plane v × Real) ∞ g := by
    have hi : ContMDiff (𝓡 3) 𝓘(Real, Real) ∞
        (fun y : unitBallBoundaryHalfSpace v => inner Real v (y : E3)) :=
      (innerSL Real v).contMDiff.comp contMDiff_subtype_val
    have hp : ContMDiff (𝓡 3) 𝓘(Real, Hemisphere.Plane v) ∞
        (fun y : unitBallBoundaryHalfSpace v =>
          (Hemisphere.Plane v).orthogonalProjectionOnto (y : E3)) :=
      (Hemisphere.Plane v).orthogonalProjectionOnto.contMDiff.comp contMDiff_subtype_val
    have hn : ContMDiff (𝓡 3) 𝓘(Real, Real) ∞
        (fun y : unitBallBoundaryHalfSpace v => ‖(y : E3)‖) := by
      intro y
      exact (contDiffAt_norm Real (unitBallBoundaryHalfSpace_ne_zero y)).contMDiffAt.comp
        y (contMDiff_subtype_val y)
    have hl : ContMDiff (𝓡 3) 𝓘(Real, Real) ∞
        (fun y : unitBallBoundaryHalfSpace v => Real.log ‖(y : E3)‖) := by
      intro y
      exact (Real.contDiffAt_log.mpr
        (norm_ne_zero_iff.mpr (unitBallBoundaryHalfSpace_ne_zero y))).contMDiffAt.comp y (hn y)
    have h := ((hi.inv₀ (fun y => ne_of_gt y.property)).smul hp).prodMk hl
    rw [← modelWithCornersSelf_prod] at h
    rw [chartedSpaceSelf_prod] at h
    exact h
  exact ⟨⟨f, g, hleft, hright⟩, hf, hg⟩


def unitBallBoundaryChart {v : E3} (hv : ‖v‖ = 1) :
    Diffeomorph (𝓡 3) 𝓘(Real, Hemisphere.Plane v × Real)
      (unitBallBoundaryHalfSpace v) (Hemisphere.Plane v × Real) ∞ :=
  (unitBallBoundaryParametrization hv).symm

@[simp] theorem unitBallBoundaryChart_symm_apply {v : E3} (hv : ‖v‖ = 1)
    (z : Hemisphere.Plane v × Real) :
    ((unitBallBoundaryChart hv).symm z : E3) =
      Real.exp z.2 • (Hemisphere.toSphere hv z.1 : E3) := rfl

@[simp] theorem unitBallBoundaryChart_zero {v : E3} (hv : ‖v‖ = 1)
    (x : Hemisphere.Plane v) :
    ((unitBallBoundaryChart hv).symm (x, 0) : E3) = Hemisphere.toSphere hv x := by
  simp

@[simp] theorem norm_unitBallBoundaryChart_symm {v : E3} (hv : ‖v‖ = 1)
    (z : Hemisphere.Plane v × Real) :
    ‖((unitBallBoundaryChart hv).symm z : E3)‖ = Real.exp z.2 := by
  simp [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]


theorem unitBallBoundaryChart_closedBall {v : E3} (hv : ‖v‖ = 1) :
    closedBall (0 : E3) 1 ∩ unitBallBoundaryHalfSpace v =
      (fun z : Hemisphere.Plane v × Real => ((unitBallBoundaryChart hv).symm z : E3)) ''
        {z | z.2 ≤ 0} := by
  ext y
  constructor
  · rintro ⟨hy, hyU⟩
    let q : unitBallBoundaryHalfSpace v := ⟨y, hyU⟩
    refine ⟨unitBallBoundaryChart hv q, ?_, ?_⟩
    · have hn : ‖y‖ ≤ 1 := by simpa using hy
      have he : Real.exp ((unitBallBoundaryChart hv q).2) = ‖y‖ := by
        rw [← norm_unitBallBoundaryChart_symm hv, Diffeomorph.symm_apply_apply]
      exact Real.exp_le_one_iff.mp (he ▸ hn)
    · exact congrArg Subtype.val ((unitBallBoundaryChart hv).symm_apply_apply q)
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, ((unitBallBoundaryChart hv).symm z).property⟩
    simpa only [mem_closedBall, dist_zero_right, norm_unitBallBoundaryChart_symm] using
      Real.exp_le_one_iff.mpr hz


theorem unitBallBoundaryChart_ball {v : E3} (hv : ‖v‖ = 1) :
    ball (0 : E3) 1 ∩ unitBallBoundaryHalfSpace v =
      (fun z : Hemisphere.Plane v × Real => ((unitBallBoundaryChart hv).symm z : E3)) ''
        {z | z.2 < 0} := by
  ext y
  constructor
  · rintro ⟨hy, hyU⟩
    let q : unitBallBoundaryHalfSpace v := ⟨y, hyU⟩
    refine ⟨unitBallBoundaryChart hv q, ?_, ?_⟩
    · have hn : ‖y‖ < 1 := by simpa using hy
      have he : Real.exp ((unitBallBoundaryChart hv q).2) = ‖y‖ := by
        rw [← norm_unitBallBoundaryChart_symm hv, Diffeomorph.symm_apply_apply]
      exact Real.exp_lt_one_iff.mp (he ▸ hn)
    · exact congrArg Subtype.val ((unitBallBoundaryChart hv).symm_apply_apply q)
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, ((unitBallBoundaryChart hv).symm z).property⟩
    simpa only [mem_ball, dist_zero_right, norm_unitBallBoundaryChart_symm] using
      Real.exp_lt_one_iff.mpr hz



theorem exists_unitBall_boundary_graph_push {v : E3} (hv : ‖v‖ = 1)
    (b : Hemisphere.Plane v → Real) (hb : ContDiff Real ∞ b) (hbc : HasCompactSupport b) :
    ∃ K : Set E3, IsCompact K ∧ K ⊆ unitBallBoundaryHalfSpace v ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, F y = y) ∧
        (∀ x : Hemisphere.Plane v,
          F (Hemisphere.toSphere hv x) = Real.exp (b x) • (Hemisphere.toSphere hv x : E3)) ∧
        F '' closedBall (0 : E3) 1 =
          (closedBall (0 : E3) 1 \ unitBallBoundaryHalfSpace v) ∪
            (fun z : Hemisphere.Plane v × Real =>
              Real.exp z.2 • (Hemisphere.toSphere hv z.1 : E3)) '' {z | z.2 ≤ b z.1} := by
  obtain ⟨K, hK, hKU, F, hfix, hzero, hside⟩ :=
    exists_boundary_graph_push (unitBallBoundaryHalfSpace v) (unitBallBoundaryChart hv)
      b hb hbc (unitBallBoundaryChart_closedBall hv)
  exact ⟨K, hK, hKU, F, hfix, by simpa using hzero, hside⟩

end Poincare.Manifold.Schoenflies
