import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CappedCylinder.Belt
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.RadialBody

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

def markedLensRadius (v : E3) (edge width : Real) (p : S2) : Real :=
  boundedCylinderRadius v p *
    (1 - Real.smoothTransition
      ((edge - inner Real v (boundedCylinderRadius v p • (p : E3))) / width) / 2)

theorem markedLensRadius_pos (v : E3) (edge width : Real) (p : S2) :
    0 < markedLensRadius v edge width p := by
  apply mul_pos (boundedCylinderRadius_pos v p)
  have := Real.smoothTransition.le_one
    ((edge - inner Real v (boundedCylinderRadius v p • (p : E3))) / width)
  linarith

theorem contMDiff_markedLensRadius (v : E3) (edge width : Real) :
    ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (markedLensRadius v edge width) := by
  have hgraph : ContMDiff (𝓡 2) (𝓡 3) ∞
      (fun p : S2 => boundedCylinderRadius v p • (p : E3)) :=
    (contMDiff_boundedCylinderRadius v).smul contMDiff_coe_sphere
  have hheight := (innerSL Real v).contMDiff.comp hgraph
  exact (contMDiff_boundedCylinderRadius v).mul
    (contMDiff_const.sub ((Real.smoothTransition.contDiff.contMDiff.comp
      ((contMDiff_const.sub hheight).div_const width)).div_const 2))

theorem markedLensRadius_eq_of_height_ge (v : E3) (edge : Real)
    {width : Real} (hw : 0 < width) (p : S2)
    (hp : edge ≤ inner Real v (boundedCylinderRadius v p • (p : E3))) :
    markedLensRadius v edge width p = boundedCylinderRadius v p := by
  simp [markedLensRadius, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) hw.le)]

theorem norm_markedLens_projection_lt_of_height_lt (v : E3) (hv : ‖v‖ = 1)
    (edge : Real) {width : Real} (hw : 0 < width) (p : S2)
    (hp : inner Real v (boundedCylinderRadius v p • (p : E3)) < edge) :
    ‖(Hemisphere.Plane v).orthogonalProjectionOnto
      (markedLensRadius v edge width p • (p : E3))‖ < 1 := by
  let a := Real.smoothTransition
    ((edge - inner Real v (boundedCylinderRadius v p • (p : E3))) / width)
  have ha0 : 0 < a := Real.smoothTransition.pos_of_pos (div_pos (sub_pos.mpr hp) hw)
  have ha1 : a ≤ 1 := Real.smoothTransition.le_one _
  have hfactor : 0 < 1 - a / 2 := by linarith
  have heq : markedLensRadius v edge width p • (p : E3) =
      (1 - a / 2) • (boundedCylinderRadius v p • (p : E3)) := by
    rw [smul_smul]
    congr 1
    exact mul_comm _ _
  rw [heq, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hfactor]
  have hproj := norm_boundedCylinder_projection_le v hv p
  nlinarith [norm_nonneg ((Hemisphere.Plane v).orthogonalProjectionOnto
    (boundedCylinderRadius v p • (p : E3)))]

theorem markedLens_bounds (v : E3) (hv : ‖v‖ = 1) (edge width : Real) (p : S2) :
    ‖(Hemisphere.Plane v).orthogonalProjectionOnto
      (markedLensRadius v edge width p • (p : E3))‖ ≤ 1 ∧
      |inner Real v (markedLensRadius v edge width p • (p : E3))| ≤ 2 := by
  let a := Real.smoothTransition
    ((edge - inner Real v (boundedCylinderRadius v p • (p : E3))) / width)
  have ha0 : 0 ≤ a := Real.smoothTransition.nonneg _
  have ha1 : a ≤ 1 := Real.smoothTransition.le_one _
  have hfactor : 0 < 1 - a / 2 := by linarith
  have heq : markedLensRadius v edge width p • (p : E3) =
      (1 - a / 2) • (boundedCylinderRadius v p • (p : E3)) := by
    rw [smul_smul]
    congr 1
    exact mul_comm _ _
  rw [heq, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hfactor,
    inner_smul_right, abs_mul, abs_of_pos hfactor]
  constructor
  · have := norm_boundedCylinder_projection_le v hv p
    nlinarith [norm_nonneg ((Hemisphere.Plane v).orthogonalProjectionOnto
      (boundedCylinderRadius v p • (p : E3)))]
  · have := abs_boundedCylinder_height_le v hv p
    nlinarith [abs_nonneg (inner Real v (boundedCylinderRadius v p • (p : E3)))]

theorem exists_ambient_marked_lens (v : E3) (hv : ‖v‖ = 1) (edge : Real)
    {width : Real} (hw : 0 < width) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ p : S2, F p = markedLensRadius v edge width p • (p : E3)) ∧
      (F '' sphere (0 : E3) 1) ∩
          ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
            {p : S2 | edge ≤ inner Real v (boundedCylinderRadius v p • (p : E3))}) =
        ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
          {p : S2 | edge ≤ inner Real v (boundedCylinderRadius v p • (p : E3))}) ∧
      (∀ y ∈ (F '' sphere (0 : E3) 1) \
          ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
            {p : S2 | edge ≤ inner Real v (boundedCylinderRadius v p • (p : E3))}),
        ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ < 1) ∧
      (∀ y ∈ F '' sphere (0 : E3) 1,
        ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ≤ 1 ∧
        |inner Real v y| ≤ 2) ∧
      F '' closedBall (0 : E3) 1 =
        Poincare.Topology.radialClosedBody (markedLensRadius v edge width) := by
  obtain ⟨F, _, hF⟩ := exists_radial_sphere_extension
    (markedLensRadius v edge width) (contMDiff_markedLensRadius v edge width)
    (markedLensRadius_pos v edge width)
  have hboundary : F '' sphere (0 : E3) 1 =
      range (fun p : S2 => markedLensRadius v edge width p • (p : E3)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hF ⟨x, hx⟩).symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p, p.property, hF p⟩
  refine ⟨F, hF, inter_eq_right.mpr ?_, ?_, ?_, ?_⟩
  · rintro y ⟨p, hp, rfl⟩
    refine ⟨p, p.property, ?_⟩
    rw [hF, markedLensRadius_eq_of_height_ge v edge hw p hp]
  · rintro y ⟨⟨x, hx, rfl⟩, hnot⟩
    let p : S2 := ⟨x, hx⟩
    have hp : inner Real v (boundedCylinderRadius v p • (p : E3)) < edge := by
      by_contra hn
      have hge := le_of_not_gt hn
      apply hnot
      refine ⟨p, hge, ?_⟩
      rw [hF p, markedLensRadius_eq_of_height_ge v edge hw p hge]
    rw [hF p]
    exact norm_markedLens_projection_lt_of_height_lt v hv edge hw p hp
  · rintro y ⟨x, hx, rfl⟩
    rw [hF ⟨x, hx⟩]
    exact markedLens_bounds v hv edge width ⟨x, hx⟩
  · exact (image_balls_eq_radialBodies F.toHomeomorph
      (markedLensRadius v edge width) (contMDiff_markedLensRadius v edge width).continuous
      (markedLensRadius_pos v edge width) hboundary).1

end Poincare.Manifold.Schoenflies.Reverse
