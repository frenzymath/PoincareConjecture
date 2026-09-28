import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Triangle.AngularLift
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Coordinates.PeriodicCircle









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

private instance : Fact (Module.finrank ℝ ℂ = 2) := ⟨by simp⟩
private instance : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩



theorem exists_smooth_radial_graph_roundedEquilateral {ρ : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 2 / 9)
    (htail : ∀ t, δ ≤ |t| → ρ t = |t|)
    (hbound : ∀ t, |t| ≤ ρ t ∧ ρ t ≤ |t| + δ)
    (hρ : ContDiff ℝ ∞ ρ) (hder : ∀ t, |deriv ρ t| ≤ 1) :
    ∃ R : sphere (0 : ℂ) 1 → ℝ, ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ R ∧
      (∀ q, R q ∈ Icc (1 / 4 : ℝ) 1) ∧
      range (roundedVertexPath ρ equilateralVertex) =
        range (fun q : sphere (0 : ℂ) 1 => R q • (q : ℂ)) := by
  have hquarter : δ < 1 / 4 := by linarith
  have hτ : 0 < 2 * Real.pi := by positivity
  have hγ := contDiff_roundedEquilateral hδ hquarter htail hbound hρ
  have hγ0 (s : ℝ) : roundedVertexPath ρ equilateralVertex s ≠ 0 := by
    have h := (norm_roundedEquilateral_mem_Icc hquarter htail hbound s).1
    intro hz
    rw [hz, norm_zero] at h
    linarith
  obtain ⟨β, hβ, hαβ, hβα, hβper⟩ :=
    exists_smooth_inverse_roundedEquilateralAngle hδ hδsmall htail hbound hρ hder
  let H : ℝ → ℝ := fun s => ‖roundedVertexPath ρ equilateralVertex (β s)‖
  have hH : ContDiff ℝ ∞ H := (hγ.comp hβ).norm ℝ (fun s => hγ0 (β s))
  have hHper : Periodic H (2 * Real.pi) := by
    intro s
    dsimp only [H]
    rw [hβper, periodic_roundedEquilateral ρ]
  let e := LinearIsometryEquiv.refl ℝ ℂ
  let R : sphere (0 : ℂ) 1 → ℝ := periodicCircleCurve (2 * Real.pi) e H
  have hR : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ R := by
    have h := contMDiff_periodicCircleCurve_family (V := ℝ) hτ e
      (fun _ => H) (hH.comp contDiff_snd) (fun _ => hHper)
    have hj : ContMDiff (𝓡 1) (𝓘(ℝ, ℝ).prod (𝓡 1)) ∞
        (fun q : sphere (0 : ℂ) 1 => ((0 : ℝ), q)) :=
      contMDiff_const.prodMk contMDiff_id
    exact h.comp (f := fun q : sphere (0 : ℂ) 1 => ((0 : ℝ), q)) hj
  have hRparam (s : ℝ) : R (sphereCircleParameter e s) = H s := by
    simpa only [div_self hτ.ne', one_mul] using
      periodicCircleCurve_sphereCircleParameter hτ e hHper s
  have hformula (s : ℝ) : roundedVertexPath ρ equilateralVertex (β s) =
      R (sphereCircleParameter e s) • (sphereCircleParameter e s : ℂ) := by
    have h := norm_mul_exp_rotatingArgument (roundedVertexPath ρ equilateralVertex (β s))
      (2 * Real.pi / 3 * β s)
    change (‖roundedVertexPath ρ equilateralVertex (β s)‖ : ℂ) *
      (Circle.exp (roundedEquilateralAngle ρ (β s)) : ℂ) = _ at h
    rw [hαβ] at h
    rw [hRparam]
    exact h.symm
  refine ⟨R, hR, (fun q => norm_roundedEquilateral_mem_Icc hquarter htail hbound _), ?_⟩
  apply Subset.antisymm
  · rintro z ⟨t, rfl⟩
    exact ⟨sphereCircleParameter e (roundedEquilateralAngle ρ t),
      (hformula (roundedEquilateralAngle ρ t)).symm.trans (congrArg _ (hβα t))⟩
  · rintro z ⟨q, rfl⟩
    obtain ⟨s, rfl⟩ := surjective_sphereCircleParameter e q
    exact ⟨β s, hformula s⟩

end Poincare.Manifold.Schoenflies.Plane
