import PoincareConjecture.Proofs.M25.Topology3D.Space3.NorthSphereChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryMatchingProfile
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CircleRadialChart










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



noncomputable def surgeryNorthChart
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere) :
    OpenPartialHomeomorph UnitTwoSphere UnitTwoSphere :=
  (northSphereChart.transHomeomorph R.toHomeomorph).trans e


@[simp] theorem surgeryNorthChart_apply
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere) (q : UnitTwoSphere) :
    surgeryNorthChart R e q = e (R (northSphereCoordinate q)) := rfl



theorem surgeryNorthChart_source
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere) :
    (surgeryNorthChart R e).source =
      {q | q ∈ northSphereDomain ∧ R (northSphereCoordinate q) ∈ e.source} := rfl


theorem surgeryNorthChart_contMDiffOn
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (surgeryNorthChart R e)
      (surgeryNorthChart R e).source :=
  he.comp (R.contMDiff_toFun.comp_contMDiffOn
    (northSphereChart_contMDiffOn.mono inter_subset_left)) (fun _ hq => hq.2)



theorem surgeryNorthChart_symm_contMDiffOn
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (hi : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target) :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ (surgeryNorthChart R e).symm
      (surgeryNorthChart R e).target :=
  northSphereChart_symm_contMDiff.comp_contMDiffOn
    (R.contMDiff_invFun.comp_contMDiffOn (hi.mono inter_subset_left))




theorem surgeryNorthChart_contains_hemisphere
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : closedBall 0 1 ⊆ e.source) {c : ℝ} (hc : c ≤ 1)
    (hR : R '' closedBall 0 1 = closedBall 0 c) :
    {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} ⊆
      (surgeryNorthChart R e).source := by
  intro q hq
  refine ⟨northern_hemisphere_subset_chart_source hq, he ?_⟩
  apply closedBall_subset_closedBall hc
  rw [← hR]
  refine ⟨northSphereCoordinate q, ?_, rfl⟩
  rw [← northSphereChart_image_northern_hemisphere]
  exact ⟨q, hq, rfl⟩



theorem surgeryNorthChart_image_hemisphere
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere) {c : ℝ}
    (hR : R '' closedBall 0 1 = closedBall 0 c) :
    surgeryNorthChart R e '' {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} =
      e '' closedBall 0 c := by
  change (e ∘ R ∘ northSphereChart) '' _ = _
  rw [image_comp, image_comp, northSphereChart_image_northern_hemisphere, hR]



theorem surgeryNorthChart_mfderiv_injective
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target)
    {q : UnitTwoSphere} (hq : q ∈ (surgeryNorthChart R e).source) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 2) (surgeryNorthChart R e) q) := by
  have hm : (surgeryNorthChart R e).MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨(surgeryNorthChart_contMDiffOn R e he).mdifferentiableOn (by simp),
      (surgeryNorthChart_symm_contMDiffOn R e hi).mdifferentiableOn (by simp)⟩
  exact hm.mfderiv_injective hq



theorem northSphereCoordinate_height {q : UnitTwoSphere}
    (hq : q ∈ northSphereDomain) :
    (heightCoordinates (q : E3)).2 =
      (1 - ‖northSphereCoordinate q‖ ^ 2) / (1 + ‖northSphereCoordinate q‖ ^ 2) := by
  have h := congrArg (fun p : UnitTwoSphere => (heightCoordinates (p : E3)).2)
    (northSpherePoint_coordinate hq)
  rw [northSpherePoint_coordinates] at h
  exact h.symm



theorem surgeryMatchingRadius_north {q : UnitTwoSphere}
    (hq : q ∈ northSphereDomain) (c alpha : ℝ) :
    surgeryMatchingRadius c alpha ‖northSphereCoordinate q‖ =
      c - alpha * (heightCoordinates (q : E3)).2 := by
  rw [northSphereCoordinate_height hq, surgeryMatchingRadius]
  ring



theorem surgeryNorthChart_collar_formula
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (Q : UnitCircle × ℝ → UnitTwoSphere) (c alpha k sigma : ℝ)
    {q : UnitTwoSphere} (hq : q ∈ northSphereDomain)
    (hw : northSphereCoordinate q ≠ 0)
    (hpos : 0 < surgeryMatchingRadius c alpha ‖northSphereCoordinate q‖)
    (hR : R (northSphereCoordinate q) =
      surgeryMatchingRadius c alpha ‖northSphereCoordinate q‖ •
        NormedSpace.normalize (northSphereCoordinate q))
    (he : e (R (northSphereCoordinate q)) =
      Q (circleDirection (R (northSphereCoordinate q)),
        sigma * (k * (1 - ‖R (northSphereCoordinate q)‖)))) :
    surgeryNorthChart R e q =
      Q (circleDirection (northSphereCoordinate q),
        sigma * (k * (1 - c) + k * alpha * (heightCoordinates (q : E3)).2)) := by
  rw [surgeryNorthChart_apply, he, hR, ← circleDirection_coe hw,
    circleDirection_smul _ hpos, norm_smul, Real.norm_eq_abs, abs_of_pos hpos,
    norm_eq_of_mem_sphere, mul_one, surgeryMatchingRadius_north hq]
  congr 2
  ring

end PoincareConjecture.M25.Topology3D
