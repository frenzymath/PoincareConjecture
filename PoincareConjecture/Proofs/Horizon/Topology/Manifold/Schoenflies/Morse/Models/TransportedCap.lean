import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CylindricalCap
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.PlaneLift



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)




theorem exists_cylindrical_cap_over_disk_with_range
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) :
    ∃ g : Hemisphere.Plane v -> E3,
      ContDiff Real ∞ g ∧ Function.Injective g ∧
      (∀ x, Function.Injective (fderiv Real g x)) ∧
      (∀ x, ‖x‖ = 1 -> g x = c • v + (A x : E3)) ∧
      (∀ x, ‖x‖ < 1 -> 0 < (inner Real v (g x) - c) / s) ∧
      (∀ q : Hemisphere.Plane v, ‖q‖ = 1 -> ∀ ρ : Real,
        3 / 4 ≤ ρ -> ρ ≤ 4 / 3 ->
        g (ρ • q) = (c + s * ((1 - ρ ^ 2) / (2 * ρ))) • v + (A q : E3)) ∧
      (∀ x, (Hemisphere.Plane v).orthogonalProjectionOnto (g x) ∈
        A '' closedBall 0 1 ∧ |inner Real v (g x) - c| ≤ 2 * |s|) ∧
      g '' closedBall (0 : Hemisphere.Plane v) 1 =
        Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv c s hs A ''
          ((fun p : sphere (0 : E3) 1 => boundedCylinderRadius v p • (p : E3)) ''
            {p : sphere (0 : E3) 1 | 0 ≤ inner Real v (p : E3)}) := by
  obtain ⟨k, hk, hki, hkder, hkb, hkh, hkc, hkbound, hkrange⟩ :=
    exists_northern_cylindrical_cap_with_range v hv
  let F := Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv c s hs A
  let g : Hemisphere.Plane v -> E3 := F ∘ k
  have hheight (x : Hemisphere.Plane v) : inner Real v (g x) =
      c + s * inner Real v (k x) :=
    Poincare.Geometry.Euclidean.inner_liftPlaneDiffeomorph hv c s hs A (k x)
  have hproject (x : Hemisphere.Plane v) :
      (Hemisphere.Plane v).orthogonalProjectionOnto (g x) =
        A ((Hemisphere.Plane v).orthogonalProjectionOnto (k x)) :=
    Poincare.Geometry.Euclidean.projection_liftPlaneDiffeomorph hv c s hs A (k x)
  refine ⟨g, F.contMDiff.contDiff.comp hk, F.injective.comp hki, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hFd : Function.Injective (fderiv Real F (k x)) := by
      have h := (F.mfderivToContinuousLinearEquiv (by simp) (k x)).injective
      change Function.Injective (mfderiv (𝓡 3) (𝓡 3) F (k x)) at h
      simpa only [mfderiv_eq_fderiv, TangentSpace] using h
    rw [show g = F ∘ k from rfl, fderiv_comp x
      (F.contMDiff.contDiff.differentiable (by simp) (k x))
      (hk.differentiable (by simp) x)]
    exact hFd.comp (hkder x)
  · intro x hx
    change F (k x) = _
    rw [hkb x hx, Poincare.Geometry.Euclidean.liftPlaneDiffeomorph_apply]
    simp [Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property]
  · intro x hx
    rw [hheight]
    simpa only [add_sub_cancel_left, mul_div_cancel_left₀ _ hs] using hkh x hx
  · intro q hq ρ hρ hρ1
    change F (k (ρ • q)) = _
    rw [hkc q hq ρ hρ hρ1, Poincare.Geometry.Euclidean.liftPlaneDiffeomorph_apply]
    simp [inner_add_right, inner_smul_right, hv,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp q.property]
  · intro x
    constructor
    · rw [hproject]
      exact mem_image_of_mem A (mem_closedBall_zero_iff.mpr (hkbound x).1)
    · rw [hheight, add_sub_cancel_left, abs_mul]
      calc
        |s| * |inner Real v (k x)| ≤ |s| * 2 :=
          mul_le_mul_of_nonneg_left (hkbound x).2 (abs_nonneg s)
        _ = 2 * |s| := mul_comm _ _
  · change (F ∘ k) '' closedBall (0 : Hemisphere.Plane v) 1 = _
    rw [image_comp, hkrange]


theorem exists_cylindrical_cap_over_disk
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) :
    ∃ g : Hemisphere.Plane v -> E3,
      ContDiff Real ∞ g ∧ Function.Injective g ∧
      (∀ x, Function.Injective (fderiv Real g x)) ∧
      (∀ x, ‖x‖ = 1 -> g x = c • v + (A x : E3)) ∧
      (∀ x, ‖x‖ < 1 -> 0 < (inner Real v (g x) - c) / s) ∧
      (∀ q : Hemisphere.Plane v, ‖q‖ = 1 -> ∀ ρ : Real,
        3 / 4 ≤ ρ -> ρ ≤ 4 / 3 ->
        g (ρ • q) = (c + s * ((1 - ρ ^ 2) / (2 * ρ))) • v + (A q : E3)) ∧
      (∀ x, (Hemisphere.Plane v).orthogonalProjectionOnto (g x) ∈
        A '' closedBall 0 1 ∧ |inner Real v (g x) - c| ≤ 2 * |s|) := by
  obtain ⟨g, hg, hi, hd, hb, hh, hc, hbound, _⟩ :=
    exists_cylindrical_cap_over_disk_with_range hv c s hs A
  exact ⟨g, hg, hi, hd, hb, hh, hc, hbound⟩

end Poincare.Manifold.Schoenflies
