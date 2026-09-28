import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Coordinates.AngularCoherence
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false

open Set Metric Function Filter
open scoped Topology ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

theorem circleAngularCoordinate_add_int_period
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : ℂ ≃ₗᵢ[ℝ] E) (a : ℝ) (x : E) (m : ℤ) :
    circleAngularCoordinate e (a + (m : ℝ) * (2 * Real.pi), x) =
      circleAngularCoordinate e (a, x) + (m : ℝ) * (2 * Real.pi) := by
  have hphase : Circle.exp (-(a + (m : ℝ) * (2 * Real.pi))) = Circle.exp (-a) := by
    rw [show -(a + (m : ℝ) * (2 * Real.pi)) = -a - (m : ℝ) * (2 * Real.pi) by ring]
    exact Circle.periodic_exp.sub_int_mul_eq m
  simp only [circleAngularCoordinate, hphase]
  ring

theorem curveTubeAngle_lift_properties
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : ℂ ≃ₗᵢ[ℝ] E) (q0 : sphere (0 : E) 1)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (hx : ∀ y ∈ T.target, (T.symm y).2 ≠ 0)
    {K : Set ℝ} (γ : ℝ → ℝ → E)
    (hγ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => γ p.1 p.2))
    (hper : ∀ z, Periodic (γ z) (2 * Real.pi))
    (hdom : ∀ z ∈ K, ∀ s ∈ Icc 0 (2 * Real.pi),
      ((z, s), γ z s) ∈ curveTubeAngularDomain e q0 T)
    (hpos : ∀ z ∈ K, ∀ s ∈ Icc 0 (2 * Real.pi),
      0 < fderiv ℝ (fun y : E => curveTubeAngle e q0 T ((z, s), y))
        (γ z s) (deriv (γ z) s)) :
    let F : ℝ × ℝ → ℝ := fun p => curveTubeAngle e q0 T (p, γ p.1 p.2)
    ContDiffOn ℝ ∞ F (K ×ˢ univ) ∧
      (∀ z s, F (z, s + 2 * Real.pi) = F (z, s) + 2 * Real.pi) ∧
      ∀ z ∈ K, ∀ s, 0 < deriv (fun t => F (z, t)) s := by
  let F : ℝ × ℝ → ℝ := fun p => curveTubeAngle e q0 T (p, γ p.1 p.2)
  change ContDiffOn ℝ ∞ F (K ×ˢ univ) ∧
    (∀ z s, F (z, s + 2 * Real.pi) = F (z, s) + 2 * Real.pi) ∧
    ∀ z ∈ K, ∀ s, 0 < deriv (fun t => F (z, t)) s
  have hshift (z s : ℝ) (m : ℤ) :
      F (z, s + (m : ℝ) * (2 * Real.pi)) = F (z, s) + (m : ℝ) * (2 * Real.pi) := by
    change circleAngularCoordinate e
      (s + (m : ℝ) * (2 * Real.pi),
        (curveTubeProjection q0 T (z, γ z (s + (m : ℝ) * (2 * Real.pi))) : E)) = _
    rw [(hper z).int_mul m s]
    exact circleAngularCoordinate_add_int_period e s _ m
  have hreduce (s : ℝ) : ∃ m : ℤ, s - (m : ℝ) * (2 * Real.pi) ∈ Icc 0 (2 * Real.pi) := by
    let m : ℤ := ⌊s / (2 * Real.pi)⌋
    have hτ : 0 < 2 * Real.pi := by positivity
    have hlo : (m : ℝ) * (2 * Real.pi) ≤ s := (le_div_iff₀ hτ).mp (Int.floor_le _)
    have hhi : s < ((m : ℝ) + 1) * (2 * Real.pi) :=
      (div_lt_iff₀ hτ).mp (Int.lt_floor_add_one _)
    exact ⟨m, ⟨by linarith, by nlinarith⟩⟩
  have hfull (z : ℝ) (hz : z ∈ K) (s : ℝ) :
      ((z, s), γ z s) ∈ curveTubeAngularDomain e q0 T := by
    obtain ⟨m, hm⟩ := hreduce s
    have hphase : Circle.exp (-(s - (m : ℝ) * (2 * Real.pi))) = Circle.exp (-s) := by
      rw [show -(s - (m : ℝ) * (2 * Real.pi)) = -s + (m : ℝ) * (2 * Real.pi) by ring]
      exact Circle.periodic_exp.int_mul m (-s)
    have h := hdom z hz (s - (m : ℝ) * (2 * Real.pi)) hm
    simp only [curveTubeAngularDomain, mem_ofPred_eq,
      (hper z).sub_int_mul_eq m, hphase] at h
    exact h
  obtain ⟨hV, hA⟩ := curveTubeAngle_regular e q0 T hInv hx
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have hinput : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p, γ p.1 p.2)) :=
      contDiff_id.prodMk hγ
    exact ((hA.contDiffAt (hV.mem_nhds (hfull p.1 hp.1 p.2))).comp p
      hinput.contDiffAt).contDiffWithinAt
  · intro z s
    simpa only [Int.cast_one, one_mul] using hshift z s 1
  · intro z hz s
    obtain ⟨m, hm⟩ := hreduce s
    let r := s - (m : ℝ) * (2 * Real.pi)
    let D := fderiv ℝ (fun y : E => curveTubeAngle e q0 T ((z, r), y))
      (γ z r) (deriv (γ z) r)
    have hγz : ContDiff ℝ ∞ (γ z) := hγ.comp (contDiff_const.prodMk contDiff_id)
    have hr : HasDerivAt (fun t => F (z, t)) D r :=
      hasDerivAt_curveTubeAngle_movingCenter e q0 T hInv hx (γ z) z r
        (hγz.differentiable (by simp) r) (hdom z hz r hm)
    have htranslated : HasDerivAt
        (fun t => F (z, t - (m : ℝ) * (2 * Real.pi)) + (m : ℝ) * (2 * Real.pi)) D s := by
      convert! (hr.scomp s ((hasDerivAt_id s).sub_const ((m : ℝ) * (2 * Real.pi)))).add_const
        ((m : ℝ) * (2 * Real.pi)) using 1
      simp only [one_smul]
    have heq (t : ℝ) : F (z, t) =
        F (z, t - (m : ℝ) * (2 * Real.pi)) + (m : ℝ) * (2 * Real.pi) := by
      simpa only [sub_add_cancel] using hshift z (t - (m : ℝ) * (2 * Real.pi)) m
    have hd : HasDerivAt (fun t => F (z, t)) D s :=
      htranslated.congr_of_eventuallyEq (Eventually.of_forall heq)
    rw [hd.deriv]
    exact hpos z hz r hm

end Poincare.Manifold.Schoenflies.Plane
