import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Coordinates.AngularCoordinate
import Mathlib.Algebra.Order.Floor.Ring










set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

section Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*}



noncomputable def periodicCircleCurve (T : ℝ) (e : ℂ ≃ₗᵢ[ℝ] E)
    (γ : ℝ → F) (q : sphere (0 : E) 1) : F :=
  γ ((T / (2 * Real.pi)) * circleAngularCoordinate e (0, (q : E)))



theorem periodicCircleCurve_sphereCircleParameter {T : ℝ} (hT : 0 < T)
    (e : ℂ ≃ₗᵢ[ℝ] E) {γ : ℝ → F} (hγ : Periodic γ T) (s : ℝ) :
    periodicCircleCurve T e γ (sphereCircleParameter e s) =
      γ ((T / (2 * Real.pi)) * s) := by
  let α := circleAngularCoordinate e (0, (sphereCircleParameter e s : E))
  have heq : Circle.exp α = Circle.exp s := by
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val
      (sphereCircleParameter_circleAngularCoordinate e 0 (sphereCircleParameter e s))
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp heq
  have hτ : 2 * Real.pi ≠ 0 := by positivity
  have hscale : (T / (2 * Real.pi)) * α =
      (T / (2 * Real.pi)) * s + (m : ℝ) * T := by
    rw [hm]
    field_simp
  change γ ((T / (2 * Real.pi)) * α) = _
  rw [hscale]
  exact hγ.int_mul m _



theorem periodicCircleCurve_eq_branch {T : ℝ} (hT : 0 < T)
    (e : ℂ ≃ₗᵢ[ℝ] E) {γ : ℝ → F} (hγ : Periodic γ T)
    (a : ℝ) (q : sphere (0 : E) 1) :
    periodicCircleCurve T e γ q =
      γ ((T / (2 * Real.pi)) * circleAngularCoordinate e (a, (q : E))) := by
  have h := periodicCircleCurve_sphereCircleParameter hT e hγ
    (circleAngularCoordinate e (a, (q : E)))
  rwa [sphereCircleParameter_circleAngularCoordinate] at h



theorem injective_periodicCircleCurve {T : ℝ} (hT : 0 < T)
    (e : ℂ ≃ₗᵢ[ℝ] E) {γ : ℝ → F} (hγ : Periodic γ T)
    (hinj : InjOn γ (Ico 0 T)) : Injective (periodicCircleCurve T e γ) := by
  have hτ : 0 < 2 * Real.pi := by positivity
  have hc : 0 < T / (2 * Real.pi) := div_pos hT hτ
  have hrep (q : sphere (0 : E) 1) :
      ∃ s ∈ Ico (0 : ℝ) (2 * Real.pi), sphereCircleParameter e s = q := by
    obtain ⟨u, hu⟩ := surjective_sphereCircleParameter e q
    let m : ℤ := ⌊u / (2 * Real.pi)⌋
    have hlo : (m : ℝ) * (2 * Real.pi) ≤ u :=
      (le_div_iff₀ hτ).mp (Int.floor_le _)
    have hhi : u < ((m : ℝ) + 1) * (2 * Real.pi) :=
      (div_lt_iff₀ hτ).mp (Int.lt_floor_add_one _)
    refine ⟨u - m * (2 * Real.pi), ⟨by linarith, by nlinarith⟩, ?_⟩
    exact ((periodic_sphereCircleParameter e).sub_int_mul_eq m).trans hu
  have hscaled {s : ℝ} (hs : s ∈ Ico (0 : ℝ) (2 * Real.pi)) :
      (T / (2 * Real.pi)) * s ∈ Ico (0 : ℝ) T := by
    refine ⟨mul_nonneg hc.le hs.1, ?_⟩
    calc
      (T / (2 * Real.pi)) * s < (T / (2 * Real.pi)) * (2 * Real.pi) :=
        mul_lt_mul_of_pos_left hs.2 hc
      _ = T := div_mul_cancel₀ _ hτ.ne'
  intro q r heq
  obtain ⟨s, hs, hsq⟩ := hrep q
  obtain ⟨t, ht, htr⟩ := hrep r
  rw [← hsq, ← htr, periodicCircleCurve_sphereCircleParameter hT e hγ,
    periodicCircleCurve_sphereCircleParameter hT e hγ] at heq
  have hst : s = t := mul_left_cancel₀ hc.ne' (hinj (hscaled hs) (hscaled ht) heq)
  exact hsq.symm.trans ((congrArg (sphereCircleParameter e) hst).trans htr)



theorem range_periodicCircleCurve {T : ℝ} (hT : 0 < T)
    (e : ℂ ≃ₗᵢ[ℝ] E) {γ : ℝ → F} (hγ : Periodic γ T) :
    range (periodicCircleCurve T e γ) = range γ := by
  apply Subset.antisymm
  · rintro y ⟨q, rfl⟩
    exact ⟨_, rfl⟩
  · rintro y ⟨t, rfl⟩
    refine ⟨sphereCircleParameter e (((2 * Real.pi) / T) * t), ?_⟩
    rw [periodicCircleCurve_sphereCircleParameter hT e hγ]
    congr 1
    field_simp

end Pointwise

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]



theorem contMDiffAt_circleAngularCoordinate_sphere (e : ℂ ≃ₗᵢ[ℝ] E)
    (a : ℝ) (q : sphere (0 : E) 1)
    (hq : e.symm (q : E) * (Circle.exp (-a) : ℂ) ∈ Complex.slitPlane) :
    ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞
      (fun q' : sphere (0 : E) 1 => circleAngularCoordinate e (a, (q' : E))) q := by
  have h := (contDiffOn_circleAngularCoordinate e (k := ∞)).contDiffAt
    ((isOpen_circleAngularCoordinate_domain e).mem_nhds (x := (a, (q : E))) hq)
  exact h.contMDiffAt.comp q
    (contMDiffAt_const.prodMk_space
      (contMDiff_coe_sphere (E := E) (n := 1) (m := ∞)).contMDiffAt)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem contMDiff_periodicCircleCurve_family {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {T : ℝ} (hT : 0 < T) (e : ℂ ≃ₗᵢ[ℝ] E)
    (γ : V → ℝ → F) (hγ : ContDiff ℝ ∞ (fun x : V × ℝ => γ x.1 x.2))
    (hper : ∀ z, Periodic (γ z) T) :
    ContMDiff (𝓘(ℝ, V).prod (𝓡 1)) 𝓘(ℝ, F) ∞
      (fun x : V × sphere (0 : E) 1 => periodicCircleCurve T e (γ x.1) x.2) := by
  intro x
  obtain ⟨a, ha⟩ := surjective_sphereCircleParameter e x.2
  have hdomain := sphereCircleParameter_mem_angularDomain e a a
    (by simp only [sub_self, mem_Ioo]; exact ⟨neg_neg_of_pos Real.pi_pos, Real.pi_pos⟩)
  rw [ha] at hdomain
  have hA := contMDiffAt_circleAngularCoordinate_sphere e a x.2 hdomain
  have hc : ContDiff ℝ ∞ (fun t : ℝ => (T / (2 * Real.pi)) * t) :=
    contDiff_const.mul contDiff_id
  have hbranch := hc.contMDiff.contMDiffAt.comp x.2 hA
  have hpair : ContMDiffAt (𝓘(ℝ, V).prod (𝓡 1)) 𝓘(ℝ, V × ℝ) ∞
      (fun y : V × sphere (0 : E) 1 =>
        (y.1, (T / (2 * Real.pi)) * circleAngularCoordinate e (a, (y.2 : E)))) x :=
    contMDiffAt_fst.prodMk_space (hbranch.comp x contMDiffAt_snd)
  apply (hγ.contMDiff.contMDiffAt.comp x hpair).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y => periodicCircleCurve_eq_branch hT e (hper y.1) a y.2)



theorem mfderiv_periodicCircleCurve_injective {T : ℝ} (hT : 0 < T)
    (e : ℂ ≃ₗᵢ[ℝ] E) {γ : ℝ → F} (hper : Periodic γ T)
    (hγ : ContDiff ℝ ∞ γ) (hder : ∀ t, deriv γ t ≠ 0)
    (q : sphere (0 : E) 1) :
    Injective (mfderiv (𝓡 1) 𝓘(ℝ, F) (periodicCircleCurve T e γ) q) := by
  obtain ⟨a, ha⟩ := surjective_sphereCircleParameter e q
  have hdomain := sphereCircleParameter_mem_angularDomain e a a
    (by simp only [sub_self, mem_Ioo]; exact ⟨neg_neg_of_pos Real.pi_pos, Real.pi_pos⟩)
  rw [ha] at hdomain
  let A : sphere (0 : E) 1 → ℝ := fun p =>
    (T / (2 * Real.pi)) * circleAngularCoordinate e (a, (p : E))
  let B : ℝ → sphere (0 : E) 1 := fun t => sphereCircleParameter e (((2 * Real.pi) / T) * t)
  have hc : ContDiff ℝ ∞ (fun t : ℝ => (T / (2 * Real.pi)) * t) :=
    contDiff_const.mul contDiff_id
  have hA : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ A q :=
    hc.contMDiff.contMDiffAt.comp q
      (contMDiffAt_circleAngularCoordinate_sphere e a q hdomain)
  have hB : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ B :=
    (contMDiff_sphereCircleParameter e).comp
      ((contDiff_const.mul contDiff_id).contMDiff)
  have hleft : B ∘ A = id := by
    funext p
    change sphereCircleParameter e
      (((2 * Real.pi) / T) * ((T / (2 * Real.pi)) *
        circleAngularCoordinate e (a, (p : E)))) = p
    have hcancel : ((2 * Real.pi) / T) * ((T / (2 * Real.pi)) *
        circleAngularCoordinate e (a, (p : E))) = circleAngularCoordinate e (a, (p : E)) := by
      field_simp
    rw [hcancel]
    exact sphereCircleParameter_circleAngularCoordinate e a p
  have hchain := mfderiv_comp q (hB.contMDiffAt.mdifferentiableAt (by simp))
    (hA.mdifferentiableAt (by simp))
  rw [hleft, mfderiv_id] at hchain
  have hAi : Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) A q) := by
    intro v w hv
    have hh := congrArg (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) B (A q)) hv
    change ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) B (A q)).comp
      (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) A q)) v =
      ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) B (A q)).comp
        (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) A q)) w at hh
    rw [← hchain] at hh
    exact hh
  have hγi : Injective (fderiv ℝ γ (A q)) := by
    intro v w hv
    simp only [fderiv_eq_smul_deriv] at hv
    exact (smul_left_injective ℝ (hder (A q))) hv
  have heq : periodicCircleCurve T e γ = γ ∘ A :=
    funext (fun p => periodicCircleCurve_eq_branch hT e hper a p)
  rw [heq, mfderiv_comp q (hγ.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    (hA.mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
  exact hγi.comp hAi

end Smooth

end Poincare.Manifold.Schoenflies.Plane
