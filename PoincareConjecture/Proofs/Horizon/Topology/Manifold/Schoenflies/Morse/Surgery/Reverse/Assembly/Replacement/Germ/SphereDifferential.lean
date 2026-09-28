import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Reverse

theorem bijective_convex_identity_of_positive_normal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E] (A : E →L[Real] E) (p : E)
    (hpp : inner Real p p = 1)
    (htan : ∀ u, inner Real p u = 0 -> A u = u)
    (hnormal : 0 < inner Real p (A p))
    {t : Real} (ht : t ∈ Icc 0 1) :
    Function.Bijective ((1 - t) • ContinuousLinearMap.id Real E + t • A) := by
  let B := (1 - t) • ContinuousLinearMap.id Real E + t • A
  have hcoef : 0 < 1 - t + t * inner Real p (A p) := by
    by_cases ht0 : t = 0
    · simp [ht0]
    · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have := mul_pos htp hnormal
      linarith [ht.2]
  have hB (u : E) : B u = (1 - t) • u + t • A u := rfl
  have hinj : Function.Injective B := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    change B u = 0 at hu
    have hproj : inner Real p (u - inner Real p u • p) = 0 := by
      simp only [inner_sub_right, inner_smul_right, hpp, mul_one, sub_self]
    have hAu : A u = u - inner Real p u • p + inner Real p u • A p := by
      have hh := htan _ hproj
      rw [map_sub, map_smul] at hh
      exact eq_add_of_sub_eq hh
    have hdot := congrArg (inner Real p) hu
    rw [hB, hAu] at hdot
    simp only [inner_add_right, inner_sub_right, inner_smul_right, hpp,
      mul_one, inner_zero_right, sub_self, zero_add] at hdot
    have hpu : inner Real p u = 0 := by
      have hz : (1 - t + t * inner Real p (A p)) * inner Real p u = 0 := by
        nlinarith [hdot]
      exact (mul_eq_zero.mp hz).resolve_left hcoef.ne'
    rw [hB, htan u hpu, ← add_smul, sub_add_cancel, one_smul] at hu
    exact hu
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

theorem fderiv_eq_self_on_fixed_sphere_patch
    {D : E3 -> E3} (hD : ContDiff Real ∞ D)
    {U : Set E3} (hU : IsOpen U)
    (hfix : ∀ x ∈ U ∩ sphere (0 : E3) 1, D x = x)
    (p : S2) (hpU : (p : E3) ∈ U)
    (u : E3) (hu : inner Real (p : E3) u = 0) : fderiv Real D p u = u := by
  let L : TangentSpace (𝓡 2) p →L[Real] E3 :=
    mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S2 -> E3) p
  have hrange : L.range = (Real ∙ (p : E3))ᗮ := by
    convert! range_mvfderiv_subtypeVal p
  have heq : D ∘ (Subtype.val : S2 -> E3) =ᶠ[𝓝 p] (Subtype.val : S2 -> E3) := by
    filter_upwards [continuous_subtype_val.continuousAt.eventually (hU.mem_nhds hpU)] with q hq
    exact hfix q ⟨hq, q.property⟩
  have hchain := mfderiv_comp p (hD.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    ((contMDiff_coe_sphere (n := 2) p).mdifferentiableAt
      (show (∞ : ℕ∞ω) ≠ 0 by simp))
  rw [heq.mfderiv_eq (I := 𝓡 2) (I' := 𝓡 3), mfderiv_eq_fderiv] at hchain
  have huL : u ∈ L.range := by
    rw [hrange, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hu
  obtain ⟨w, rfl⟩ := huL
  exact (congrArg (fun A => A w) hchain).symm

theorem positive_normal_of_ball_preserving_sphere_patch
    {D : E3 -> E3} (hD : ContDiff Real ∞ D)
    (hball : MapsTo D (closedBall (0 : E3) 1) (closedBall (0 : E3) 1))
    {U : Set E3} (hU : IsOpen U)
    (hfix : ∀ x ∈ U ∩ sphere (0 : E3) 1, D x = x)
    (p : S2) (hpU : (p : E3) ∈ U) (hinj : Injective (fderiv Real D p)) :
    0 < inner Real (p : E3) (fderiv Real D p p) := by
  have hDp : D p = p := hfix p ⟨hpU, p.property⟩
  have hcurve : HasDerivAt (fun t : Real => D ((1 + t) • (p : E3)))
      (fderiv Real D p p) 0 := by
    have hd := ((hasDerivAt_const (0 : Real) (1 : Real)).add (hasDerivAt_id 0)).smul_const (p : E3)
    have hD0 : HasFDerivAt D (fderiv Real D p) ((1 + (0 : Real)) • (p : E3)) := by
      simpa using (hD.differentiable (by simp) p).hasFDerivAt
    have hc := hD0.comp_hasDerivAt 0
      (show HasDerivAt (fun t : Real => (1 + t) • (p : E3)) (p : E3) 0 by simpa using hd)
    convert! hc using 1
  have hinside : ∀ᶠ t in 𝓝[<] (0 : Real), ‖D ((1 + t) • (p : E3))‖ ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (-1 : Real) < 0 by norm_num)] with t ht
    apply mem_closedBall_zero_iff.mp (hball ?_)
    rw [mem_closedBall_zero_iff, norm_smul]
    simp only [norm_eq_of_mem_sphere p, Real.norm_eq_abs, mul_one,
      abs_of_pos (by linarith [ht.1] : 0 < 1 + t)]
    linarith [ht.2]
  have hlim := hcurve.norm_sq.tendsto_slope_zero_left
  have hnonneg : 0 ≤ 2 * inner Real (p : E3) (fderiv Real D p p) := by
    simp only [zero_add, add_zero, one_smul, hDp, norm_eq_of_mem_sphere p, one_pow] at hlim
    apply ge_of_tendsto hlim
    filter_upwards [hinside, self_mem_nhdsWithin] with t ht htneg
    change 0 ≤ t⁻¹ * (‖D ((1 + t) • (p : E3))‖ ^ 2 - 1)
    apply mul_nonneg_of_nonpos_of_nonpos
    · exact inv_nonpos.mpr (le_of_lt htneg)
    · nlinarith [norm_nonneg (D ((1 + t) • (p : E3)))]
  have hne : inner Real (p : E3) (fderiv Real D p p) ≠ 0 := by
    intro hz
    have htan := fderiv_eq_self_on_fixed_sphere_patch hD hU hfix p hpU
      (fderiv Real D p p) hz
    have heq : fderiv Real D p p = (p : E3) := hinj htan
    rw [heq] at hz
    simp at hz
  exact lt_of_le_of_ne (by linarith) hne.symm

theorem bijective_fderiv_homotopy_of_ball_preserving_sphere_patch
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hball : MapsTo D (closedBall (0 : E3) 1) (closedBall (0 : E3) 1))
    {U : Set E3} (hU : IsOpen U)
    (hfix : ∀ x ∈ U ∩ sphere (0 : E3) 1, D x = x)
    {t : Real} (ht : t ∈ Icc 0 1) (p : S2) (hpU : (p : E3) ∈ U) :
    Function.Bijective (fderiv Real (fun y => (1 - t) • y + t • D y) p) := by
  have hD : ContDiff Real ∞ D := D.contMDiff.contDiff
  have hinj : Function.Injective (fderiv Real D p) := by
    have h := (D.mfderivToContinuousLinearEquiv (by simp) p).injective
    change Function.Injective (mfderiv (𝓡 3) (𝓡 3) D p) at h
    simpa only [mfderiv_eq_fderiv, TangentSpace] using h
  have hd := ((hasFDerivAt_id (p : E3)).const_smul (1 - t)).add
    ((hD.differentiable (by simp) p).hasFDerivAt.const_smul t)
  change Function.Bijective
    (fderiv Real ((1 - t) • (id : E3 -> E3) + t • (D : E3 -> E3)) (p : E3))
  rw [hd.fderiv]
  exact bijective_convex_identity_of_positive_normal _ (p : E3) (by simp)
    (fderiv_eq_self_on_fixed_sphere_patch hD hU hfix p hpU)
    (positive_normal_of_ball_preserving_sphere_patch hD hball hU hfix p hpU hinj) ht

end Poincare.Manifold.Schoenflies.Reverse
