import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Circle.Normal

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := Metric.sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

theorem fderiv_eq_self_on_circle_tangent {e : E2 -> E2}
    (he : ContDiff Real ∞ e) (hfix : ∀ p : S1, e p = p) (p : S1)
    (u : E2) (hu : inner Real (p : E2) u = 0) : fderiv Real e p u = u := by
  let L : TangentSpace (𝓡 1) p →L[Real] E2 :=
    mfderiv (𝓡 1) (𝓡 2) (Subtype.val : S1 -> E2) p
  have hrange : L.range = (Real ∙ (p : E2))ᗮ := by
    convert! range_mvfderiv_subtypeVal p
  have heq : e ∘ (Subtype.val : S1 -> E2) = Subtype.val := funext hfix
  have hchain := mfderiv_comp p (he.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    ((contMDiff_coe_sphere (n := 1) p).mdifferentiableAt
      (show (∞ : ℕ∞ω) ≠ 0 by simp))
  rw [heq, mfderiv_eq_fderiv] at hchain
  have huL : u ∈ L.range := by
    rw [hrange, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hu
  obtain ⟨w, rfl⟩ := huL
  exact (congrArg (fun A => A w) hchain).symm

private theorem bijective_convex_identity_of_positive_normal
    (A : E2 →L[Real] E2) (p : S1)
    (htan : ∀ u, inner Real (p : E2) u = 0 -> A u = u)
    (hnormal : 0 < inner Real (p : E2) (A p))
    {t : Real} (ht : t ∈ Icc 0 1) :
    Function.Bijective ((1 - t) • ContinuousLinearMap.id Real E2 + t • A) := by
  let B := (1 - t) • ContinuousLinearMap.id Real E2 + t • A
  have hpp : inner Real (p : E2) p = 1 := by simp
  have hcoef : 0 < 1 - t + t * inner Real (p : E2) (A p) := by
    by_cases ht0 : t = 0
    · simp [ht0]
    · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have := mul_pos htp hnormal
      linarith [ht.2]
  have hB (u : E2) : B u = (1 - t) • u + t • A u := rfl
  have hinj : Function.Injective B := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u hu
    change B u = 0 at hu
    have hproj : inner Real (p : E2) (u - inner Real (p : E2) u • (p : E2)) = 0 := by
      simp only [inner_sub_right, inner_smul_right, hpp, mul_one, sub_self]
    have hAu : A u = u - inner Real (p : E2) u • (p : E2) +
        inner Real (p : E2) u • A p := by
      have hh := htan _ hproj
      rw [map_sub, map_smul] at hh
      exact eq_add_of_sub_eq hh
    have hdot := congrArg (inner Real (p : E2)) hu
    rw [hB, hAu] at hdot
    simp only [inner_add_right, inner_sub_right, inner_smul_right, hpp,
      mul_one, inner_zero_right, sub_self, zero_add] at hdot
    have hpu : inner Real (p : E2) u = 0 := by
      have hz : (1 - t + t * inner Real (p : E2) (A p)) * inner Real (p : E2) u = 0 := by
        nlinarith [hdot]
      exact (mul_eq_zero.mp hz).resolve_left hcoef.ne'
    rw [hB, htan u hpu, ← add_smul, sub_add_cancel, one_smul] at hu
    exact hu
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

theorem bijective_fderiv_circle_collar_homotopy {e : E2 -> E2}
    (he : ContDiff Real ∞ e) (hfix : ∀ p : S1, e p = p)
    (hnormal : ∀ p : S1, 0 < inner Real (p : E2) (fderiv Real e p p))
    {t : Real} (ht : t ∈ Icc 0 1) (p : S1) :
    Function.Bijective (fderiv Real (fun x : E2 => (1 - t) • x + t • e x) p) := by
  have hd := ((hasFDerivAt_id (p : E2)).const_smul (1 - t)).add
    ((he.differentiable (by simp) p).hasFDerivAt.const_smul t)
  change Function.Bijective (fderiv Real ((1 - t) • (id : E2 -> E2) + t • e) (p : E2))
  rw [hd.fderiv]
  exact bijective_convex_identity_of_positive_normal (fderiv Real e p) p
    (fderiv_eq_self_on_circle_tangent he hfix p) (hnormal p) ht

end Poincare.Manifold.Schoenflies
