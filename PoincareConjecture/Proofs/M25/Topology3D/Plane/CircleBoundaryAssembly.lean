import PoincareConjecture.Proofs.M25.Topology3D.Plane.SmoothCircleLift
import PoincareConjecture.Proofs.M25.Topology3D.Plane.CircleLiftExtension
import Mathlib.Analysis.Calculus.Deriv.MeanValue










set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem circle_lift_add_period_of_positive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : ℂ ≃ₗᵢ[ℝ] E) (B : ℝ → ℝ) (hB : ContDiff ℝ ∞ B)
    (hpos : ∀ s, 0 < deriv B s)
    (hper : Periodic (fun s => sphereCircleParameter e (B s)) (2 * Real.pi))
    (hinj : ∀ s t, sphereCircleParameter e (B s) = sphereCircleParameter e (B t) →
      sphereCircleParameter e s = sphereCircleParameter e t) :
    ∀ s, B (s + 2 * Real.pi) = B s + 2 * Real.pi := by
  have hmono : StrictMono B := strictMono_of_deriv_pos hpos
  have hτ : 0 < 2 * Real.pi := by positivity
  intro s
  have heq : Circle.exp (B (s + 2 * Real.pi)) = Circle.exp (B s) := by
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val (hper s)
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp heq
  have hmpos : (0 : ℝ) < m := by
    have hh := hmono (show s < s + 2 * Real.pi by linarith)
    nlinarith
  have hmone : (1 : ℤ) ≤ m := by
    have : (0 : ℤ) < m := by exact_mod_cast hmpos
    omega
  have hmexact : m = 1 := by
    by_contra hne
    have hmgt : (1 : ℝ) < m := by exact_mod_cast (show (1 : ℤ) < m by omega)
    have hlt : B s + 2 * Real.pi < B (s + 2 * Real.pi) := by nlinarith
    obtain ⟨u, hu, heu⟩ := intermediate_value_Icc
      (show s ≤ s + 2 * Real.pi by linarith) hB.continuous.continuousOn
        (show B s + 2 * Real.pi ∈ Icc (B s) (B (s + 2 * Real.pi)) from
          ⟨by linarith, hlt.le⟩)
    have hus : s < u := hmono.lt_iff_lt.mp (by rw [heu]; linarith)
    have hut : u < s + 2 * Real.pi := hmono.lt_iff_lt.mp (by rwa [heu])
    have hsame : sphereCircleParameter e (B u) = sphereCircleParameter e (B s) := by
      rw [heu]
      exact periodic_sphereCircleParameter e (B s)
    have hueq := injOn_sphereCircleParameter_Ico e
      (show (s + 2 * Real.pi) - s ≤ 2 * Real.pi by linarith)
      (show u ∈ Ico s (s + 2 * Real.pi) from ⟨hus.le, hut⟩)
      (show s ∈ Ico s (s + 2 * Real.pi) from ⟨le_rfl, by linarith⟩)
      (hinj u s hsame)
    exact (ne_of_gt hus) hueq
  simpa only [hmexact, Int.cast_one, one_mul] using hm




theorem exists_circle_lift_ambient_extension
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ ≃ₗᵢ[ℝ] E) (q0 : sphere (0 : E) 1)
    (B : ℝ × ℝ → ℝ) (hB : ContDiff ℝ ∞ B)
    (hper : ∀ z, Periodic (fun s => sphereCircleParameter e (B (z, s))) (2 * Real.pi))
    (hinj : ∀ z s t, sphereCircleParameter e (B (z, s)) =
      sphereCircleParameter e (B (z, t)) → sphereCircleParameter e s = sphereCircleParameter e t)
    (hne : ∀ z s, deriv (fun t => B (z, t)) s ≠ 0) :
    ∃ A : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun p : ℝ × E => A p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (A p.1).symm p.2) ∧
      ∀ z s, A z (sphereCircleParameter e s : E) = (sphereCircleParameter e (B (z, s)) : E) := by
  have hpositive (C : ℝ × ℝ → ℝ) (hC : ContDiff ℝ ∞ C)
      (hCp : ∀ z, Periodic (fun s => sphereCircleParameter e (C (z, s))) (2 * Real.pi))
      (hCi : ∀ z s t, sphereCircleParameter e (C (z, s)) =
        sphereCircleParameter e (C (z, t)) → sphereCircleParameter e s = sphereCircleParameter e t)
      (hCd : ∀ z s, 0 < deriv (fun t => C (z, t)) s) :
      ∃ A : ℝ → (E ≃ₘ[ℝ] E),
        ContDiff ℝ ∞ (fun p : ℝ × E => A p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × E => (A p.1).symm p.2) ∧
        ∀ z s, A z (sphereCircleParameter e s : E) =
          (sphereCircleParameter e (C (z, s)) : E) := by
    have htrans (z : ℝ) := circle_lift_add_period_of_positive e (fun s => C (z, s))
      (hC.comp (contDiff_const.prodMk contDiff_id)) (hCd z) (hCp z) (hCi z)
    obtain ⟨A, hA, hAi, _, _, _, hAb⟩ :=
      exists_supported_circle_lift_extension e q0 C hC htrans hCd
    exact ⟨A, hA, hAi, hAb⟩
  let d : ℝ × ℝ → ℝ := fun p => fderiv ℝ B p (0, 1)
  have hd : Continuous d :=
    ((hB.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hder (z s : ℝ) : HasDerivAt (fun t => B (z, t)) (d (z, s)) s :=
    (hB.differentiable (by simp) (z, s)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_const s z).prodMk (hasDerivAt_id s))
  have hdne (p : ℝ × ℝ) : d p ≠ 0 := by
    rw [← (hder p.1 p.2).deriv]
    exact hne p.1 p.2
  have hsign : (∀ p, 0 < d p) ∨ ∀ p, d p < 0 := by
    rcases lt_or_gt_of_ne (hdne (0, 0)) with hneg | hpos
    · right
      intro p
      by_contra hp
      obtain ⟨u, hu⟩ := intermediate_value_univ (0, 0) p hd ⟨hneg.le, le_of_not_gt hp⟩
      exact hdne u hu
    · left
      intro p
      by_contra hp
      obtain ⟨u, hu⟩ := intermediate_value_univ p (0, 0) hd ⟨le_of_not_gt hp, hpos.le⟩
      exact hdne u hu
  rcases hsign with hpos | hneg
  · exact hpositive B hB hper hinj (fun z s => by rw [(hder z s).deriv]; exact hpos (z, s))
  let R : E ≃ₘ[ℝ] E :=
    (e.symm.trans (Complex.conjLIE.trans e)).toContinuousLinearEquiv.toDiffeomorph
  have hR (s : ℝ) : R (sphereCircleParameter e s : E) = (sphereCircleParameter e (-s) : E) := by
    change e (starRingEnd ℂ (e.symm (e (Circle.exp s : ℂ)))) = e (Circle.exp (-s) : ℂ)
    rw [e.symm_apply_apply, Circle.exp_neg, Circle.coe_inv_eq_conj]
  let C : ℝ × ℝ → ℝ := fun p => B (p.1, -p.2)
  have hC : ContDiff ℝ ∞ C := hB.comp (contDiff_fst.prodMk contDiff_snd.neg)
  have hCp (z : ℝ) : Periodic (fun s => sphereCircleParameter e (C (z, s))) (2 * Real.pi) := by
    intro s
    change sphereCircleParameter e (B (z, -(s + 2 * Real.pi))) =
      sphereCircleParameter e (B (z, -s))
    rw [neg_add, ← sub_eq_add_neg]
    exact (hper z).sub_eq (-s)
  have hCi (z s t : ℝ) (h : sphereCircleParameter e (C (z, s)) =
      sphereCircleParameter e (C (z, t))) :
      sphereCircleParameter e s = sphereCircleParameter e t := by
    have hh := congrArg (fun q : sphere (0 : E) 1 => R (q : E)) (hinj z (-s) (-t) h)
    rw [hR, hR, neg_neg, neg_neg] at hh
    exact Subtype.ext hh
  have hCd (z s : ℝ) : 0 < deriv (fun t => C (z, t)) s := by
    have hh := (hder z (-s)).comp s (hasDerivAt_id s).neg
    change HasDerivAt (fun t => C (z, t)) (d (z, -s) * -1) s at hh
    rw [hh.deriv]
    nlinarith [hneg (z, -s)]
  obtain ⟨H, hH, hHi, hHb⟩ := hpositive C hC hCp hCi hCd
  refine ⟨fun z => R.trans (H z), ?_, ?_, ?_⟩
  · exact hH.comp (contDiff_fst.prodMk (R.contDiff.comp contDiff_snd))
  · exact R.symm.contDiff.comp hHi
  · intro z s
    change H z (R (sphereCircleParameter e s : E)) = (sphereCircleParameter e (B (z, s)) : E)
    rw [hR, hHb]
    simp only [C, neg_neg]




theorem exists_unit_curve_ambient_extension
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (e : ℂ ≃ₗᵢ[ℝ] E) (q0 : sphere (0 : E) 1)
    (γ : ℝ × ℝ → E) (hγ : ContDiff ℝ ∞ γ)
    (hnorm : ∀ p, ‖γ p‖ = 1)
    (hper : ∀ z, Periodic (fun s => γ (z, s)) (2 * Real.pi))
    (hne : ∀ z s, deriv (fun t => γ (z, t)) s ≠ 0)
    (hinj : ∀ z s t, γ (z, s) = γ (z, t) →
      sphereCircleParameter e s = sphereCircleParameter e t) :
    ∃ A : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun p : ℝ × E => A p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (A p.1).symm p.2) ∧
      ∀ z s, A z (sphereCircleParameter e s : E) = γ (z, s) := by
  let q : sphere (0 : E) 1 := ⟨γ (0, 0), mem_sphere_zero_iff_norm.mpr (hnorm (0, 0))⟩
  obtain ⟨s0, hs0⟩ := surjective_sphereCircleParameter e q
  obtain ⟨B, hB, _, hBγ⟩ := exists_contDiff_sphere_parameter_lift e γ hγ hnorm (0, 0) s0
    (congrArg Subtype.val hs0)
  have hBp (z : ℝ) : Periodic (fun s => sphereCircleParameter e (B (z, s))) (2 * Real.pi) := by
    intro s
    apply Subtype.ext
    rw [hBγ, hBγ]
    exact hper z s
  have hBi (z s t : ℝ) (h : sphereCircleParameter e (B (z, s)) =
      sphereCircleParameter e (B (z, t))) :
      sphereCircleParameter e s = sphereCircleParameter e t := by
    apply hinj z s t
    simpa only [hBγ] using congrArg Subtype.val h
  have hBn (z s : ℝ) : deriv (fun t => B (z, t)) s ≠ 0 := by
    intro hz
    have hdB : HasDerivAt (fun t => B (z, t)) (deriv (fun t => B (z, t)) s) s :=
      ((hB.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) s).hasDerivAt
    have hh := (hasDerivAt_sphereCircleParameter_coe e (B (z, s))).scomp s hdB
    have hfun : ((fun t => (sphereCircleParameter e t : E)) ∘ fun t => B (z, t)) =
        (fun t => γ (z, t)) := funext (fun t => hBγ (z, t))
    rw [hfun, hz, zero_smul] at hh
    exact hne z s hh.deriv
  obtain ⟨A, hA, hAi, hAb⟩ := exists_circle_lift_ambient_extension e q0 B hB hBp hBi hBn
  exact ⟨A, hA, hAi, fun z s => (hAb z s).trans (hBγ (z, s))⟩

end PoincareConjecture.M25.Topology3D
