import PoincareConjecture.Proofs.M63.Mathlib.PeriodicTranslation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_periodicTranslation (f g : C(AddCircle L, E))
    (hf : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : AddCircle L))
      (g (x : AddCircle L)) x) (a : ℝ) :
    HasDerivAt (fun s : ℝ => periodicTranslation s f) (-(periodicTranslation a g)) a := by
  have hpoint (x : AddCircle L) (s : ℝ) :
      HasDerivAt (fun r : ℝ => periodicTranslation r f x) (-(periodicTranslation s g x)) s := by
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    change HasDerivAt (fun r : ℝ => f ((y : AddCircle L) - (r : AddCircle L)))
      (-g ((y : AddCircle L) - (s : AddCircle L))) s
    simpa only [Function.comp_def, id_eq, neg_one_smul, AddCircle.coe_sub] using
      (hf (y - s)).scomp s ((hasDerivAt_id s).const_sub y)
  have hcont : Continuous (fun s : ℝ => periodicTranslation s g) :=
    continuous_periodicTranslation.comp (continuous_id.prodMk continuous_const)
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro eps heps
  obtain ⟨delta, hdelta, hnear⟩ := Metric.continuousAt_iff.mp hcont.continuousAt eps heps
  filter_upwards [Metric.ball_mem_nhds a hdelta] with s hs
  apply (ContinuousMap.norm_le _ (mul_nonneg heps.le (norm_nonneg _))).mpr
  intro x
  let b : E := -(periodicTranslation a g x)
  let h : ℝ → E := fun r => periodicTranslation r f x - (r - a) • b
  have hd (r : ℝ) : HasDerivAt h (-(periodicTranslation r g x) - b) r := by
    exact ((hpoint x r).sub (((hasDerivAt_id r).sub_const a).smul_const b)).congr_deriv
      (by simp only [one_smul])
  have hb (r : ℝ) (hr : r ∈ Metric.ball a delta) :
      ‖-(periodicTranslation r g x) - b‖ ≤ eps := by
    have hnorm : ‖periodicTranslation r g - periodicTranslation a g‖ < eps := by
      simpa only [dist_eq_norm] using hnear hr
    have hx := ((periodicTranslation r g - periodicTranslation a g).norm_coe_le_norm x).trans
      hnorm.le
    simpa only [b, neg_sub_neg, norm_sub_rev, ContinuousMap.sub_apply] using hx
  have hrem := (convex_ball a delta).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (hd r).hasDerivWithinAt) hb (Metric.mem_ball_self hdelta) hs
  simp only [h, sub_self, zero_smul, sub_zero] at hrem
  change ‖periodicTranslation s f x - periodicTranslation a f x - (s - a) • b‖ ≤ _
  have heq : periodicTranslation s f x - periodicTranslation a f x - (s - a) • b =
      (periodicTranslation s f x - (s - a) • b) - periodicTranslation a f x := by abel
  rw [heq]
  exact hrem

theorem contDiff_periodicTranslation_nat (k : ℕ) (f : C(AddCircle L, E))
    (hf : ContDiff ℝ k (fun x : ℝ => f (x : AddCircle L))) :
    ContDiff ℝ k (fun a : ℝ => periodicTranslation a f) := by
  induction k generalizing f with
  | zero =>
    exact contDiff_zero.mpr
      (continuous_periodicTranslation.comp (continuous_id.prodMk continuous_const))
  | succ k ih =>
    let u : ℝ → E := fun x => f (x : AddCircle L)
    have hu : ContDiff ℝ ((k : ℕ∞ω) + 1) u := by
      simpa only [Nat.cast_add, Nat.cast_one] using hf
    have hud : Differentiable ℝ u := hu.differentiable (by simp)
    have hu1 : ContDiff ℝ k (deriv u) := hu.deriv'
    have hp : Function.Periodic u L := by
      intro x
      simp only [u, AddCircle.coe_add_period]
    have hp1 : Function.Periodic (deriv u) L := by
      intro x
      have h : HasDerivAt (fun y => u (y + L)) (deriv u (x + L)) x := by
        simpa only [Function.comp_def, one_smul, id_eq] using
          (hud (x + L)).hasDerivAt.scomp x ((hasDerivAt_id x).add_const L)
      rw [show (fun y => u (y + L)) = u from funext hp] at h
      exact h.unique (hud x).hasDerivAt
    let g : C(AddCircle L, E) := ⟨hp1.lift,
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L)).continuous_iff.mpr
        hu1.continuous⟩
    have hg (x : ℝ) : HasDerivAt (fun y : ℝ => f (y : AddCircle L))
        (g (x : AddCircle L)) x := (hud x).hasDerivAt
    have hderiv := hasDerivAt_periodicTranslation f g hg
    have hderivEq : deriv (fun a : ℝ => periodicTranslation a f) =
        fun a => -(periodicTranslation a g) := funext (fun a => (hderiv a).deriv)
    have hgoal : ContDiff ℝ ((k : ℕ∞ω) + 1) (fun a : ℝ => periodicTranslation a f) := by
      rw [contDiff_succ_iff_deriv]
      refine ⟨fun a => (hderiv a).differentiableAt, by simp, ?_⟩
      rw [hderivEq]
      exact (ih g hu1).neg
    simpa only [Nat.cast_add, Nat.cast_one] using hgoal

theorem contDiff_periodicTranslation (f : C(AddCircle L, E))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle L))) :
    ContDiff ℝ ∞ (fun a : ℝ => periodicTranslation a f) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro k hk
  exact contDiff_periodicTranslation_nat k f (hf.of_le (by exact_mod_cast hk))

end PoincareConjecture.M63
