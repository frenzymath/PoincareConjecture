import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientNormalFlow
import PoincareConjecture.Proofs.M63.Mathlib.PrescribedPeriodicLabelFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem exists_normal_curve_on_prescribed_ambient_slab
    (F : RicciFlow n M (Icc a b)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e) {U : Set W} (hU : IsOpen U)
    (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {L T S : ℝ} (hL : 0 < L) (hT : 0 < T) (hS : 0 < S)
    (hTb : a + T ≤ b) (hST : S ≤ T / 4) (hS1 : S ≤ 1 / 2)
    {q : ℝ → ℝ → W}
    (hq : ContDiffOn ℝ ∞ (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hper : ∀ t ∈ Icc 0 T, Function.Periodic (q t) L)
    (hguard : ∀ t ∈ Icc 0 T, ∀ x, q t x ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t x) (deriv (q t) x) ≠ 0)
    (hfixed : ∀ t ∈ Icc 0 T, ∀ x, q t x = e (ρ (q t x)))
    (htime : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => q s x)
      (ambientCurvePrincipal F ρ (a + t) (q t x) (deriv (q t) x) •
          deriv (deriv (q t)) x +
        ambientCurveLower F e ρ (a + t) (q t x) (deriv (q t) x)) t) :
    let A := fun t x => ambientCurvePrincipal F ρ (a + t) (q t x) (deriv (q t) x)
    ∃ ψ : ℝ → ℝ → ℝ, (∀ x, ψ 0 x = x) ∧
      (∀ t ∈ Icc 0 S, ∀ x, ψ t (x + L) = ψ t x + L) ∧
      ContDiffOn ℝ ∞ (Function.uncurry ψ) (Icc 0 S ×ˢ univ) ∧
      (∀ t ∈ Icc 0 S, ∀ x, HasDerivWithinAt (fun s => ψ s x)
        (deriv (A t) (ψ t x) / 2) (Icc 0 S) t) ∧
      (∀ t ∈ Icc 0 S, ∀ x, 0 < deriv (ψ t) x) ∧
      (∀ t ∈ Icc 0 S, Function.Bijective (ψ t)) ∧
      let c := fun x t => ρ (q (t - a) (ψ (t - a) ((L / curvePeriod) * x)))
      M63SmoothShrinkingCurveOn F c (Icc a (a + S)) ∧
        (∀ x, c x a = ρ (q 0 ((L / curvePeriod) * x))) ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
          (fun z : ℝ × ℝ => c z.1 z.2) (univ ×ˢ Icc a (a + S)) := by
  classical
  let A := fun t x => ambientCurvePrincipal F ρ (a + t) (q t x) (deriv (q t) x)
  let w := fun t x => deriv (A t) x / 2
  obtain ⟨hw, hwper⟩ := ambientCurve_labelVelocity_regular F hU hρ hT hTb hq hper hguard
  let v := fun t x => if t ∈ Icc 0 T then w t x else 0
  have hvper (t : ℝ) : Function.Periodic (v t) L := by
    intro x
    dsimp only [v]
    split_ifs with ht
    · exact hwper t ht x
    · rfl
  have hv : ContDiffOn ℝ ∞ (Function.uncurry v) (Ico 0 T ×ˢ univ) := by
    apply (hw.mono (prod_mono Ico_subset_Icc_self Subset.rfl)).congr
    intro z hz
    exact if_pos ⟨hz.1.1, hz.1.2.le⟩
  obtain ⟨ψ, hψzero, hψper, hψjoint, hψode, hψpos, hψbij⟩ :=
    exists_smooth_periodic_label_flow_on_prescribed_slab hL hT hS hST hS1 v hvper hv
  have hST' : S < T := by linarith only [hST, hT]
  have hψactual (t : ℝ) (ht : t ∈ Icc 0 S) (x : ℝ) :
      HasDerivWithinAt (fun s => ψ s x) (deriv (A t) (ψ t x) / 2) (Icc 0 S) t := by
    have hm : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hST'.le⟩
    simpa only [v, if_pos hm] using hψode t ht x
  let σ := fun x : ℝ => (L / curvePeriod) * x
  have hσ : ContDiff ℝ ∞ σ := contDiff_const.mul contDiff_id
  have hp : 0 < curvePeriod := Real.two_pi_pos
  have hκ : 0 < L / curvePeriod := div_pos hL hp
  have hσd (x : ℝ) : HasDerivAt σ (L / curvePeriod) x := by
    simpa only [σ, mul_one, id_eq] using! (hasDerivAt_id x).const_mul (L / curvePeriod)
  have hσpos (x : ℝ) : 0 < deriv σ x := by rw [(hσd x).deriv]; exact hκ
  have hσshift (x : ℝ) : σ (x + curvePeriod) = σ x + L := by
    dsimp only [σ]
    rw [mul_add, div_mul_cancel₀ _ hp.ne']
  have hc := ambientCurve_normal_solution_of_labels F he hU heU hρ hρe
    hT hTb hq hper hguard hfixed htime hσ hσpos hσshift hS hST'
      hψzero hψjoint hψper hψpos hψactual
  exact ⟨ψ, hψzero, hψper, hψjoint, hψactual, hψpos, hψbij, hc⟩

end PoincareConjecture.M63
