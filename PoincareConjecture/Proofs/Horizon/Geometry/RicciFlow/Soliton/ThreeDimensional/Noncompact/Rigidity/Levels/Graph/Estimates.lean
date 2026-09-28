import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Graph









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

private theorem abs_root_le_div_of_deriv_lower
    {f : ℝ → ℝ} {ε c s : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hf : ContinuousOn f (Ioo (-ε) ε))
    (hder : ∀ r ∈ Ioo (-ε) ε, c ≤ deriv f r)
    (hs : s ∈ Ioo (-ε) ε) (hzero : f s = 0) : |s| ≤ |f 0| / c := by
  have hdiff : DifferentiableOn ℝ f (interior (Ioo (-ε) ε)) := by
    intro r hr
    exact (differentiableAt_of_deriv_ne_zero
      (hc.trans_le (hder r (interior_subset hr))).ne').differentiableWithinAt
  have hlow : ∀ r ∈ interior (Ioo (-ε) ε), c ≤ deriv f r :=
    fun r hr ↦ hder r (interior_subset hr)
  have hz : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  apply (le_div_iff₀ hc).mpr
  by_cases hs0 : 0 ≤ s
  · have h := (convex_Ioo (-ε) ε).mul_sub_le_image_sub_of_le_deriv
      hf hdiff hlow 0 hz s hs hs0
    rw [hzero] at h
    rw [abs_of_nonneg hs0]
    nlinarith [neg_le_abs (f 0)]
  · have h := (convex_Ioo (-ε) ε).mul_sub_le_image_sub_of_le_deriv
      hf hdiff hlow s hs 0 hz (le_of_not_ge hs0)
    rw [hzero] at h
    rw [abs_of_neg (lt_of_not_ge hs0)]
    nlinarith [le_abs_self (f 0)]

variable {n : ℕ} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
  {F : ℝ × N → ℝ}
  (hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F)

include hF

omit [IsManifold (𝓡 n) ∞ N] in


theorem level_height_abs_le
    {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hder : ∀ y : N, ∀ s ∈ Ioo (-ε) ε, c ≤ deriv (fun r ↦ F (r, y)) s)
    {u : N → ℝ} (hroot : ∀ y, u y ∈ Ioo (-ε) ε ∧ F (u y, y) = 0)
    (y : N) : |u y| ≤ |F (0, y)| / c :=
  abs_root_le_div_of_deriv_lower hε hc
    (hF.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    (hder y) (hroot y).1 (hroot y).2

omit [IsManifold (𝓡 n) ∞ N] in

theorem level_height_mvfderiv
    {u : N → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hzero : ∀ y, F (u y, y) = 0) (y : N)
    (hne : deriv (fun r ↦ F (r, y)) (u y) ≠ 0)
    (v : EuclideanSpace ℝ (Fin n)) :
    mvfderiv (𝓡 n) u y v =
      -(mvfderiv (𝓡 n) (fun z ↦ F (u y, z)) y v) /
        deriv (fun r ↦ F (r, y)) (u y) := by
  have hdF := (hF (u y, y)).mdifferentiableAt (by simp)
  have hdu := (hu y).mdifferentiableAt (by simp)
  have hd := mvfderiv_comp (f := fun z ↦ (u z, z)) (g := F) y hdF
    (hdu.prodMk mdifferentiableAt_id)
  change mvfderiv (𝓡 n) (fun z ↦ F (u z, z)) y = _ at hd
  have hconst : (fun z ↦ F (u z, z)) = fun _ ↦ (0 : ℝ) := funext hzero
  rw [hconst, mvfderiv_const] at hd
  have hv := congrArg (fun L ↦ L v) hd
  have hg := mfderiv_prodMk hdu mdifferentiableAt_id
  simp only [id_eq] at hg
  rw [hg, mfderiv_id] at hv
  change (0 : ℝ) = mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) F (u y, y)
    (mvfderiv (𝓡 n) u y v, v) at hv
  rw [mfderiv_prod_eq_add_apply hdF, mfderiv_eq_fderiv] at hv
  change 0 = fderiv ℝ (fun r ↦ F (r, y)) (u y) (mvfderiv (𝓡 n) u y v) +
    mvfderiv (𝓡 n) (fun z ↦ F (u y, z)) y v at hv
  rw [fderiv_eq_deriv_mul] at hv
  apply (eq_div_iff hne).mpr
  linarith

omit [IsManifold (𝓡 n) ∞ N] in


theorem level_height_mvfderiv_abs_le
    {u : N → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hzero : ∀ y, F (u y, y) = 0) {c B : ℝ} (hc : 0 < c)
    (y : N) (v : EuclideanSpace ℝ (Fin n))
    (hvertical : c ≤ deriv (fun r ↦ F (r, y)) (u y))
    (hhorizontal : |mvfderiv (𝓡 n) (fun z ↦ F (u y, z)) y v| ≤ B) :
    |mvfderiv (𝓡 n) u y v| ≤ B / c := by
  have hp := hc.trans_le hvertical
  rw [level_height_mvfderiv hF hu hzero y hp.ne' v, abs_div, abs_neg, abs_of_pos hp]
  exact (div_le_div_of_nonneg_left (abs_nonneg _) hc hvertical).trans
    (div_le_div_of_nonneg_right hhorizontal hc.le)




theorem exists_level_height_with_C1_bounds
    {ε c δ η : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (hvertical : ∀ y : N, ∀ s ∈ Ioo (-ε) ε, c ≤ deriv (fun r ↦ F (r, y)) s)
    (hleft : ∀ y : N, F (-ε, y) < 0) (hright : ∀ y : N, 0 < F (ε, y))
    (hresidual : ∀ y : N, |F (0, y)| ≤ δ)
    (hhorizontal : ∀ y : N, ∀ s ∈ Ioo (-ε) ε, ∀ v : EuclideanSpace ℝ (Fin n),
      |mvfderiv (𝓡 n) (fun z ↦ F (s, z)) y v| ≤ η * ‖v‖) :
    ∃ u : N → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u ∧
      (∀ y, u y ∈ Ioo (-ε) ε ∧ F (u y, y) = 0) ∧
      (∀ y s, s ∈ Ioo (-ε) ε → (F (s, y) = 0 ↔ s = u y)) ∧
      (∀ y, |u y| ≤ δ / c) ∧
      ∀ (y : N) (v : EuclideanSpace ℝ (Fin n)),
        |mvfderiv (𝓡 n) u y v| ≤ (η / c) * ‖v‖ := by
  obtain ⟨u, hu, hroot, huniq⟩ := exists_unique_smooth_level_height hF hε
    (fun y s hs ↦ hc.trans_le (hvertical y s hs)) hleft hright
  refine ⟨u, hu, hroot, huniq, ?_, ?_⟩
  · intro y
    exact (level_height_abs_le hF hε hc hvertical hroot y).trans
      (div_le_div_of_nonneg_right (hresidual y) hc.le)
  · intro y v
    have h := level_height_mvfderiv_abs_le hF hu (fun z ↦ (hroot z).2) hc y v
      (hvertical y _ (hroot y).1) (hhorizontal y _ (hroot y).1 v)
    convert! h using 1
    ring

end Poincare.Manifold
