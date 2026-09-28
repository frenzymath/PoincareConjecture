import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Graph.Estimates








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

variable {n : ℕ} {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
  {F : ℝ × N → ℝ} {V : Set (ℝ × N)}


theorem exists_unique_smooth_level_height_on
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F V)
    {ε : ℝ} (hε : 0 < ε) (hslab : Icc (-ε) ε ×ˢ (univ : Set N) ⊆ V)
    (hpos : ∀ y : N, ∀ s ∈ Ioo (-ε) ε, 0 < deriv (fun r => F (r, y)) s)
    (hleft : ∀ y : N, F (-ε, y) < 0) (hright : ∀ y : N, 0 < F (ε, y)) :
    ∃ u : N → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u ∧
      (∀ y, u y ∈ Ioo (-ε) ε ∧ F (u y, y) = 0) ∧
      ∀ y s, s ∈ Ioo (-ε) ε → (F (s, y) = 0 ↔ s = u y) := by
  have hcont (y : N) : ContinuousOn (fun s : ℝ => F (s, y)) (Icc (-ε) ε) := by
    apply hF.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
    intro s hs
    exact hslab ⟨hs, mem_univ y⟩
  have hmono (y : N) : StrictMonoOn (fun s => F (s, y)) (Icc (-ε) ε) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (hcont y)
    simpa only [interior_Icc] using hpos y
  have hex (y : N) : ∃ s ∈ Ioo (-ε) ε, F (s, y) = 0 := by
    obtain ⟨s, hs, hz⟩ := intermediate_value_Icc (by linarith : -ε ≤ ε)
      (hcont y) ⟨(hleft y).le, (hright y).le⟩
    change F (s, y) = 0 at hz
    refine ⟨s, ⟨?_, ?_⟩, hz⟩
    · exact lt_of_le_of_ne hs.1 (by intro he; have := hleft y; rw [he, hz] at this; exact this.false)
    · exact lt_of_le_of_ne hs.2 (by intro he; have := hright y; rw [← he, hz] at this; exact this.false)
  choose u hu hz using hex
  refine ⟨u, ?_, fun y => ⟨hu y, hz y⟩, ?_⟩
  · intro y
    apply contMDiffAt_of_unique_time_root isOpen_Ioo isOpen_univ
      (hF.mono (fun p hp => hslab ⟨Ioo_subset_Icc_self hp.1, hp.2⟩))
      (σ := u) (v := deriv (fun r => F (r, y)) (u y))
      (fun z _ => ⟨hu z, hz z⟩)
      (fun z _ => (hmono z).injOn.mono Ioo_subset_Icc_self) (mem_univ y)
      (hpos y _ (hu y)).ne'
    exact (differentiableAt_of_deriv_ne_zero (hpos y _ (hu y)).ne').hasDerivAt
  · intro y s hs
    constructor
    · intro hzero
      exact (hmono y).injOn (Ioo_subset_Icc_self hs) (Ioo_subset_Icc_self (hu y))
        (hzero.trans (hz y).symm)
    · rintro rfl
      exact hz y

omit [IsManifold (𝓡 n) ∞ N] in

theorem level_height_mvfderiv_on
    (hV : IsOpen V)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F V)
    {u : N → ℝ} (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hmem : ∀ y, (u y, y) ∈ V) (hzero : ∀ y, F (u y, y) = 0)
    (y : N) (hne : deriv (fun r => F (r, y)) (u y) ≠ 0)
    (v : EuclideanSpace ℝ (Fin n)) :
    mvfderiv (𝓡 n) u y v =
      -(mvfderiv (𝓡 n) (fun z => F (u y, z)) y v) /
        deriv (fun r => F (r, y)) (u y) := by
  have hdF := (hF.contMDiffAt (hV.mem_nhds (hmem y))).mdifferentiableAt (by simp)
  have hdu := (hu y).mdifferentiableAt (by simp)
  have hd := mvfderiv_comp (f := fun z => (u z, z)) (g := F) y hdF
    (hdu.prodMk mdifferentiableAt_id)
  change mvfderiv (𝓡 n) (fun z => F (u z, z)) y = _ at hd
  have hconst : (fun z => F (u z, z)) = fun _ => (0 : ℝ) := funext hzero
  rw [hconst, mvfderiv_const] at hd
  have hv := congrArg (fun L => L v) hd
  have hg := mfderiv_prodMk hdu mdifferentiableAt_id
  simp only [id_eq] at hg
  rw [hg, mfderiv_id] at hv
  change (0 : ℝ) = mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) F (u y, y)
    (mvfderiv (𝓡 n) u y v, v) at hv
  rw [mfderiv_prod_eq_add_apply hdF, mfderiv_eq_fderiv] at hv
  change 0 = fderiv ℝ (fun r => F (r, y)) (u y) (mvfderiv (𝓡 n) u y v) +
    mvfderiv (𝓡 n) (fun z => F (u y, z)) y v at hv
  rw [fderiv_eq_deriv_mul] at hv
  apply (eq_div_iff hne).mpr
  linarith



theorem exists_level_height_with_C1_bounds_on
    (hV : IsOpen V)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F V)
    {ε δ η : ℝ} (hε : 0 < ε) (hδ : δ < ε)
    (hslab : Icc (-ε) ε ×ˢ (univ : Set N) ⊆ V)
    (ν : N → EuclideanSpace ℝ (Fin n) → ℝ)
    (hvalue : ∀ y : N, ∀ s ∈ Icc (-ε) ε, |F (s, y) - s| ≤ δ)
    (hvertical : ∀ y : N, ∀ s ∈ Ioo (-ε) ε,
      (1 / 2 : ℝ) ≤ deriv (fun r => F (r, y)) s)
    (hhorizontal : ∀ y : N, ∀ s ∈ Ioo (-ε) ε, ∀ v : EuclideanSpace ℝ (Fin n),
      |mvfderiv (𝓡 n) (fun z => F (s, z)) y v| ≤ η * ν y v) :
    ∃ u : N → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u ∧
      (∀ y, u y ∈ Ioo (-ε) ε ∧ F (u y, y) = 0) ∧
      (∀ y s, s ∈ Ioo (-ε) ε → (F (s, y) = 0 ↔ s = u y)) ∧
      (∀ y, |u y| ≤ δ) ∧
      ∀ (y : N) (v : EuclideanSpace ℝ (Fin n)),
        |mvfderiv (𝓡 n) u y v| ≤ (2 * η) * ν y v := by
  have hleft (y : N) : F (-ε, y) < 0 := by
    have h := (abs_le.mp (hvalue y (-ε) ⟨le_rfl, by linarith⟩)).2
    linarith
  have hright (y : N) : 0 < F (ε, y) := by
    have h := (abs_le.mp (hvalue y ε ⟨by linarith, le_rfl⟩)).1
    linarith
  obtain ⟨u, hu, hroot, huniq⟩ := exists_unique_smooth_level_height_on hF hε hslab
    (fun y s hs => lt_of_lt_of_le (by norm_num) (hvertical y s hs)) hleft hright
  refine ⟨u, hu, hroot, huniq, ?_, ?_⟩
  · intro y
    simpa only [(hroot y).2, zero_sub, abs_neg] using
      hvalue y (u y) (Ioo_subset_Icc_self (hroot y).1)
  · intro y v
    have hden := hvertical y (u y) (hroot y).1
    have hp : 0 < deriv (fun r => F (r, y)) (u y) := by linarith
    rw [level_height_mvfderiv_on hV hF hu
      (fun z => hslab ⟨Ioo_subset_Icc_self (hroot z).1, mem_univ z⟩)
      (fun z => (hroot z).2) y hp.ne' v, abs_div, abs_neg, abs_of_pos hp]
    have h := (div_le_div_of_nonneg_left (abs_nonneg
      (mvfderiv (𝓡 n) (fun z => F (u y, z)) y v))
      (by norm_num : (0 : ℝ) < 1 / 2) hden).trans
      (div_le_div_of_nonneg_right (hhorizontal y (u y) (hroot y).1 v)
        (by norm_num : (0 : ℝ) ≤ 1 / 2))
    calc
      _ ≤ η * ν y v / (1 / 2) := h
      _ = (2 * η) * ν y v := by ring

end Poincare.Manifold
