import PoincareConjecture.Proofs.M34.Mathlib.ParameterSpatialDerivatives
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Order.Compact










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace Real.smoothTransition



theorem one_sub_eq (x : ℝ) :
    1 - smoothTransition x = smoothTransition (1 - x) := by
  have hne := (pos_denom x).ne'
  unfold smoothTransition
  rw [show 1 - (1 - x) = x by ring, add_comm (expNegInvGlue (1 - x)) (expNegInvGlue x)]
  field_simp
  ring




theorem uniform_spatial_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) {K : Set E} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ q : ℝ, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (fun y => smoothTransition (ρ y + q)) x‖ ≤ C := by
  cases m with
  | zero =>
      refine ⟨1, le_rfl, fun q x _ => ?_⟩
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (nonneg _)] using
        le_one (ρ x + q)
  | succ m =>
      obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hρ.continuous.continuousOn
      let R := max A 0 + 2
      have hRA : A + 2 ≤ R := by dsimp [R]; linarith [le_max_left A 0]
      let f : ℝ × E → ℝ := fun p => smoothTransition (ρ p.2 + p.1)
      have hf : ContDiff ℝ ∞ f :=
        Real.smoothTransition.contDiff.comp ((hρ.comp contDiff_snd).add contDiff_fst)
      have hj : ContinuousOn
          (fun p : ℝ × E => iteratedFDeriv ℝ (m + 1) (fun y => f (p.1, y)) p.2)
          (Icc (-R) R ×ˢ K) :=
        (hf.contDiffOn.iteratedFDeriv_snd_of_isOpen (U := univ) (S := univ)
          isOpen_univ (m + 1)).continuousOn.mono (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
      obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hj
      refine ⟨max C 1, le_max_right _ _, fun q x hx => ?_⟩
      by_cases hq : q ∈ Icc (-R) R
      · exact (hC (q, x) ⟨hq, hx⟩).trans (le_max_left _ _)
      have hAx : |ρ x| ≤ A := hA x hx
      simp only [mem_Icc, not_and_or, not_le] at hq
      rcases hq with hq | hq
      · have hlt : ρ x + q < 0 := by linarith [(abs_le.mp hAx).2]
        have heq : (fun y => smoothTransition (ρ y + q)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [(isOpen_lt (hρ.continuous.add continuous_const)
            continuous_const).mem_nhds hlt] with y hy
          exact zero_of_nonpos hy.le
        rw [(heq.iteratedFDeriv (𝕜 := ℝ) (m + 1)).eq_of_nhds,
          iteratedFDeriv_const_of_ne (Nat.succ_ne_zero m), Pi.zero_apply, norm_zero]
        exact zero_le_one.trans (le_max_right _ _)
      · have hlt : 1 < ρ x + q := by linarith [(abs_le.mp hAx).1]
        have heq : (fun y => smoothTransition (ρ y + q)) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
          filter_upwards [(isOpen_lt continuous_const
            (hρ.continuous.add continuous_const)).mem_nhds hlt] with y hy
          exact one_of_one_le hy.le
        rw [(heq.iteratedFDeriv (𝕜 := ℝ) (m + 1)).eq_of_nhds,
          iteratedFDeriv_const_of_ne (Nat.succ_ne_zero m), Pi.zero_apply, norm_zero]
        exact zero_le_one.trans (le_max_right _ _)




theorem uniform_spatial_weight_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) {K : Set E} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ m, ∀ q : ℝ, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (fun y => smoothTransition (ρ y + q)) x‖ ≤ C ∧
      ‖iteratedFDeriv ℝ j (fun y => 1 - smoothTransition (ρ y + q)) x‖ ≤ C := by
  choose C hC hbC using fun j => uniform_spatial_jet_bound hρ hK j
  choose D hD hbD using fun j => uniform_spatial_jet_bound hρ.neg hK j
  let G := ∑ j ∈ Finset.range (m + 1), max (C j) (D j)
  have hG (j : ℕ) (hj : j ≤ m) : max (C j) (D j) ≤ G :=
    Finset.single_le_sum (fun i _ => (zero_le_one.trans (hC i)).trans (le_max_left _ _))
      (by simpa using hj)
  refine ⟨G, (hC 0).trans ((le_max_left _ _).trans (hG 0 (Nat.zero_le m))), ?_⟩
  intro j hj q x hx
  refine ⟨(hbC j q x hx).trans ((le_max_left _ _).trans (hG j hj)), ?_⟩
  have heq : (fun y => 1 - smoothTransition (ρ y + q)) =
      fun y => smoothTransition (-ρ y + (1 - q)) := by
    funext y
    rw [one_sub_eq]
    congr 1
    ring
  rw [heq]
  exact (hbD j (1 - q) x hx).trans ((le_max_right _ _).trans (hG j hj))

end Real.smoothTransition
