import PoincareConjecture.Proofs.M36.ComparisonSmoothJets
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Operations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.M36

theorem radialNeckWeight_support_geometry (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ∈ tsupport (radialNeckWeight g₀)) :
    x ≠ 0 ∧ standardSurgeryHeight g₀ x < 2 := by
  have hrad := radialNeckWeight_tsupport g₀ hx
  have hheight : standardSurgeryHeight g₀ x ≤ 7 / 4 := by
    change g₀.cylindrical_end.radius + 4 - 7 / 4 ≤ radialArclength g₀ ‖x‖ at hrad
    unfold standardSurgeryHeight
    linarith only [hrad]
  refine ⟨?_, by linarith only [hheight]⟩
  intro hz
  rw [hz, standardSurgeryHeight_zero] at hheight
  linarith [g₀.cylindrical_end.radius_pos]

set_option maxHeartbeats 800000 in
theorem exists_radialWeightedError_jet_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g₀ : StandardInitialMetric) (C q : ℝ) {r : ℝ} (hr : 0 < r)
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ epsilon : ℝ, epsilon ∈ Set.Icc (0 : ℝ) 1 →
      ∀ B : StandardCapSpace → F,
      (∀ x ∈ K ∩ tsupport (radialNeckWeight g₀), ContDiffAt ℝ ∞ B x) →
      ∀ b : ℝ, 0 ≤ b →
      (∀ k : ℕ, k ≤ m → ∀ x ∈ K ∩ tsupport (radialNeckWeight g₀),
        ‖iteratedFDeriv ℝ k B x‖ ≤ b) →
      ∀ k : ℕ, k ≤ m → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ k (fun y =>
          (radialConformalMultiplier g₀ C q epsilon r y * radialNeckWeight g₀ y) • B y) x‖ ≤
            A * b := by
  let f : ℝ → StandardCapSpace → ℝ := fun e y =>
    radialConformalMultiplier g₀ C q e r y * radialNeckWeight g₀ y
  have hf : ContDiff ℝ ∞ (Function.uncurry f) :=
    (radialConformalMultiplier_joint_contDiff g₀ C q hr).mul
      ((radialNeckWeight_contDiff g₀).comp contDiff_snd)
  obtain ⟨A, hA, hbound⟩ := exists_parametric_jet_bound hf
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)) hK m
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  refine ⟨2 ^ m * A,
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hA, ?_⟩
  intro epsilon hepsilon B hB b hb hBbound k hk x hx
  by_cases hsupport : x ∈ tsupport (radialNeckWeight g₀)
  · have hfe : ContDiff ℝ ∞ (f epsilon) :=
      hf.comp (f := fun y : StandardCapSpace => (epsilon, y))
        (contDiff_const.prodMk contDiff_id)
    calc
      _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j (f epsilon) x‖ * ‖iteratedFDeriv ℝ (k - j) B x‖ :=
        Poincare.Analysis.Calculus.norm_iteratedFDeriv_smul_le_of_contDiffAt
          hfe.contDiffAt (hB x ⟨hx, hsupport⟩) k
      _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * A * b := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hbound epsilon hepsilon j (hjk.trans hk) x hx)
            (Nat.cast_nonneg _))
          (hBbound (k - j) ((Nat.sub_le _ _).trans hk) x ⟨hx, hsupport⟩)
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA0)
      _ = 2 ^ k * A * b := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have hsum : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = (2 : ℝ) ^ k := by
          exact_mod_cast Nat.sum_range_choose k
        rw [hsum]
      _ ≤ (2 ^ m * A) * b := by gcongr <;> norm_num
  · have heq : (fun y => f epsilon y • B y) =ᶠ[nhds x] fun _ => (0 : F) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hsupport] with y hy
      simp only [Pi.zero_apply] at hy
      simp [f, hy]
    change ‖iteratedFDeriv ℝ k (fun y => f epsilon y • B y) x‖ ≤ _
    rw [(heq.iteratedFDeriv ℝ k).self_of_nhds]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    positivity

end PoincareConjecture.M36
