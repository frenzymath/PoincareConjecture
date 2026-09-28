import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.NonlinearSchwartz

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped ContDiff SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Z" => EuclideanSpace ℝ (Fin m)

private theorem schwartz_toLp_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X Y : 𝓢(V, F)) :
    (X - Y).toLp 2 volume = X.toLp 2 volume - Y.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℝ F 2 (volume : Measure V)).map_sub X Y

private theorem schwartz_partial_toLp_sub
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X Y : 𝓢(V, F)) (v : V) :
    (∂_{v} (X - Y)).toLp 2 volume = (∂_{v} X).toLp 2 volume - (∂_{v} Y).toLp 2 volume :=
  ((SchwartzMap.toLpCLM ℝ F 2 (volume : Measure V)).comp
    (LineDeriv.lineDerivOpCLM ℝ 𝓢(V, F) v)).map_sub X Y

theorem nonlinearTestSchwartz_value_cauchy
    (T : V × Z → ℝ) (hT : ContDiff ℝ ∞ T) (hT0 : ∀ x, T (x, 0) = 0)
    (X : ℕ → 𝓢(V, Z)) (hc : ∀ k, HasCompactSupport (X k))
    {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ x z w, ‖T (x, z) - T (x, w)‖ ≤ C * ‖z - w‖)
    (hX : CauchySeq (fun k => (X k).toLp 2 volume)) :
    CauchySeq (fun k => (nonlinearTestSchwartz T hT hT0 (X k) (hc k)).toLp 2 volume) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hX (ε / (C + 1)) (by positivity)
  refine ⟨N, ?_⟩
  intro i hi j hj
  have hb := nonlinearTestSchwartz_value_norm_le T hT hT0 (X i) (X j) (hc i) (hc j) hLip
  simp only [schwartz_toLp_sub] at hb
  have hd := hN i hi j hj
  rw [dist_eq_norm] at hd ⊢
  have hs := (lt_div_iff₀ (show 0 < C + 1 by positivity)).mp hd
  have hn := norm_nonneg ((X i).toLp 2 volume - (X j).toLp 2 volume)
  nlinarith only [hb, hs, hn]

theorem nonlinearTestSchwartz_partial_cauchy
    (T : V × Z → ℝ) (hT : ContDiff ℝ ∞ T) (hT0 : ∀ x, T (x, 0) = 0)
    (X : ℕ → 𝓢(V, Z)) (hc : ∀ k, HasCompactSupport (X k)) (v : V)
    {C : ℝ} (hC : 0 ≤ C)
    (hspace : ∀ x z w, ‖nonlinearSpaceJet T x z v - nonlinearSpaceJet T x w v‖ ≤
      C * ‖z - w‖)
    (hval : ∀ x z, ‖nonlinearValueJet T x z‖ ≤ C)
    (hvalLip : ∀ x z w, ‖nonlinearValueJet T x z - nonlinearValueJet T x w‖ ≤ C * ‖z - w‖)
    (hX : CauchySeq (fun k => (X k).toLp 2 volume))
    (hdX : CauchySeq (fun k => (∂_{v} (X k)).toLp 2 volume)) :
    CauchySeq (fun k => (∂_{v} (nonlinearTestSchwartz T hT hT0 (X k) (hc k))).toLp 2 volume) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := Metric.cauchySeq_iff.mp hdX ((ε / 3) / (2 * C + 1)) (by positivity)
  let B : ℝ := SchwartzMap.seminorm ℝ 0 0 (∂_{v} (X k))
  have hB : 0 ≤ B := apply_nonneg _ _
  have hW (x : V) : ‖fderiv ℝ (X k) x v‖ ≤ B :=
    SchwartzMap.norm_le_seminorm ℝ (∂_{v} (X k)) x
  let A : ℝ := C * (1 + B)
  have hA : 0 ≤ A := mul_nonneg hC (by positivity)
  obtain ⟨N₀, hN₀⟩ := Metric.cauchySeq_iff.mp hX ((ε / 3) / (A + 1)) (by positivity)
  obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.mp hdX ((ε / 3) / (C + 1)) (by positivity)
  refine ⟨max k (max N₀ N₁), ?_⟩
  intro i hi j hj
  have hjk : k ≤ j := (le_max_left _ _).trans hj
  have hi0 : N₀ ≤ i := (le_max_left _ _).trans ((le_max_right _ _).trans hi)
  have hj0 : N₀ ≤ j := (le_max_left _ _).trans ((le_max_right _ _).trans hj)
  have hi1 : N₁ ≤ i := (le_max_right _ _).trans ((le_max_right _ _).trans hi)
  have hj1 : N₁ ≤ j := (le_max_right _ _).trans ((le_max_right _ _).trans hj)
  have h0 := hN₀ i hi0 j hj0
  have h1 := hN₁ i hi1 j hj1
  have h2 := hk j hjk k le_rfl
  simp only [dist_eq_norm] at h0 h1 h2 ⊢
  have hb0 : A * ‖(X i).toLp 2 volume - (X j).toLp 2 volume‖ < ε / 3 := by
    have h := (lt_div_iff₀ (show 0 < A + 1 by positivity)).mp h0
    nlinarith only [h, norm_nonneg ((X i).toLp 2 volume - (X j).toLp 2 volume)]
  have hb1 : C * ‖(∂_{v} (X i)).toLp 2 volume - (∂_{v} (X j)).toLp 2 volume‖ < ε / 3 := by
    have h := (lt_div_iff₀ (show 0 < C + 1 by positivity)).mp h1
    nlinarith only [h, norm_nonneg
      ((∂_{v} (X i)).toLp 2 volume - (∂_{v} (X j)).toLp 2 volume)]
  have hb2 : (2 * C) *
      ‖(∂_{v} (X j)).toLp 2 volume - (∂_{v} (X k)).toLp 2 volume‖ < ε / 3 := by
    have h := (lt_div_iff₀ (show 0 < 2 * C + 1 by positivity)).mp h2
    nlinarith only [h, norm_nonneg
      ((∂_{v} (X j)).toLp 2 volume - (∂_{v} (X k)).toLp 2 volume)]
  have hb := nonlinearTestSchwartz_partial_norm_le T hT hT0 (X i) (X j) (X k)
    (hc i) (hc j) v hC hB hspace hval hvalLip hW
  simp only [schwartz_partial_toLp_sub, schwartz_toLp_sub] at hb
  change _ ≤ A * _ + _ + _ at hb
  linarith only [hb, hb0, hb1, hb2]

end PoincareConjecture.M35.Uniqueness.Heat
