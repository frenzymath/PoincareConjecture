import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryArc
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryEstimate
import Mathlib.Topology.MetricSpace.Equicontinuity












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric Filter Complex
open scoped Topology

universe u

namespace PoincareConjecture

private theorem m65Jordan_inverse_modulus {N : ℕ}
    (Γ : LoopCircle → EuclideanSpace ℝ (Fin N))
    (hΓ : Continuous Γ) (hinj : Function.Injective Γ) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x y : LoopCircle, ‖Γ x - Γ y‖ < δ → dist x y < η := by
  let E := (hΓ.isClosedEmbedding hinj).isEmbedding.toHomeomorph
  let : CompactSpace (range Γ) := E.compactSpace
  have hu := CompactSpace.uniformContinuous_of_continuous E.symm.continuous
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hu η hη
  refine ⟨δ, hδ, fun x y hxy => ?_⟩
  have hdist : dist (E x) (E y) < δ := by
    change dist (Γ x) (Γ y) < δ
    rwa [dist_eq_norm]
  simpa only [Homeomorph.symm_apply_apply] using
    hd (a := E x) (b := E y) hdist

private theorem m65Logarithmic_scale (B : ℝ) {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∃ ε, 0 < ε ∧ ε < R ∧ 2 * Real.pi * B < η ^ 2 * Real.log (R / ε) := by
  let K := 2 * Real.pi * (max B 0 + 1) / η ^ 2 + 1
  have hBpos : 0 < max B 0 + 1 := by linarith [le_max_right B 0]
  have hK : 0 < K := by dsimp only [K]; positivity
  let ε := R / Real.exp K
  have hε : 0 < ε := div_pos hR (Real.exp_pos _)
  have hεR : ε < R := (div_lt_self hR (Real.one_lt_exp_iff.mpr hK))
  have hratio : R / ε = Real.exp K := by dsimp only [ε]; field_simp
  have hprod : η ^ 2 * K = 2 * Real.pi * (max B 0 + 1) + η ^ 2 := by
    dsimp only [K]
    field_simp
  refine ⟨ε, hε, hεR, ?_⟩
  rw [hratio, Real.log_exp, hprod]
  nlinarith [le_max_left B 0, Real.pi_pos, sq_pos_of_pos hη]

private theorem m65Complex_pin_separation (c : ℂ) (hc : c = I ∨ c = -I) :
    ∀ i j : Fin 3, i ≠ j → 1 ≤ ‖(![1, -1, c] : Fin 3 → ℂ) i - ![1, -1, c] j‖ := by
  rcases hc with rfl | rfl <;> intro i j hij <;> fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | norm_num [Complex.norm_def, Complex.normSq_apply]

private theorem m65Normalized_pin_data {M : Type u} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : M65WeakDisk e γ) {a b c : LoopCircle} (hF : F.Normalized a b c) :
    ∃ p : Fin 3 → LoopCircle, (∀ i j : Fin 3, i ≠ j → 1 ≤ dist (p i) (p j)) ∧
      ∀ i, F.parameter (p i) = (![a, b, c] : Fin 3 → LoopCircle) i := by
  let p : LoopCircle := ⟨orthonormalBasisOneI.repr 1, by simp⟩
  let n : LoopCircle := ⟨orthonormalBasisOneI.repr (-1), by simp⟩
  let ip : LoopCircle := ⟨orthonormalBasisOneI.repr I, by simp⟩
  let im : LoopCircle := ⟨orthonormalBasisOneI.repr (-I), by simp⟩
  change F.parameter p = a ∧ F.parameter n = b ∧
    (F.parameter ip = c ∨ F.parameter im = c) at hF
  obtain ⟨ha, hb, hc⟩ := hF
  rcases hc with hc | hc
  · refine ⟨![p, n, ip], ?_, ?_⟩
    · intro i j hij
      have hp (k : Fin 3) : ((![p, n, ip] : Fin 3 → LoopCircle) k : LoopPlane) =
          orthonormalBasisOneI.repr ((![1, -1, I] : Fin 3 → ℂ) k) := by fin_cases k <;> rfl
      rw [Subtype.dist_eq, hp i, hp j]
      rw [LinearIsometryEquiv.dist_map, dist_eq_norm]
      exact m65Complex_pin_separation I (Or.inl rfl) i j hij
    · intro i
      fin_cases i <;> assumption
  · refine ⟨![p, n, im], ?_, ?_⟩
    · intro i j hij
      have hp (k : Fin 3) : ((![p, n, im] : Fin 3 → LoopCircle) k : LoopPlane) =
          orthonormalBasisOneI.repr ((![1, -1, -I] : Fin 3 → ℂ) k) := by fin_cases k <;> rfl
      rw [Subtype.dist_eq, hp i, hp j]
      rw [LinearIsometryEquiv.dist_map, dist_eq_norm]
      exact m65Complex_pin_separation (-I) (Or.inr rfl) i j hij
    · intro i
      fin_cases i <;> assumption

set_option maxHeartbeats 1200000 in






theorem m65NormalizedWeakDisks_boundary_equicontinuous
    {M : Type u} [TopologicalSpace M] {N : ℕ} {ι : Type*}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : ι → M65WeakDisk e γ) (he : Continuous e) (hγ : Continuous γ)
    (hJordan : Function.Injective (e ∘ γ))
    {a b c : LoopCircle} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpin : ∀ i, (F i).Normalized a b c) (B : ℝ)
    (hB : ∀ i, ‖(F i).derivative 0‖ ^ 2 + ‖(F i).derivative 1‖ ^ 2 ≤ B) :
    Equicontinuous (fun i z => (F i).parameter z) := by
  intro z
  apply Metric.equicontinuousAt_iff_right.mpr
  intro η hη
  have hq : Function.Injective (![a, b, c] : Fin 3 → LoopCircle) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨δ, hδ, hcontrol⟩ := m65ThreePin_weak_arc_modulus ![a, b, c] hq hη
  obtain ⟨ξ, hξ, hinverse⟩ := m65Jordan_inverse_modulus (e ∘ γ) (he.comp hγ) hJordan hδ
  obtain ⟨ε, hε, hεR, hlog⟩ := m65Logarithmic_scale B (R := 1 / 4) (by norm_num) hξ
  have hε1 : ε ≤ 1 := by linarith
  have hdε := (m65CrosscutBoundaryWidth_bounds hε hε1).1
  obtain ⟨α, hα⟩ := m65LoopAngular_continuous_surjective.2 z
  let U := m65LoopAngular '' Ioo (α - m65CrosscutBoundaryWidth ε) (α + m65CrosscutBoundaryWidth ε)
  have hU : IsOpen U := m65LoopAngular_open _ isOpen_Ioo
  have hzU : z ∈ U := ⟨α, ⟨by linarith, by linarith⟩, hα⟩
  filter_upwards [hU.mem_nhds hzU] with y hy
  intro i
  obtain ⟨v, hv, rfl⟩ := hy
  let θ := α - Real.pi
  have hθ : θ + Real.pi = α := by dsimp only [θ]; ring
  have hbudget : 2 * Real.pi * (‖(F i).derivative 0‖ ^ 2 + ‖(F i).derivative 1‖ ^ 2) <
      ξ ^ 2 * Real.log ((1 / 4) / ε) :=
    (mul_le_mul_of_nonneg_left (hB i) (by positivity)).trans_lt hlog
  obtain ⟨r, hr, hgap⟩ := m65WeakDisk_boundary_courantLebesgue (F i) he hγ θ
    hε hεR (by norm_num : (1 / 4 : ℝ) ≤ 1) hbudget
  have hrpos : 0 < r := hε.trans_le hr.1
  have hr1 : r ≤ 1 := by linarith [hr.2]
  let d := m65CrosscutBoundaryWidth r
  let s := fun t => m65LoopAngular (θ + Real.pi + t)
  obtain ⟨hs, hsi, hleft, hright⟩ := m65CrosscutBoundaryArc_endpoints θ hrpos hr1
  have hdpos : 0 < d := (m65CrosscutBoundaryWidth_bounds hrpos hr1).1
  have hsub : m65CrosscutBoundaryWidth ε ≤ d := m65CrosscutBoundaryWidth_mono hr.1
  have hend : dist ((F i).parameter (s (-d))) ((F i).parameter (s d)) < δ := by
    apply hinverse
    change s (-d) = _ at hleft
    change s d = _ at hright
    rw [hleft, hright]
    exact (sq_lt_sq₀ (norm_nonneg _) hξ.le).mp hgap
  obtain ⟨p, hpsep, hpmap⟩ := m65Normalized_pin_data (F i) (hpin i)
  have hdiam : ∀ x ∈ Icc (-d) d, ∀ y ∈ Icc (-d) d, dist (s x) (s y) < 1 := by
    intro x hx y hy
    have hx' := m65CrosscutBoundaryArc_dist_center θ hrpos hr1 hx
    have hy' := m65CrosscutBoundaryArc_dist_center θ hrpos hr1 hy
    have htri := dist_triangle (s x) (m65LoopAngular (θ + Real.pi)) (s y)
    rw [dist_comm (m65LoopAngular (θ + Real.pi)) (s y)] at htri
    change dist (s x) (m65LoopAngular (θ + Real.pi)) ≤ r at hx'
    change dist (s y) (m65LoopAngular (θ + Real.pi)) ≤ r at hy'
    linarith [hr.2]
  have hz : s 0 = z := by dsimp only [s]; rw [hθ, add_zero, hα]
  have hyv : s (v - α) = m65LoopAngular v := by
    dsimp only [s]
    rw [hθ]
    congr 1
    ring
  have h0 : (0 : ℝ) ∈ Icc (-d) d := ⟨by linarith, hdpos.le⟩
  have hv' : v - α ∈ Icc (-d) d := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hfinal := hcontrol (F i).parameter (F i).weakly_monotone p hpsep hpmap s (-d) d
    (by linarith) hs.continuousOn hsi hdiam hend 0 h0 (v - α) hv'
  rwa [hz, hyv] at hfinal

end PoincareConjecture
