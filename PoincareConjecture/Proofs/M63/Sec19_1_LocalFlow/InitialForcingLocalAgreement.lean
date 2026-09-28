import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothInitialForcing
import PoincareConjecture.Proofs.M63.Mathlib.CompactParameterNeighborhood

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M63

open SpectralHeatNative QuasilinearDeTurckNative DeTurckMetricProducerNative

theorem initialForcing_eventuallyEq_of_coefficients
    {iota E : Type*} [Countable iota] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lambda : iota → NNReal) {T : ℝ} (hT : 0 ≤ T)
    (M : E →L[ℝ] State iota →L[ℝ] State iota)
    (G1 G2 : ℝ × State iota → E) (Q1 Q2 : ℝ × State iota → State iota)
    (R1 R2 : State iota × ForcingSpace iota T → ForcingSpace iota T)
    (hR1 : ∀ w F, ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      R1 (w, F) t =
        M (G1 (t, initialResponseTrace lambda w hT F ⟨t, ht⟩))
          (initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t -
            shiftedBaseMultiplier lambda (initialResponseTrace lambda w hT F ⟨t, ht⟩)) +
          Q1 (t, initialResponseTrace lambda w hT F ⟨t, ht⟩))
    (hR2 : ∀ w F, ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      R2 (w, F) t =
        M (G2 (t, initialResponseTrace lambda w hT F ⟨t, ht⟩))
          (initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t -
            shiftedBaseMultiplier lambda (initialResponseTrace lambda w hT F ⟨t, ht⟩)) +
          Q2 (t, initialResponseTrace lambda w hT F ⟨t, ht⟩))
    (w : State iota) (F0 : ForcingSpace iota T) {O : Set (ℝ × State iota)}
    (hO : IsOpen O)
    (htrace : ∀ t : Icc (0 : ℝ) T, ((t : ℝ), initialResponseTrace lambda w hT F0 t) ∈ O)
    (heq : ∀ t u, 0 ≤ t → (t, u) ∈ O → G1 (t, u) = G2 (t, u) ∧ Q1 (t, u) = Q2 (t, u)) :
    R1 =ᶠ[𝓝 (w, F0)] R2 := by
  obtain ⟨V0, _, hV0⟩ := exists_initialHeatPath_operator lambda hT
  let S := State iota
  let X := S × ForcingSpace iota T
  let V : X →L[ℝ] ResponsePath iota T :=
    V0.comp (ContinuousLinearMap.fst ℝ S (ForcingSpace iota T)) +
      (shiftedTraceOperator hT lambda).comp (ContinuousLinearMap.snd ℝ S (ForcingSpace iota T))
  have hV (z : X) (t : Icc (0 : ℝ) T) :
      V z t = initialResponseTrace lambda z.1 hT z.2 t := by
    change V0 z.1 t + shiftedTracePath hT lambda z.2 t = _
    rw [hV0]
    rfl
  let Z : X × Icc (0 : ℝ) T → ℝ × S := fun p => ((p.2 : ℝ), V p.1 p.2)
  have hZ : Continuous Z :=
    (continuous_subtype_val.comp continuous_snd).prodMk
      (continuous_eval.comp ((V.continuous.comp continuous_fst).prodMk continuous_snd))
  obtain ⟨eps, heps, hnear⟩ := exists_uniform_open_parameter_radius (x0 := (w, F0)) hZ hO
    (fun t => by simpa only [Z, hV] using htrace t)
  filter_upwards [Metric.ball_mem_nhds (w, F0) heps] with z hz
  apply Lp.ext
  filter_upwards [hR1 z.1 z.2, hR2 z.1 z.2,
    ae_restrict_mem measurableSet_Ioc] with t h1 h2 ht
  have hmem : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hinside : (t, initialResponseTrace lambda z.1 hT z.2 ⟨t, hmem⟩) ∈ O := by
    simpa only [Z, hV] using hnear z hz ⟨t, hmem⟩
  obtain ⟨hG, hQ⟩ := heq t _ hmem.1 hinside
  rw [h1 hmem, h2 hmem, hG, hQ]

theorem contDiffAt_initialForcing_of_local_extensions
    {iota E : Type*} [Countable iota] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lambda : iota → NNReal) {T : ℝ} (hT : 0 ≤ T)
    (M : E →L[ℝ] State iota →L[ℝ] State iota)
    (G : ℝ × State iota → E) (Q : ℝ × State iota → State iota)
    (R : State iota × ForcingSpace iota T → ForcingSpace iota T)
    (hR : ∀ w F, ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      R (w, F) t =
        M (G (t, initialResponseTrace lambda w hT F ⟨t, ht⟩))
          (initialHeatHigh lambda w t + shiftedHighOperator hT lambda F t -
            shiftedBaseMultiplier lambda (initialResponseTrace lambda w hT F ⟨t, ht⟩)) +
          Q (t, initialResponseTrace lambda w hT F ⟨t, ht⟩))
    (w : State iota) (F0 : ForcingSpace iota T) {O : Set (ℝ × State iota)}
    (hO : IsOpen O)
    (htrace : ∀ t : Icc (0 : ℝ) T, ((t : ℝ), initialResponseTrace lambda w hT F0 t) ∈ O)
    (hext : ∀ k : ℕ, ∃ (Gk : ℝ × State iota → E) (Qk : ℝ × State iota → State iota),
      ContDiff ℝ k Gk ∧ ContDiff ℝ k Qk ∧
      ∀ t u, 0 ≤ t → (t, u) ∈ O → G (t, u) = Gk (t, u) ∧ Q (t, u) = Qk (t, u)) :
    ContDiffAt ℝ ∞ R (w, F0) := by
  apply contDiffAt_infty.mpr
  intro k
  obtain ⟨Gk, Qk, hGk, hQk, heq⟩ := hext k
  obtain ⟨Rk, hRk, hrep⟩ := exists_contDiff_initialForcing lambda hT M Gk Qk hGk hQk
  exact hRk.contDiffAt.congr_of_eventuallyEq
    (initialForcing_eventuallyEq_of_coefficients lambda hT M G Gk Q Qk R Rk
      hR hrep w F0 hO htrace heq)

end PoincareConjecture.M63
