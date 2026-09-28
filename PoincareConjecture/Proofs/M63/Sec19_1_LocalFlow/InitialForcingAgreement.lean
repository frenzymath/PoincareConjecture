import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothInitialForcing









set_option autoImplicit false

open Set Filter MeasureTheory

namespace PoincareConjecture.M63.CenteredSpectralResidual

open SpectralHeatNative QuasilinearDeTurckNative




theorem exists_contDiff_forcingResidual
    {iota E : Type*} [Countable iota] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace (State iota)] [BorelSpace (State iota)]
    {lambda : iota → NNReal} {w : State iota} {T r r0 : ℝ} {k : ℕ∞}
    (N : CenteredSpectralResidual lambda w T) (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (_hr : 0 ≤ r) (hrr0 : 2 * r ≤ r0)
    (M : E →L[ℝ] State iota →L[ℝ] State iota)
    (G : ℝ × State iota → E) (Q : ℝ × State iota → State iota)
    (hG : ContDiff ℝ k G) (hQ : ContDiff ℝ k Q)
    (hsource : ∀ᵐ t ∂timeMeasure T, ∀ x,
      ‖shiftedBaseMultiplier lambda x‖ ≤ r0 →
      N.toFun t x =
        M (G (t, heat lambda t.toNNReal w + shiftedBaseMultiplier lambda x))
          (initialHeatHigh lambda w t + x) +
        Q (t, heat lambda t.toNNReal w + shiftedBaseMultiplier lambda x) -
        M (G (t, heat lambda t.toNNReal w + shiftedBaseMultiplier lambda x))
          (shiftedBaseMultiplier lambda
            (heat lambda t.toNNReal w + shiftedBaseMultiplier lambda x))) :
    ∃ R : State iota × ForcingSpace iota T → ForcingSpace iota T,
      ContDiff ℝ k R ∧
      (∀ w' F, ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
        R (w', F) t =
          M (G (t, initialResponseTrace lambda w' hT F ⟨t, ht⟩))
            (initialHeatHigh lambda w' t + shiftedHighOperator hT lambda F t -
              shiftedBaseMultiplier lambda (initialResponseTrace lambda w' hT F ⟨t, ht⟩)) +
            Q (t, initialResponseTrace lambda w' hT F ⟨t, ht⟩)) ∧
      ∀ F, ‖F‖ ≤ r → R (w, F) = N.forcingResidual hT F := by
  obtain ⟨R, hR, hrep⟩ := exists_contDiff_initialForcing lambda hT M G Q hG hQ
  refine ⟨R, hR, hrep, ?_⟩
  intro F hF
  apply Lp.ext
  filter_upwards [hrep w F, N.forcingResidual_coe hT F, hsource,
    intermediate_high_eq_trace hT lambda F, intermediate_high_bound hT hT1 lambda F,
    ae_restrict_mem measurableSet_Ioc] with t hRt hNt hsourceT htrace hbound hmem
  have ht : t ∈ Icc (0 : ℝ) T := ⟨hmem.1.le, hmem.2⟩
  have hball : ‖shiftedBaseMultiplier lambda (shiftedHighOperator hT lambda F t)‖ ≤ r0 :=
    hbound.trans ((mul_le_mul_of_nonneg_left hF (by norm_num)).trans hrr0)
  have hV : heat lambda t.toNNReal w +
      shiftedBaseMultiplier lambda (shiftedHighOperator hT lambda F t) =
        initialResponseTrace lambda w hT F ⟨t, ht⟩ := by
    change heat lambda t.toNNReal w +
      shiftedBaseMultiplier lambda (shiftedHighOperator hT lambda F t) =
        heat lambda t.toNNReal w + shiftedTracePath hT lambda F ⟨t, ht⟩
    rw [htrace ht]
  have hN := hsourceT (shiftedHighOperator hT lambda F t) hball
  rw [hV] at hN
  rw [hRt ht, hNt, hN, map_sub]
  abel

end PoincareConjecture.M63.CenteredSpectralResidual
