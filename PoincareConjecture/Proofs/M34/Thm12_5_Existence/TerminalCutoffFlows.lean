import PoincareConjecture.Proofs.M34.Thm12_5_Existence.TerminalCutoffBounds
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.CutoffDoubles
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.DoubleFlows
import PoincareConjecture.Proofs.M34.Standard.CompactDerivativeBounds
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.Restart.Approximation











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff

namespace PoincareConjecture.M34



theorem terminalCutoffRadius_ge_three (k : ℕ) : (3 : ℝ) ≤ (k : ℝ) + 5 := by
  linarith [Nat.cast_nonneg (α := ℝ) k]



abbrev TerminalCutoffDouble (g0 : StandardInitialMetric) (k : ℕ) :=
  CutoffDouble g0.cylindrical_end (terminalCutoffRadius_ge_three k)

namespace PartialFlowTerminalJets

variable {g0 : StandardInitialMetric} {F : PartialStandardCapFlow g0} {S : ℝ}
  (L : PartialFlowTerminalJets F S) (P : M34StandardCapPredecessors)
  (E0 : StandardCapEstimate g0) {B : ℝ} (hS : 0 < S) (hSF : S ≤ F.lifetime) (hB : 0 < B)
  (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
    (F.flow.connection t).curvatureTensorNorm x ≤ B)



theorem cutoffDouble_curvatureDerivative_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (hR : 3 ≤ R),
      ∀ D : LeviCivitaData (cutoffDoubleMetric g0.cylindrical_end
        (L.metric P.curvature E0 hS hSF hB hfull) hR),
      ∀ q : CutoffDouble g0.cylindrical_end hR, D.curvatureDerivativeNorm m q ≤ C := by
  obtain ⟨C, hC, hbound⟩ := L.cutoffMetric_curvatureDerivative_bound
    P.curvature E0 hS hSF hB hfull m
  refine ⟨C, hC, fun R hR D q => ?_⟩
  let h := L.metric P.curvature E0 hS hSF hB hfull
  let Dh := (cutoffMetric g0.cylindrical_end h R).euclideanLeviCivitaData
  exact cutoffDouble_curvatureDerivative_le g0.cylindrical_end h hR Dh m (hbound R Dh) D q



theorem cutoffDouble_initialDerivative_bounds_upto (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (hR : 3 ≤ R),
      ∀ D : LeviCivitaData (cutoffDoubleMetric g0.cylindrical_end
        (L.metric P.curvature E0 hS hSF hB hfull) hR),
      ∀ j ≤ k, ∀ q : CutoffDouble g0.cylindrical_end hR, D.curvatureDerivativeNorm j q ≤ C := by
  induction k with
  | zero =>
      obtain ⟨C, hC, hb⟩ := L.cutoffDouble_curvatureDerivative_bound P E0 hS hSF hB hfull 0
      refine ⟨C, hC, fun R hR D j hj q => ?_⟩
      have hj0 : j = 0 := by omega
      subst j
      exact hb R hR D q
  | succ k ih =>
      obtain ⟨C, hC, hb⟩ := ih
      obtain ⟨A, hA, ha⟩ := L.cutoffDouble_curvatureDerivative_bound P E0 hS hSF hB hfull (k + 1)
      refine ⟨max C A, le_max_of_le_left hC, fun R hR D j hj q => ?_⟩
      by_cases hjk : j ≤ k
      · exact (hb R hR D j hjk q).trans (le_max_left _ _)
      · have hjs : j = k + 1 := by omega
        subst j
        exact (ha R hR D q).trans (le_max_right _ _)



theorem cutoffDouble_flows_exist :
    ∃ τ K : ℝ, 0 < τ ∧ 0 < K ∧ ∀ (R : ℝ) (hR : 3 ≤ R),
      ∃ H : RicciFlow 3 (CutoffDouble g0.cylindrical_end hR) (Icc 0 τ),
        H.metric 0 = cutoffDoubleMetric g0.cylindrical_end
          (L.metric P.curvature E0 hS hSF hB hfull) hR ∧
        ∀ t ∈ Icc 0 τ, ∀ q : CutoffDouble g0.cylindrical_end hR,
          (H.connection t).curvatureTensorNorm q ≤ K := by
  obtain ⟨A, hA, hbound⟩ := L.cutoffDouble_curvatureDerivative_bound P E0 hS hSF hB hfull 0
  let C := A + 1
  have hC : 0 < C := by dsimp [C]; linarith
  let τ : ℝ := 1 / (23328 * C)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hsmall : 16 * (3 : ℝ) ^ 6 * C * τ ≤ 1 / 2 := by
    have hCne : C ≠ 0 := ne_of_gt hC
    dsimp [τ]
    norm_num
    field_simp
    nlinarith
  refine ⟨τ, 2 * C, hτ, by positivity, fun R hR => ?_⟩
  let h := cutoffDoubleMetric g0.cylindrical_end (L.metric P.curvature E0 hS hSF hB hfull) hR
  obtain ⟨D⟩ := exists_leviCivitaData h
  obtain ⟨H, hH, hnorm⟩ := exists_compactFlow_on_small_slab
    (P.local_flow 3 (CutoffDouble g0.cylindrical_end hR)) h D hC hτ hsmall (fun q => by
      rw [← D.curvatureDerivativeNorm_zero]
      exact (hbound R hR D q).trans (by dsimp [C]; linarith))
  exact ⟨H, hH, hnorm⟩



theorem cutoffDouble_flow_derivative_bounds {T K : ℝ} (hT : 0 < T) (hK : 0 < K) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 3 ≤ R)
      (H : RicciFlow 3 (CutoffDouble g0.cylindrical_end hR) (Icc 0 T)),
      H.metric 0 = cutoffDoubleMetric g0.cylindrical_end
        (L.metric P.curvature E0 hS hSF hB hfull) hR →
      (∀ t ∈ Icc 0 T, ∀ q : CutoffDouble g0.cylindrical_end hR,
        (H.connection t).curvatureTensorNorm q ≤ K) →
      ∀ t ∈ Icc 0 T, ∀ q : CutoffDouble g0.cylindrical_end hR,
        (H.connection t).curvatureDerivativeNorm k q ≤ C := by
  obtain ⟨A, _hA, hA⟩ := L.cutoffDouble_initialDerivative_bounds_upto P E0 hS hSF hB hfull k
  have hKA : 0 < max K A := hK.trans_le (le_max_left _ _)
  obtain ⟨C, hC, hest⟩ := compact_initial_derivative_bound P.curvature 3 k hKA hT
  refine ⟨C, hC, fun R hR H hH hcurv => ?_⟩
  apply hest (CutoffDouble g0.cylindrical_end hR) H
  · exact fun t ht q => (hcurv t ht q).trans (le_max_left _ _)
  · have hinit : ∀ D : LeviCivitaData (H.metric 0), ∀ j ≤ k,
        ∀ q : CutoffDouble g0.cylindrical_end hR, D.curvatureDerivativeNorm j q ≤ A := by
      rw [hH]
      exact hA R hR
    exact fun j hj q => (hinit (H.connection 0) j hj q).trans (le_max_right _ _)




theorem metricFlowApproximation_exists :
    Nonempty (MetricFlowApproximation (L.metric P.curvature E0 hS hSF hB hfull)
      (TerminalCutoffDouble g0)) := by
  classical
  obtain ⟨T, K, hT, hK, hflows⟩ := L.cutoffDouble_flows_exist P E0 hS hSF hB hfull
  choose H hinit hcurv using fun k : ℕ => hflows ((k : ℝ) + 5) (terminalCutoffRadius_ge_three k)
  choose C hC hderiv using fun m =>
    L.cutoffDouble_flow_derivative_bounds P E0 hS hSF hB hfull hT hK m
  refine ⟨{
    time := T
    time_pos := hT
    flow := H
    source := fun k => endTruncation g0.cylindrical_end (((k : ℝ) + 5) - 1)
    source_isOpen := fun k => endTruncation_isOpen _ (by linarith [Nat.cast_nonneg (α := ℝ) k])
    chart := fun k => cutoffDoubleChart g0.cylindrical_end (terminalCutoffRadius_ge_three k) false
    chart_smooth := fun k => cutoffDoubleChart_contMDiffOn _ _ _
    chart_invertible := fun k x hx => cutoffDoubleChart_mfderiv_isInvertible _ _ _ hx
    initial_pullback := ?_
    compact_sources := ?_
    curvature_bound := C
    bound_pos := hC
    curvature_le := fun m k => hderiv m ((k : ℝ) + 5) (terminalCutoffRadius_ge_three k)
      (H k) (hinit k) (hcurv k) }⟩
  · intro k x hx
    rw [hinit k]
    exact cutoffDoubleMetric_initial_pullback _ _ _ _ hx
  · intro K hK
    have heq (k : ℕ) : ((k : ℝ) + 5) - 1 = (k : ℝ) + 4 := by ring
    simpa only [heq] using eventually_compact_subset_cutoff_source g0.cylindrical_end hK

end PartialFlowTerminalJets
end PoincareConjecture.M34
