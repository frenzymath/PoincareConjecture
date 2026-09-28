import PoincareConjecture.Proofs.M08.CompleteMetricBalls
import PoincareConjecture.Statements.Ch04.CurvatureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def shiftedContinuationFlow {J : Set ℝ} (F : RicciFlow n M J)
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Icc (T - τmax) T ⊆ J) :
    RicciFlow n M (Icc 0 τmax) where
  metric t := F.metric (T - τmax + t)
  connection t := F.connection (T - τmax + t)
  interval := ordConnected_Icc
  nontrivial := ⟨0, ⟨le_rfl, hτmax.le⟩, τmax, ⟨hτmax.le, le_rfl⟩, ne_of_lt hτmax⟩
  smooth := by
    have hm : MapsTo (fun z : ℝ × M ↦ (T - τmax + z.1, z.2))
        (Icc 0 τmax ×ˢ univ) (J ×ˢ univ) := by
      intro z hz
      exact ⟨hwindow ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, mem_univ _⟩
    exact F.smooth.comp
      ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd).contMDiffOn hm
  equation t ht x v w := by
    have hm : MapsTo (fun r : ℝ ↦ T - τmax + r) (Icc 0 τmax) J := by
      intro r hr
      exact hwindow ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have h := (F.equation (T - τmax + t) (hm ht) x v w).comp t
      ((hasDerivAt_id t).const_add (T - τmax)).hasDerivWithinAt hm
    simpa only [mul_one, Function.comp_def] using h

set_option maxHeartbeats 1000000 in
theorem exists_uniform_curvatureDerivative_bound {J : Set ℝ}
    [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax τ₁ : ℝ) (hτmax : 0 < τmax) (hτ₁ : τ₁ < τmax)
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T)) :
    ∃ B : ℝ, 0 < B ∧ ∀ τ ∈ Icc 0 τ₁, ∀ x : M,
      (F.connection (T - τ)).curvatureDerivativeNorm 1 x ≤ B := by
  obtain ⟨K, hK, hRm⟩ := hcurvature.2
  let G := shiftedContinuationFlow F T τmax hτmax hwindow
  have hK' : 0 < K + 1 := by linarith
  obtain ⟨C, hC, hshi⟩ := hM04.local_derivative_estimates n 1 (K + 1)
    ((K + 1) * τmax) 1 hK' (mul_pos hK' hτmax) zero_lt_one
  have hratio : τmax ≤ ((K + 1) * τmax) / (K + 1) := by
    rw [mul_div_cancel_left₀ _ (ne_of_gt hK')]
  have hbase : MetricComplete (F.metric (T - τmax)) :=
    hcurvature.1 _ ⟨le_rfl, sub_le_self T hτmax.le⟩
  have hcompact (x : M) : IsCompact (closure ((G.metric 0).ball x 1)) := by
    simpa only [G, shiftedContinuationFlow, add_zero] using
      isCompact_closure_referenceBall (F.metric (T - τmax)) hbase x zero_lt_one
  have hbound (t : ℝ) (ht : t ∈ Icc 0 τmax) (x : M) :
      (G.connection t).curvatureTensorNorm x ≤ K + 1 := by
    have hm : T - τmax + t ∈ Icc (T - τmax) T :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ((le_abs_self _).trans (hRm _ hm x)).trans (by linarith)
  refine ⟨C / Real.sqrt (τmax - τ₁), div_pos hC (Real.sqrt_pos.mpr (sub_pos.mpr hτ₁)), ?_⟩
  intro τ hτ x
  have ht : τmax - τ ∈ Ioc 0 τmax := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hcenter : x ∈ (G.metric 0).ball x ((1 : ℝ) / 2) := by
    change (G.metric 0).edist x x < ENNReal.ofReal ((1 : ℝ) / 2)
    have hself : (G.metric 0).edist x x = 0 := by
      letI : MetricSpace M := referenceMetricSpace (G.metric 0)
      change edist x x = 0
      exact edist_self x
    rw [hself]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have h := hshi M τmax hτmax hratio G x (hcompact x)
    (fun t ht y _ ↦ hbound t ht y) (τmax - τ) ht x hcenter
  have heq : T - τmax + (τmax - τ) = T - τ := by ring
  have h' : (F.connection (T - τ)).curvatureDerivativeNorm 1 x ≤
      C / Real.sqrt (τmax - τ) := by
    dsimp only [G, shiftedContinuationFlow] at h
    simp only [Nat.cast_one, ← Real.sqrt_eq_rpow] at h
    have hnorm := congrArg (fun t : ℝ ↦ (F.connection t).curvatureDerivativeNorm 1 x) heq
    exact hnorm ▸ h
  exact h'.trans (div_le_div_of_nonneg_left hC.le
    (Real.sqrt_pos.mpr (sub_pos.mpr hτ₁)) (Real.sqrt_le_sqrt (by linarith [hτ.2])))

end PoincareConjecture.M08
