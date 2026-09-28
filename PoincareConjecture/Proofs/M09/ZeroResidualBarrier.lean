import PoincareConjecture.Proofs.M09.ExponentialAdaptedFrame
import PoincareConjecture.Proofs.M09.AdaptedComparisonFamily
import PoincareConjecture.Proofs.M09.ComparisonActionChart
import PoincareConjecture.Proofs.M09.ComparisonFirstDerivatives
import PoincareConjecture.Proofs.M09.ComparisonLaplacian
import PoincareConjecture.Proofs.M09.HarnackIntegral
import PoincareConjecture.Proofs.M09.MinimizingInitialVectors









set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T2Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_exists_zeroResidual_upperBarrier
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 b (A.path Z b hb hmax)) :
    ∃ B : ReducedLengthUpperBarrier F T p (A.gamma Z b) b,
      reducedLengthBarrierResidual F T p (A.gamma Z b) b B = 0 := by
  let c := Real.sqrt b
  have hc : 0 < c := Real.sqrt_pos.mpr hb
  obtain ⟨U, P, hU, _, hKU, htime, hα, hP, hpair⟩ :=
    lExponentialFamily_exists_adapted_frame hτmax hwindow A Z b hb hmax
  obtain ⟨f, Ω, N, hΩ, _, h0N, hNΩ, hf, hbase, hfixed0, hfields, hbij⟩ :=
    exists_scaled_frame_comparison_family F T c hc (A.squareFamily Z) P U hU hKU hα
      (fun i ↦ (hP i).smooth) (hpair c (hKU ⟨hc.le, le_rfl⟩))
  have hsegment : ∀ s ∈ Set.Icc 0 c, ((0 : Fin n → ℝ), s) ∈ Ω :=
    fun _ hs ↦ hNΩ ⟨h0N, hs⟩
  have hfixed : ∀ x, f (x, 0) = p := fun x ↦ (hfixed0 x).trans (A.square_at_zero Z)
  obtain ⟨B, e, hze, _, _, _, _, hpullSource⟩ := exists_upperBarrier_of_comparison_family
    hM04 hL hτmax hwindow A Z b hb hmax hmin f Ω hΩ hf hsegment hbase hfixed hbij
  have hpull : (fun z : (Fin n → ℝ) × ℝ ↦ B.representative (f (z.1, Real.sqrt z.2), z.2))
      =ᶠ[𝓝 (0, b)] (fun z ↦ backwardLLength F T 0 z.2 (fun t ↦ f (z.1, Real.sqrt t)) /
        (2 * Real.sqrt z.2)) := by
    filter_upwards [e.open_source.mem_nhds hze] with z hz
    exact hpullSource z hz
  obtain ⟨hdf, _, hd⟩ := comparison_family_first_derivatives hM04 hL hτmax hwindow
    A Z b hb hmax f Ω hΩ hf hsegment hbase hfixed B.representative
      B.representative_spacetime_smooth hpull hbij.2
  let O : Set M := {q | (q, b) ∈ B.neighborhood}
  have hO : IsOpen O := B.neighborhood_open.preimage (continuous_id.prodMk continuous_const)
  have hΔ := comparison_family_laplacian_eq hM04 hL hτmax hwindow A Z b hb hmax hmin
    P U hU hKU htime hα hP hpair f Ω hΩ hf hsegment hbase hfixed hfields
      B.representative O hO B.center_mem B.representative_space_smooth_on hdf hpull
  have hvalue : B.representative (A.gamma Z b, b) = A.action Z b / (2 * Real.sqrt b) :=
    B.touches.trans ((lExponentialFamily_reducedLength_eq_action_iff hL A Z b hb hmax).mpr hmin)
  have hK := lExponentialFamily_harnack_integral_eq hM04 hτmax hwindow A Z b hb hmax
  refine ⟨B, ?_⟩
  unfold reducedLengthBarrierResidual
  rw [hd, hΔ, hK, hvalue]
  field_simp [hb.ne', hc.ne'] <;> ring

theorem exists_zeroResidual_upperBarrier
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (q : M)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    ∃ B : ReducedLengthUpperBarrier F T p q b, reducedLengthBarrierResidual F T p q b B = 0 := by
  obtain ⟨Z, hend, hmin⟩ := lExponentialFamily_exists_minimizing_initialVector
    hM04 hL hτmax hwindow A b hb hmax q
  rw [← hend]
  exact lExponentialFamily_exists_zeroResidual_upperBarrier hM04 hL hτmax hwindow
    A Z b hb hmax hmin

theorem exists_upperBarrier_with_residual_le
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (q : M)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ReducedLengthUpperBarrier F T p q b, reducedLengthBarrierResidual F T p q b B ≤ ε := by
  obtain ⟨B, hB⟩ := exists_zeroResidual_upperBarrier hM04 hL hτmax hwindow A q b hb hmax
  exact ⟨B, hB.le.trans hε.le⟩

end PoincareConjecture.Proofs.M09
