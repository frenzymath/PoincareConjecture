import PoincareConjecture.Proofs.M09.LocalCompactPhaseBound
import PoincareConjecture.Proofs.M09.UniformIntervalContinuation
import PoincareConjecture.Proofs.M09.UniformRestartRadius
import PoincareConjecture.Proofs.M09.RegularizedRestartGluing

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

set_option backward.isDefEq.respectTransparency false in
theorem Ico_subset_maximalRegularizedDomain {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (q0 : TangentBundle (𝓡 n) M) :
    Set.Ico 0 (Real.sqrt τmax) ⊆ maximalRegularizedDomain F T τmax 0 q0 := by
  have hsqrt : 0 < Real.sqrt τmax := Real.sqrt_pos.mpr hτmax
  have h0time : (0 : ℝ) ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) :=
    ⟨neg_lt_zero.mpr hsqrt, hsqrt⟩
  let A := maximalRegularizedSolution F hM04 T τmax hτmax hwindow 0 h0time q0
  let D := maximalRegularizedDomain F T τmax 0 q0
  let γ := maximalRegularizedCurve F T τmax 0 q0
  let Emax := max 0 ((F.metric T).inner q0.proj q0.2 q0.2)
  have hphase : curvePhase (n := n) γ 0 = q0 := A.initial_phase
  have hstart : γ 0 = q0.proj := congrArg Bundle.TotalSpace.proj hphase
  have henergy : regularizedCurveEnergy F T γ 0 = (F.metric T).inner q0.proj q0.2 q0.2 := by
    have h := congrArg (fun q : TangentBundle (𝓡 n) M ↦
      (F.metric T).inner q.proj q.2 q.2) hphase
    simpa [regularizedCurveEnergy, curvePhase] using h
  intro S hS
  obtain ⟨c, hSc, hcmax⟩ := exists_between hS.2
  have hc0 : 0 < c := hS.1.trans_lt hSc
  have hcmax' : c ^ 2 < τmax := by
    nlinarith [Real.sq_sqrt hτmax.le]
  obtain ⟨K0, hK0, hbound⟩ := exists_uniform_compact_local_phase_bound F hM04 T τmax
    hτmax hwindow hcurvature q0.proj (c ^ 2) Emax (sq_pos_of_pos hc0) hcmax'
    (le_max_left _ _)
  let K := K0 ∩ (Set.Icc 0 S ×ˢ (Set.univ : Set (TangentBundle (𝓡 n) M)))
  have hK : IsCompact K := hK0.inter_right (isClosed_Icc.prod isClosed_univ)
  have hKtime : ∀ z ∈ K, z.1 ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) := by
    intro z hz
    exact ⟨(neg_lt_zero.mpr hsqrt).trans_le hz.2.1.1, hz.2.1.2.trans_lt hS.2⟩
  have hconf : ∀ s ∈ Set.Icc 0 S, s ∈ D → (s, curvePhase (n := n) γ s) ∈ K := by
    intro s hs hsD
    refine ⟨hbound γ D A.open_domain A.preconnected_domain A.initial_mem A.isLocal hstart
      (henergy.trans_le (le_max_right _ _)) s hsD hs.1 ?_, hs, Set.mem_univ _⟩
    rw [Real.sqrt_sq hc0.le]
    exact hs.2.trans_lt hSc
  obtain ⟨r, hr, hrestart⟩ := exists_uniform_regularizedRestartRadius F hM04 T τmax
    hτmax hwindow K hK hKtime
  have hstep : ∀ s ∈ Set.Icc 0 S, s ∈ D → Set.Ioo (s - r) (s + r) ⊆ D := by
    intro s hs hsD
    obtain ⟨B, hB⟩ := hrestart (s, curvePhase (n := n) γ s) (hconf s hs hsD)
    exact hB.trans (maximalRegularizedDomain_contains_restart F hM04 T τmax hτmax
      hwindow 0 h0time q0 s hsD B)
  exact Icc_subset_of_uniform_open_intervals D A.open_domain A.initial_mem S hS.1 r hr hstep
    ⟨hS.1, le_rfl⟩

end PoincareConjecture.Proofs.M09
