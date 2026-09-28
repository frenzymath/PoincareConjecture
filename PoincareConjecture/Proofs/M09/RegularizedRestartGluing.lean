import PoincareConjecture.Proofs.M09.MaximalRegularizedCurve
import Mathlib.Data.Set.Piecewise

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]

theorem exists_regularizedIntervalSolution_union {J : Set ℝ}
    {F : RicciFlow n M J} {T b s0 : ℝ} {q0 : TangentBundle (𝓡 n) M}
    (hM04 : RicciFlowCurvatureTheory.{u}) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J)
    (A : RegularizedIntervalSolution F T b s0 q0) (s : ℝ) (hs : s ∈ A.domain)
    (B : RegularizedIntervalSolution F T b s (curvePhase (n := n) A.curve s)) :
    ∃ C : RegularizedIntervalSolution F T b s0 q0,
      C.domain = A.domain ∪ B.domain ∧
      Set.EqOn C.curve A.curve A.domain ∧ Set.EqOn C.curve B.curve B.domain := by
  classical
  have hp := localRegularizedCurve_phase_eqOn F hM04 T b hb hwindow A.curve B.curve
    (A.domain ∩ B.domain) (A.open_domain.inter B.open_domain)
    (A.preconnected_domain.ordConnected.inter B.preconnected_domain.ordConnected).isPreconnected
    (fun _ ht ↦ A.time_mem ht.1) (A.isLocal.mono Set.inter_subset_left)
    (B.isLocal.mono Set.inter_subset_right) s ⟨hs, B.initial_mem⟩ B.initial_phase.symm
  let c := A.domain.piecewise A.curve B.curve
  have heA : Set.EqOn c A.curve A.domain := Set.piecewise_eqOn ..
  have heB : Set.EqOn c B.curve B.domain := by
    intro t ht
    by_cases htA : t ∈ A.domain
    · exact (heA htA).trans (congrArg Bundle.TotalSpace.proj (hp ⟨htA, ht⟩))
    · exact Set.piecewise_eq_of_notMem A.domain A.curve B.curve htA
  have hgA : ∀ t ∈ A.domain, c =ᶠ[𝓝 t] A.curve := by
    intro t ht
    filter_upwards [A.open_domain.mem_nhds ht] with r hr using heA hr
  have hgB : ∀ t ∈ B.domain, c =ᶠ[𝓝 t] B.curve := by
    intro t ht
    filter_upwards [B.open_domain.mem_nhds ht] with r hr using heB hr
  have hc : IsLocalRegularizedCurveOn F T c (A.domain ∪ B.domain) := by
    apply IsLocalRegularizedCurveOn.of_locally
    intro t ht
    rcases ht with ht | ht
    · exact ⟨A.curve, A.domain, A.open_domain, ht, A.isLocal, hgA t ht⟩
    · exact ⟨B.curve, B.domain, B.open_domain, ht, B.isLocal, hgB t ht⟩
  let C : RegularizedIntervalSolution F T b s0 q0 := {
    domain := A.domain ∪ B.domain
    open_domain := A.open_domain.union B.open_domain
    preconnected_domain := A.preconnected_domain.union s hs B.initial_mem B.preconnected_domain
    initial_mem := Or.inl A.initial_mem
    time_mem := fun _ ht ↦ ht.elim (fun h ↦ A.time_mem h) (fun h ↦ B.time_mem h)
    curve := c
    isLocal := hc
    initial_phase := (curvePhase_eventuallyEq (hgA s0 A.initial_mem)).eq_of_nhds.trans
      A.initial_phase
  }
  exact ⟨C, rfl, heA, heB⟩

theorem maximalRegularizedDomain_contains_restart {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (s0 : ℝ) (hs0 : s0 ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (q0 : TangentBundle (𝓡 n) M) (s : ℝ)
    (hs : s ∈ maximalRegularizedDomain F T b s0 q0)
    (B : RegularizedIntervalSolution F T b s
      (curvePhase (n := n) (maximalRegularizedCurve F T b s0 q0) s)) :
    B.domain ⊆ maximalRegularizedDomain F T b s0 q0 := by
  let A := maximalRegularizedSolution F hM04 T b hb hwindow s0 hs0 q0
  obtain ⟨C, hC, _, _⟩ := exists_regularizedIntervalSolution_union hM04 hb hwindow A s hs B
  intro t ht
  exact C.domain_subset_maximal (hC.symm ▸ Or.inr ht)

end PoincareConjecture.Proofs.M09
