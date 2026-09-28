import PoincareConjecture.Proofs.M09.RegularizedIntervalSolution
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

def maximalRegularizedDomain {J : Set ℝ} (F : RicciFlow n M J)
    (T b s0 : ℝ) (q0 : TangentBundle (𝓡 n) M) : Set ℝ :=
  ⋃ A : RegularizedIntervalSolution F T b s0 q0, A.domain

noncomputable def maximalRegularizedCurve {J : Set ℝ} (F : RicciFlow n M J)
    (T b s0 : ℝ) (q0 : TangentBundle (𝓡 n) M) (s : ℝ) : M := by
  classical
  exact if hs : s ∈ maximalRegularizedDomain F T b s0 q0 then
    (Classical.choose (Set.mem_iUnion.mp hs)).curve s else q0.proj

theorem isOpen_maximalRegularizedDomain {J : Set ℝ} (F : RicciFlow n M J)
    (T b s0 : ℝ) (q0 : TangentBundle (𝓡 n) M) :
    IsOpen (maximalRegularizedDomain F T b s0 q0) :=
  isOpen_iUnion (fun A ↦ A.open_domain)

theorem isPreconnected_maximalRegularizedDomain {J : Set ℝ} (F : RicciFlow n M J)
    (T b s0 : ℝ) (q0 : TangentBundle (𝓡 n) M) :
    IsPreconnected (maximalRegularizedDomain F T b s0 q0) :=
  isPreconnected_iUnion ⟨s0, Set.mem_iInter.mpr (fun A ↦ A.initial_mem)⟩
    (fun A ↦ A.preconnected_domain)

theorem maximalRegularizedDomain_subset {J : Set ℝ} (F : RicciFlow n M J)
    (T b s0 : ℝ) (q0 : TangentBundle (𝓡 n) M) :
    maximalRegularizedDomain F T b s0 q0 ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b) := by
  intro s hs
  obtain ⟨A, hsA⟩ := Set.mem_iUnion.mp hs
  exact A.time_mem hsA

theorem RegularizedIntervalSolution.domain_subset_maximal {J : Set ℝ}
    {F : RicciFlow n M J} {T b s0 : ℝ} {q0 : TangentBundle (𝓡 n) M}
    (A : RegularizedIntervalSolution F T b s0 q0) :
    A.domain ⊆ maximalRegularizedDomain F T b s0 q0 :=
  fun _ hs ↦ Set.mem_iUnion.mpr ⟨A, hs⟩

theorem RegularizedIntervalSolution.phase_eqOn {J : Set ℝ} [T2Space M]
    {F : RicciFlow n M J} {T b s0 : ℝ} {q0 : TangentBundle (𝓡 n) M}
    (A B : RegularizedIntervalSolution F T b s0 q0)
    (hM04 : RicciFlowCurvatureTheory.{u}) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) :
    Set.EqOn (curvePhase (n := n) A.curve) (curvePhase (n := n) B.curve)
      (A.domain ∩ B.domain) := by
  exact localRegularizedCurve_phase_eqOn F hM04 T b hb hwindow A.curve B.curve
    (A.domain ∩ B.domain) (A.open_domain.inter B.open_domain)
    (A.preconnected_domain.ordConnected.inter B.preconnected_domain.ordConnected).isPreconnected
    (fun _ hs ↦ A.time_mem hs.1) (A.isLocal.mono Set.inter_subset_left)
    (B.isLocal.mono Set.inter_subset_right) s0 ⟨A.initial_mem, B.initial_mem⟩
    (A.initial_phase.trans B.initial_phase.symm)

theorem maximalRegularizedCurve_eqOn {J : Set ℝ} [T2Space M]
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (s0 : ℝ) (q0 : TangentBundle (𝓡 n) M)
    (A : RegularizedIntervalSolution F T b s0 q0) :
    Set.EqOn (maximalRegularizedCurve F T b s0 q0) A.curve A.domain := by
  intro s hs
  have hsD := A.domain_subset_maximal hs
  let B := Classical.choose (Set.mem_iUnion.mp hsD)
  have hsB : s ∈ B.domain := Classical.choose_spec (Set.mem_iUnion.mp hsD)
  have hp := B.phase_eqOn A hM04 hb hwindow ⟨hsB, hs⟩
  unfold maximalRegularizedCurve
  rw [dif_pos hsD]
  exact congrArg Bundle.TotalSpace.proj hp

theorem maximalRegularizedCurve_eventuallyEq {J : Set ℝ} [T2Space M]
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (s0 : ℝ) (q0 : TangentBundle (𝓡 n) M)
    (A : RegularizedIntervalSolution F T b s0 q0) (s : ℝ) (hs : s ∈ A.domain) :
    maximalRegularizedCurve F T b s0 q0 =ᶠ[𝓝 s] A.curve := by
  filter_upwards [A.open_domain.mem_nhds hs] with t ht
  exact maximalRegularizedCurve_eqOn F hM04 T b hb hwindow s0 q0 A ht

theorem maximalRegularizedCurve_isLocal {J : Set ℝ} [T2Space M]
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (s0 : ℝ) (q0 : TangentBundle (𝓡 n) M) :
    IsLocalRegularizedCurveOn F T (maximalRegularizedCurve F T b s0 q0)
      (maximalRegularizedDomain F T b s0 q0) := by
  apply IsLocalRegularizedCurveOn.of_locally
  intro s hs
  obtain ⟨A, hsA⟩ := Set.mem_iUnion.mp hs
  exact ⟨A.curve, A.domain, A.open_domain, hsA, A.isLocal,
    maximalRegularizedCurve_eventuallyEq F hM04 T b hb hwindow s0 q0 A s hsA⟩

noncomputable def maximalRegularizedSolution {J : Set ℝ} [T2Space M]
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (s0 : ℝ) (hs0 : s0 ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (q0 : TangentBundle (𝓡 n) M) : RegularizedIntervalSolution F T b s0 q0 where
  domain := maximalRegularizedDomain F T b s0 q0
  open_domain := isOpen_maximalRegularizedDomain F T b s0 q0
  preconnected_domain := isPreconnected_maximalRegularizedDomain F T b s0 q0
  initial_mem := by
    obtain ⟨A⟩ := nonempty_regularizedIntervalSolution F hM04 T b hb hwindow s0 hs0 q0
    exact A.domain_subset_maximal A.initial_mem
  time_mem := maximalRegularizedDomain_subset F T b s0 q0
  curve := maximalRegularizedCurve F T b s0 q0
  isLocal := maximalRegularizedCurve_isLocal F hM04 T b hb hwindow s0 q0
  initial_phase := by
    obtain ⟨A⟩ := nonempty_regularizedIntervalSolution F hM04 T b hb hwindow s0 hs0 q0
    exact (curvePhase_eventuallyEq (maximalRegularizedCurve_eventuallyEq F hM04 T b hb
      hwindow s0 q0 A s0 A.initial_mem)).eq_of_nhds.trans A.initial_phase

end PoincareConjecture.Proofs.M09
