import PoincareConjecture.Proofs.M09.RegularizedIntervalSolution
import PoincareConjecture.Proofs.M09.TangentChartPhase








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Z" => ℝ × (V × V)
local notation "Q" => ℝ × TangentBundle (𝓡 n) M

theorem exists_regularizedRestartNeighborhood {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (z0 : Q) (htime : z0.1 ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) :
    ∃ (O : Set Q) (r : ℝ), IsOpen O ∧ z0 ∈ O ∧ 0 < r ∧
      ∀ z ∈ O, ∃ A : RegularizedIntervalSolution F T b z.1 z.2,
        A.domain = Set.Ioo (z.1 - r) (z.1 + r) := by
  let p := z0.2.proj
  let B : Set Q := Set.univ ×ˢ {q : TangentBundle (𝓡 n) M | q.proj ∈ (chartAt V p).source}
  let c : Q → Z := fun z ↦ (z.1, tangentChartPhase p z.2)
  have hB : IsOpen B := isOpen_univ.prod ((chartAt V p).open_source.preimage
    (FiberBundle.continuous_proj V (TangentSpace (𝓡 n))))
  have hc : ContinuousOn c B := continuous_fst.continuousOn.prodMk
    ((tangentChartPhase_continuousOn p).comp continuous_snd.continuousOn (fun _ hz ↦ hz.2))
  obtain ⟨A⟩ := nonempty_localRegularizedRestartFamily F hM04 T b hb hwindow p (c z0)
    ⟨htime, (chartAt V p).map_source (mem_chart_source V p)⟩
  let O := B ∩ c ⁻¹' A.neighborhood
  have hO : IsOpen O := hc.isOpen_inter_preimage hB A.neighborhood_open
  refine ⟨O, A.radius, hO, ⟨⟨Set.mem_univ _, mem_chart_source V p⟩, A.center_mem⟩,
    A.radius_pos, ?_⟩
  intro z hz
  let S : RegularizedIntervalSolution F T b z.1 z.2 := {
    domain := Set.Ioo (z.1 - A.radius) (z.1 + A.radius)
    open_domain := isOpen_Ioo
    preconnected_domain := isPreconnected_Ioo
    initial_mem := ⟨by linarith [A.radius_pos], by linarith [A.radius_pos]⟩
    time_mem := fun s hs ↦ A.time_mem (c z) hz.2 s hs
    curve := A.curve (c z)
    isLocal := A.isLocalRegularizedCurveOn hM04 hb hwindow (c z) hz.2
    initial_phase := (A.initial_phase (c z) hz.2).trans (tangentChartPhase_inverse p z.2 hz.1.2)
  }
  exact ⟨S, rfl⟩

theorem exists_uniform_regularizedRestartRadius {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (K : Set Q) (hK : IsCompact K)
    (htime : ∀ z ∈ K, z.1 ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ K,
      ∃ A : RegularizedIntervalSolution F T b z.1 z.2,
        Set.Ioo (z.1 - r) (z.1 + r) ⊆ A.domain := by
  classical
  choose O r hO hmem hr hsol using fun z : K ↦
    exists_regularizedRestartNeighborhood F hM04 T b hb hwindow z (htime z z.property)
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover O hO (fun z hz ↦
    Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hmem ⟨z, hz⟩⟩)
  have hbound (S : Finset K) : ∃ d : ℝ, 0 < d ∧ ∀ i ∈ S, d ≤ r i := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨d, hd, hdi⟩ := ih
      refine ⟨min d (r i), lt_min hd (hr i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hdi j hj)
  obtain ⟨d, hd, hdi⟩ := hbound S
  refine ⟨d, hd, ?_⟩
  intro z hz
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (hS hz)
  obtain ⟨A, hA⟩ := hsol i z hzi
  refine ⟨A, ?_⟩
  rw [hA]
  intro s hs
  have hle := hdi i hi
  constructor <;> linarith [hs.1, hs.2]

end PoincareConjecture.Proofs.M09
