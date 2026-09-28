import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Compact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Alternatives
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Exclusion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Spherical

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RicciFlow

variable {M : Type} [TopologicalSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem exists_terminal_scalar_bound_of_m23_predecessors
    (P : M23NormalizedKappaCompactnessPredecessors)
    {κ : ℝ} (F : RicciFlow 3 M (Iic 0)) (hκ : 0 < κ)
    (hc : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hop : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hmono : ∀ s t, s ≤ t → t ≤ 0 → ∀ x,
      (F.connection s).scalarCurvature x ≤ (F.connection t).scalarCurvature x)
    (hnc : ∀ t ≤ 0, ∀ p : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (F.metric t).ball p r,
        |(F.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ 3) ≤ calibratedMetricVolume (F.metric t)
        ((F.metric t).ball p r))
    (p : M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : M, (F.connection 0).scalarCurvature x ≤ B := by
  classical
  by_cases hcompact : CompactSpace M
  · let _ := hcompact
    exact F.exists_terminal_scalar_bound_of_compactSpace P
  let _ : NoncompactSpace M := ⟨fun h => hcompact ⟨h⟩⟩
  by_contra hbound
  have hunbounded : ¬ BddAbove (range (F.connection 0).scalarCurvature) := by
    rintro ⟨B, hB⟩
    exact hbound ⟨max B 0, le_max_right _ _, fun x =>
      (hB (mem_range_self x)).trans (le_max_left _ _)⟩
  obtain ⟨S, _⟩ := F.exists_selected_roundProductBlowup P hκ hc hop hmono hnc p hunbounded
  have hsec : (F.connection 0).NonnegativeSectionalCurvature :=
    fun x v w => (F.connection 0).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hop 0 le_rfl x) v w
  obtain ⟨εs, hεs, hspherical⟩ := S.exists_no_eventual_spherical_necks (hc 0 le_rfl) hsec
  obtain ⟨εp, hεp, hprojective⟩ := S.exists_no_eventual_projective_necks (hc 0 le_rfl) hsec
  let ε := min εs (min εp (1 / 4))
  have hε : 0 < ε := lt_min hεs (lt_min hεp (by norm_num))
  have hεs' : ε ≤ εs := min_le_left _ _
  have hεp' : ε ≤ εp := (min_le_right _ _).trans (min_le_left _ _)
  have hεhalf : ε < 1 / 2 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num)
  obtain ⟨δ, _, _, B, hmodels⟩ := S.exists_terminal_round_or_projective_necks
    P hκ (hc 0 le_rfl) (hop 0 le_rfl) hmono hε hεhalf
  rcases hmodels with ⟨Φ, q, _, hnecks⟩ | ⟨Φ, q, _, _, _, _, hnecks⟩
  · apply hspherical ε hε hεs' B.convergence.subsequence B.convergence.subsequence_strictMono
    filter_upwards [hnecks] with i hi
    obtain ⟨N, hNe, hNs, hNc, _⟩ := hi
    exact ⟨N, hNe, hNs, hNc⟩
  · apply hprojective ε hε hεp' B.convergence.subsequence B.convergence.subsequence_strictMono
      (fun i => B.convergence.embedding i ∘ Φ) q
    filter_upwards [hnecks] with i hi
    exact ⟨hi.1, hi.2.1, hi.2.2.2.1, hi.2.2.1⟩

end PoincareConjecture.RicciFlow
