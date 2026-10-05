import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Necks.Geometry.SeparatingChainTube
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Necks.Geometry.SeparatingCoverChain
import PoincareLib.Topology.Manifold.NeckCap.Theory
import Mathlib.Data.Sigma.Basic

/-!
# Separating A.19 and A.20 consumers

The covering-chain theorem and the separating-chain tube theorem already
construct all geometric data. Their dependent chain equality gives the
frozen conclusions of Morgan--Tian A.19, pp. 507-508, and the separating
branch of A.20, p. 508; see the reviewed separating-tube-conclusion plan.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.NeckOnlyCover

/-- A separating centered neck cover has the corrected A.19 tube conclusion
(Morgan--Tian pp. 507-508; reviewed separating-tube-conclusion plan). -/
theorem exists_correctedA19Conclusion_of_separating :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      ∀ hsep : ∀ N ∈ H.necks, N.IsSeparating,
        AppendixA19Theory g H hsep := by
  classical
  obtain ⟨epsilonK, hKpos, hKcap, hK⟩ :=
    exists_covering_balanced_chain_of_separating.{u}
  obtain ⟨epsilonT, hTpos, _, hT⟩ :=
    BalancedNeckChain.exists_epsilonTubeCertificate_of_separating.{u}
  refine ⟨min epsilonK epsilonT, lt_min hKpos hTpos,
    (min_le_left _ _).trans hKcap, ?_⟩
  intro M _ _ _ _ _ _ g H he hsep
  obtain ⟨C, hsource, hcontains, hcenters, _hquarters, _hincidence⟩ :=
    hK H (he.trans (min_le_left _ _)) hsep
  have hCsep : ∀ i ∈ C.shape.active, (C.neck i).IsSeparating := by
    intro i hi
    obtain ⟨N, hN, hsame⟩ := C.selected i hi
    have hNH : N ∈ H.necks := by
      rw [← hsource]
      exact hN
    rcases hsame with ⟨_, _, hcenter, _, hsphere, _⟩
    unfold EpsilonNeck.IsSeparating
    rw [hcenter, hsphere]
    exact hsep N hNH
  obtain ⟨T, hepsilon, hchain, _hcarrier⟩ :=
    hT C H.X (he.trans (min_le_right _ _)) hCsep hcontains
  have hpairs :
      (⟨T.epsilon, T.chain⟩ :
        Sigma (fun delta : ℝ => BalancedNeckChain g delta)) =
        ⟨H.epsilon, C⟩ := Sigma.ext hepsilon hchain
  have hshape : T.chain.shape = C.shape :=
    congrArg (fun p : Sigma (fun delta : ℝ => BalancedNeckChain g delta) =>
      p.2.shape) hpairs
  have hsource' : T.chain.source_necks = C.source_necks :=
    congrArg (fun p : Sigma (fun delta : ℝ => BalancedNeckChain g delta) =>
      p.2.source_necks) hpairs
  have hneck (i : ℤ) : T.chain.neck i = C.neck i :=
    congrArg (fun p : Sigma (fun delta : ℝ => BalancedNeckChain g delta) =>
      p.2.neck i) hpairs
  have hsource_subset : T.chain.source_necks ⊆ H.necks := by
    intro N hN
    rw [hsource', hsource] at hN
    exact hN
  have hselected : ∀ i ∈ T.chain.shape.active,
      (T.chain.neck i).center ∈ H.X := by
    intro i hi
    have hiC : i ∈ C.shape.active := by
      rw [← hshape]
      exact hi
    rw [hneck i]
    exact hcenters i hiC
  exact ⟨{
    tube := T
    epsilon_eq := hepsilon
    source_subset := hsource_subset
    selected_centers_mem := hselected
    contains_X := T.contains_X
    separating_necks := hsep
  }⟩

/-- The separating A.20 branch is the A.19 tube with whole carrier
(Morgan--Tian p. 508; reviewed separating-tube-conclusion plan). -/
theorem exists_correctedA20Conclusion_of_separating :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      (∀ N ∈ H.necks, N.IsSeparating) →
      ∀ hwhole : H.X = Set.univ,
        AppendixA20Theory g H hwhole := by
  classical
  obtain ⟨epsilon0, hpos, hcap, hA19⟩ :=
    exists_correctedA19Conclusion_of_separating.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g H he hsep hwhole
  obtain ⟨D⟩ := hA19 H he hsep
  have hcarrier : D.tube.carrier = (Set.univ : Set M) := by
    apply Set.eq_univ_of_forall
    intro x
    apply D.contains_X
    rw [hwhole]
    exact Set.mem_univ x
  exact ⟨CorrectedA20Conclusion.tube D.tube D.source_subset
    D.selected_centers_mem D.epsilon_eq hcarrier D.separating_necks⟩

end PoincareMT.NeckOnlyCover
