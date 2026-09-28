import PoincareConjecture.Proofs.M25.AppA_1_Necks.SeparatingTube
import PoincareConjecture.Definitions.M25NeckCapTopology










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem ConnectedNeckCapCover.exists_repairedData_of_separating_neck_centers :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : ConnectedNeckCapCover g), H.epsilon ≤ epsilon0 →
      (∀ x ∈ H.X, ∃ N ∈ H.necks, N.center = x) →
      (∀ N ∈ H.necks, N.center ∈ H.X → N.IsSeparating) →
      Nonempty (RepairedNeckCapTopologyData g H) := by
  classical
  obtain ⟨epsilon0, hpos, hcap, hA19⟩ :=
    NeckOnlyCover.exists_correctedA19Conclusion_of_separating.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g H he hcenters hsep
  let K : NeckOnlyCover g :=
    { epsilon := H.epsilon
      epsilon_pos := H.epsilon_pos
      epsilon_threshold := H.epsilon_threshold
      epsilon_threshold_pos := H.epsilon_threshold_pos
      epsilon_threshold_le_one_two_hundred := H.epsilon_threshold_le_one_two_hundred
      epsilon_le_threshold := H.epsilon_le_threshold
      X := H.X
      connected_X := H.connected_X
      necks := {N | N ∈ H.necks ∧ N.center ∈ H.X}
      pointwise_center_cover := by
        intro x hx
        obtain ⟨N, hN, hNx⟩ := hcenters x hx
        refine ⟨N, ⟨hN, ?_⟩, hNx⟩
        rw [hNx]
        exact hx
      neck_epsilon := by
        intro N hN
        exact H.neck_epsilon N hN.1 }
  have hKsep : ∀ N ∈ K.necks, N.IsSeparating := by
    intro N hN
    change N ∈ H.necks ∧ N.center ∈ H.X at hN
    exact hsep N hN.1 hN.2
  obtain ⟨D⟩ := hA19 K (show K.epsilon ≤ epsilon0 from he) hKsep
  refine ⟨{ region := NeckCapRegion.tube D.tube, compatible := ?_ }⟩
  change D.tube.epsilon = H.epsilon
  exact D.epsilon_eq

end PoincareConjecture
