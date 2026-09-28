import PoincareConjecture.Statements.M25NeckCapTopology
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.NonseparatingCompactUnion
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.CertificateAssembly
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.FiniteBackwardExtensionReturn









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace M25



def CompactNonseparatingFibrationInput : Prop :=
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 → H.X = Set.univ →
      (∀ N ∈ H.necks, N.IsNonseparating) →
      IsCompact (Set.univ : Set M) →
      ∃ F : SphereBundleCircleCertificate g H.X,
        F.carrier = Set.univ ∧ F.epsilon = H.epsilon

end M25



theorem a20_fibration_of_nonseparating
    (hF : M25.CompactNonseparatingFibrationInput.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 → H.X = Set.univ →
      (∀ N ∈ H.necks, N.IsNonseparating) →
      ∃ F : SphereBundleCircleCertificate g H.X,
        F.carrier = Set.univ ∧ F.epsilon = H.epsilon := by
  obtain ⟨εc, hcpos, hccap, hcompact⟩ :=
    NeckOnlyCover.exists_compact_whole_union_of_nonseparating.{u}
  obtain ⟨εf, hfpos, _, hF2⟩ :=
    hF
  refine ⟨min εc εf, lt_min hcpos hfpos, (min_le_left _ _).trans hccap, ?_⟩
  intro M _ _ _ _ _ _ g H he hwhole hnon
  obtain ⟨x0, hx0⟩ := H.connected_X.nonempty
  obtain ⟨N, hN, _⟩ := H.pointwise_center_cover x0 hx0
  have hM : IsCompact (Set.univ : Set M) := by
    obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcpt⟩ :=
      hcompact H (he.trans (min_le_left _ _)) hwhole N hN (hnon N hN)
    exact hcpt
  exact hF2 H (he.trans (min_le_right _ _)) hwhole hnon hM

end PoincareConjecture
