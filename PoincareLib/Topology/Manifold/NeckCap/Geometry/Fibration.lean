import PoincareLib.Topology.Manifold.NeckCap.Theory
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Fibration.Nonseparating.NonseparatingCompactUnion
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Fibration.Certificate.CertificateAssembly
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Fibration.Finite.FiniteBackwardExtensionReturn

/-!
# The nonseparating branch of A.20

Compactness reduces the whole-cover branch to its remaining circle-bundle
construction. Morgan--Tian, Lemma A.20, printed p. 508;
see the reviewed entry-assembly-adoption derivation of 2026-09-23.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

namespace M25

/-- The remaining compact circle-bundle construction, MT A.20, p. 508.
The threshold precedes the ambient geometry and the whole neck cover. -/
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

/-- Whole nonseparating covers reduce to the compact construction through
the proved compact-union theorem. MT A.20, p. 508. -/
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

end PoincareMT
