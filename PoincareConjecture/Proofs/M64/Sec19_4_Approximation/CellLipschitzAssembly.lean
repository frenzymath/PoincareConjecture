import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.WithinCellLipschitz
import PoincareConjecture.Proofs.M60.Mathlib.CompactExtendedLipschitz

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem m64_lipschitzOn_cell_of_extension
    (g : RiemannianMetric n M) {f F : LoopPlane → M} {S : Set LoopPlane}
    (hS : IsCompact S)
    (hfinite : ∀ x ∈ S, ∀ y ∈ S,
      g.edist (f x) (f y) ≠ (⊤ : ENNReal))
    (hF : ∀ x ∈ S, ContMDiffAt (𝓡 2) (𝓡 n) 1 F x)
    (hEq : EqOn f F S) :
    ∃ K : ℝ≥0, ∀ x ∈ S, ∀ y ∈ S,
      g.edist (f x) (f y) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal ‖x - y‖ := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : IsRiemannianManifold (𝓡 n) M := ⟨fun _ _ => rfl⟩
  have hloc : LocallyLipschitzOn S f := by
    intro x hx
    obtain ⟨K, U, hU, hK⟩ :=
      m64_lipschitzOn_nhdsWithin_of_extension g (hF x hx) hEq
    refine ⟨K, U ∩ S,
      inter_mem (nhdsWithin_le_nhds hU) self_mem_nhdsWithin, ?_⟩
    intro y hy z hz
    change g.edist (f y) (f z) ≤ (K : ℝ≥0∞) * edist y z
    simpa only [edist_dist, dist_eq_norm] using hK y hy z hz
  obtain ⟨K, hK⟩ := M60.exists_lipschitzOnWith_of_compact_edist_ne_top
    hS hloc hfinite
  refine ⟨K, ?_⟩
  intro x hx y hy
  have h := hK hx hy
  change g.edist (f x) (f y) ≤ (K : ℝ≥0∞) * edist x y at h
  simpa only [edist_dist, dist_eq_norm] using h

end PoincareConjecture
