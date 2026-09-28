import PoincareConjecture.Proofs.M39.Prop15_12_PathBounds

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M40

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y] [RegularSpace Y]

theorem metric_edist_le_mul_of_local_pair_bound
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    (f : X → Y) {C : ℝ} (hC : 0 < C)
    (hlocal : ∀ x, ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ z ∈ U,
      h.edist (f y) (f z) ≤ ENNReal.ofReal C * g.edist y z)
    (x y : X) : h.edist (f x) (f y) ≤ ENNReal.ofReal C * g.edist x y := by
  have hopen : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ z ∈ U,
        h.edist (f y) (f z) ≤ ENNReal.ofReal C * g.edist y z := by
    intro x
    obtain ⟨U, hUx, hU⟩ := hlocal x
    obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.mp hUx
    exact ⟨V, hVo, hxV, fun y hy z hz => hU y (hVU hy) z (hVU hz)⟩
  choose U hUo hxU hUb using hopen
  apply M39.metric_edist_le_mul_of_open_cover g h U hUo
    (fun z => ⟨z, hxU z⟩) f hC
  intro i γ a b hab hγ hγU
  exact (hUb i (γ a) (hγU ⟨le_rfl, hab⟩) (γ b) (hγU ⟨hab, le_rfl⟩)).trans
    (mul_le_mul' le_rfl (M36.metric_edist_le_pathELength g hab hγ))

end PoincareConjecture.M40
