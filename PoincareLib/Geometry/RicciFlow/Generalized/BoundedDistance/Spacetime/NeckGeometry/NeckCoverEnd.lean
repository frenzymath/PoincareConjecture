import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.NeckGeometry.NeckCoverCompactness
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.CompactGeometry.CompactHeightTail

/-!
# Uniform scalar divergence on a proper neck-covered end

Finite volume makes bounded-scalar centers compactly contained. An
actual continuous height on the containing cylinder then excludes that
compact set from a late end tail. Source: Morgan--Tian Claim 10.8,
p. 254; M28 derivations 94 and 128.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

/-- A proper high-height side in the actual neck cover has uniform
scalar divergence. Heights are used only on their displayed domain;
every real scalar threshold is allowed. Source: Claim 10.8; derivation 128. -/
theorem scalar_diverges_on_proper_neck_cover_end
    (K : NeckOnlyCover g) (D : LeviCivitaData g)
    (hD : ∀ N ∈ K.necks, N.connection = D)
    (hfinite : g.volumeMeasure univ ≠ ⊤) {U P : Set M}
    (height : U → ℝ) (hh : Continuous height) (hupper : ∀ x, height x < 1)
    (hPK : P ⊆ K.X) (hclosure : closure P ⊆ U)
    (hside : ∀ x : U, (1 / 2 : ℝ) < height x → x.val ∈ P) :
    ∀ B : ℝ, ∃ a : ℝ, 1 / 2 < a ∧ a < 1 ∧
      ∀ x : U, a < height x → B < D.scalarCurvature x.val := by
  intro B
  obtain ⟨C, hC, hcapture⟩ := exists_compact_bounded_scalar_neck_cover K D hD hfinite
    (show 0 < max B 1 from lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  obtain ⟨a, ha, ha1, havoid⟩ := Poincare.exists_height_tail_disjoint_compact
    height hh hupper hclosure hside hC
  refine ⟨a, ha, ha1, ?_⟩
  intro x hx
  by_contra! hscalar
  exact havoid x hx (hcapture
    ⟨hPK (hside x (ha.trans hx)), hscalar.trans (le_max_left _ _)⟩)

end PoincareMT.M28
