import PoincareConjecture.Proofs.M76.Dehn.OriginalFiniteEdgeIntersections
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.Cover

set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem MarkedSurfaceMotionData.finite_edge_comparison_intersection
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V} (hK : K.faces.Finite) (hK₀ : K₀ ≤ K)
    {face : Finset V} (hface : face ∈ K.faces)
    (hsucc : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V))
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    {Q : OpenPartialHomeomorph t.Carrier V3}
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {B : OpenPartialHomeomorph s.Carrier V3} {J : SimplicialComplex ℝ V3}
    {U : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}
    (motion : MarkedSurfaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    (hKdim : ∀ c ∈ K.faces, c.card ≤ 3)
    (A : SimplicialComplex ℝ V) (hAdim : ∀ c ∈ A.faces, c.card ≤ 2)
    (old : K₀.faces)
    (hmarked : boundary = true → face ∈ A.faces ∧ old.val ∈ A.faces)
    (hsmall : boundary = true ∨ face.card ≤ 2 ∨ old.val.card ≤ 2) :
    {w : V3 | w ∈ motion.coordinates.map 1 '' motion.source.space ∧
      w ∉ motion.fixedSource.space ∧ w ∈ (motion.targets old).space}.Finite := by
  obtain ⟨T, hT, hcover⟩ :=
    motion.exists_finite_intersection_cover hK hK₀ hface hsucc hj hQ hKdim A hAdim old hmarked
  have hzero (L : AffineSubspace ℝ V3) (hL : L ∈ T) :
      Module.finrank ℝ L.direction = 0 :=
    hsmall.elim (hT L hL).2.2.1 (hT L hL).2.2.2
  have hfinite : (⋃ L ∈ (T : Set (AffineSubspace ℝ V3)), (L : Set V3)).Finite :=
    T.finite_toSet.biUnion fun L hL => L.finite_of_finrank_direction_eq_zero (hzero L hL)
  apply hfinite.subset
  intro w hw
  obtain ⟨L, hL, hwL⟩ := hcover w hw.1 hw.2.1 hw.2.2
  exact mem_iUnion₂.mpr ⟨L, hL, hwL⟩

end Geometry.OriginalPLTower
