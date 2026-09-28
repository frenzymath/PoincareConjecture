import PoincareConjecture.Proofs.M76.Dehn.OriginalFiniteIntersectionCover

set_option autoImplicit false

open Set Geometry

namespace AffineSubspace

theorem finite_of_finrank_direction_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : AffineSubspace ℝ E)
    (hL : Module.finrank ℝ L.direction = 0) : (L : Set E).Finite := by
  apply Set.Subsingleton.finite
  intro x hx y hy
  have hxy := vsub_mem_direction hx hy
  rw [Submodule.finrank_eq_zero.mp hL, Submodule.mem_bot, vsub_eq_zero_iff_eq] at hxy
  exact hxy

end AffineSubspace

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

theorem FaceMotionData.finite_edge_comparison_intersection
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V2} (hK : K.faces.Finite) (hK₀ : K₀ ≤ K)
    {face : Finset V2} (hface : face ∈ K.faces)
    (hsucc : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V2))
    {j : V2 → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    {Q : OpenPartialHomeomorph t.Carrier V3}
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {B : OpenPartialHomeomorph s.Carrier V3} {J : SimplicialComplex ℝ V3}
    {U : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}
    (motion : FaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    (A : SimplicialComplex ℝ V2) (hA : A.space = Metric.sphere (0 : V2) 1)
    (old : K₀.faces)
    (hmarked : boundary = true → face ∈ A.faces ∧ old.val ∈ A.faces)
    (hsmall : boundary = true ∨ face.card ≤ 2 ∨ old.val.card ≤ 2) :
    {w : V3 | w ∈ motion.coordinates.map 1 '' motion.source.space ∧
      w ∉ motion.fixedSource.space ∧ w ∈ (motion.targets old).space}.Finite := by
  obtain ⟨T, hT, hcover⟩ :=
    motion.exists_finite_intersection_cover hK hK₀ hface hsucc hj hQ A hA old hmarked
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
