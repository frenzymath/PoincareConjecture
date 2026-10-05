import PoincareLib.Topology.Manifold.Diffeomorph.BallExtension.Collar
import PoincareLib.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Affine

/-!
# Matching a ball to an outward boundary collar

Compactness of the boundary sphere supplies a uniform collar lying in the
ball chart. The ambient collar extension then corrects the full transition
without changing the ball image or the target neighborhood.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare

open PoincareMT

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

/-- Boundary agreement alone supplies the uniform target containment needed
to match the complete outward collar of an existing smooth ball. -/
theorem exists_ball_neighborhood_matching_boundary_collar
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    (b : OpenPartialHomeomorph E3 M)
    (hbs : Metric.closedBall 0 1 ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (c : OpenPartialHomeomorph RoundCylinderSpace M)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ)
    (hsource : univ ×ˢ Ioo (-δ) δ ⊆ c.source)
    (hzero : c '' (univ ×ˢ ({0} : Set ℝ)) = b '' Metric.sphere 0 1)
    (hpositive : ∀ (q : UnitTwoSphere) (t : ℝ), 0 < t → t < δ →
      c (q, t) ∉ b '' Metric.closedBall 0 1) :
    ∃ (η : ℝ) (a : OpenPartialHomeomorph E3 M),
      0 < η ∧ η < δ ∧ Metric.closedBall 0 1 ⊆ a.source ∧
      a.target = b.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ a a.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ a.symm a.target ∧
      a '' Metric.closedBall 0 1 = b '' Metric.closedBall 0 1 ∧
      ∀ p : RoundCylinderSpace, |p.2| < η →
        Real.exp p.2 • (p.1 : E3) ∈ a.source ∧
        a (Real.exp p.2 • (p.1 : E3)) = c p := by
  let W : Opens RoundCylinderSpace := ⟨(c.trans b.symm).source,
    (c.trans b.symm).open_source⟩
  have hzeroW (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ W := by
    refine ⟨hsource ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩, ?_⟩
    obtain ⟨x, hx, hxq⟩ := hzero.subset
      (mem_image_of_mem c (show (q, (0 : ℝ)) ∈ univ ×ˢ ({0} : Set ℝ) from ⟨mem_univ _, rfl⟩))
    change c (q, 0) ∈ b.target
    exact hxq ▸ b.map_source (hbs (Metric.sphere_subset_closedBall hx))
  obtain ⟨r, hr, hrW⟩ := CylinderGluing.exists_cylinder_collar W hzeroW
  let ε := min r δ
  have hε : 0 < ε := lt_min hr hδ
  have hεs : univ ×ˢ Ioo (-ε) ε ⊆ c.source := by
    intro z hz
    exact (hrW z ((abs_lt.mpr hz.2).trans_le (min_le_left _ _))).1
  have hεb : c '' (univ ×ˢ Ioo (-ε) ε) ⊆ b.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hrW z ((abs_lt.mpr hz.2).trans_le (min_le_left _ _))).2
  obtain ⟨η, a, hη, hηε, hrest⟩ := exists_ball_neighborhood_matching_collar
    b hbs hb hbi c hc hci hε hεs hεb hzero
    (fun q t ht htε => hpositive q t ht (htε.trans_le (min_le_right _ _)))
  exact ⟨η, a, hη, hηε.trans_le (min_le_right _ _), hrest⟩

end Poincare
