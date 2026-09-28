import PoincareConjecture.Proofs.M14.Sec6_3_PrefixJoinGauge
import PoincareConjecture.Proofs.M09.SmoothJoinCutoff









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14.PrefixJoinGauge

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ c : ℝ} {x y : G.Point}
  {q : M14BackwardPath G T τ₁ τ₂ x y}
  {p : M14BackwardPath G T τ₁ c x (q.curve c)} (D : PrefixJoinGauge q p)



theorem overlap_time {s : ℝ} (hs : s ∈ Icc (c - D.radius) c) :
    (D.lift (p.curve s)).1 = (D.lift (q.curve s)).1 := by
  have hwide : s ∈ Icc (c - D.radius) (c + D.radius) :=
    ⟨hs.1, by linarith [hs.2, D.radius_pos]⟩
  apply Subtype.ext
  rw [D.lift_time _ (D.prefix_in_image s hs), D.lift_time _ (D.continuation_in_image s hwide),
    p.curve_time s ⟨D.left_margin.le.trans hs.1, hs.2⟩,
    q.curve_time s ⟨D.left_margin.le.trans hs.1, hwide.2.trans D.right_margin.le⟩]




theorem blend_mem_region (a d : ℝ) {s : ℝ} (hs : s ∈ Icc (c - D.radius) c) :
    Proofs.M09.smoothJoinBlend (fun t => (D.lift (p.curve t)).2.val)
      (fun t => (D.lift (q.curve t)).2.val) a d s ∈ D.spatialRegion := by
  apply Proofs.M09.smoothJoinBlend_mem_convex _ _ _ _ _ _ D.region_convex
  · exact D.image_coordinates _ (D.prefix_in_image s hs)
  · exact D.image_coordinates _ (D.continuation_in_image s
      ⟨hs.1, by linarith [hs.2, D.radius_pos]⟩)

end PoincareConjecture.M14.PrefixJoinGauge
