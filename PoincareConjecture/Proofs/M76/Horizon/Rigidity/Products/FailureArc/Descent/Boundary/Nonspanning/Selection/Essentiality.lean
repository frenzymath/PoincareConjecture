import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Contacts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Maps.Normalization
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.Canonical
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.Orientation.StageRimHomotopy



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.NonspanningStripExteriors

open PolygonalCrossingResolution NonspanningChainHole

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem original_rims_nonnull
    {c : Bool → P2 → P2} {T : Set P2}
    (E : NonspanningStripExteriors c spanningInnerSquare T)
    (N : NonspanningChainAnnulus E.hole)
    {X Y : Type*} [TopologicalSpace Y] {R : Set Y}
    {f g : P2 → X} {τ : (P2 × ℝ) → X} (projection : X → Y)
    (old original : C(Ann, R))
    (hold : ∀ x : Ann, (old x : Y) = projection (f x))
    (hnew : ∀ x : Ann, (original x : Y) = projection (g x))
    (hkeep : ∀ i (x : E.hole.sourceSet i), g (N.copy i x) =
      pieceMap f (τ ∘ tubeArmOrientation E.s0 E.s1) i x)
    (hnon : ¬ (planarAnnulusRim old true).Nullhomotopic) :
    ∀ b, ¬ (planarAnnulusRim original b).Nullhomotopic := by
  let k := E.hole.piece
  have hfront (z : Circle) : (annulusRimPoint true z : P2) ∈ frontier spanningInnerSquare :=
    (spanning_inner_frontier _).mpr (by simpa using depth_annulusRimPoint true z)
  have hsource (z : Circle) : (annulusRimPoint true z : P2) ∈ E.hole.sourceSet (.inl k) :=
    ⟨interior_subset (E.hole.source_inside
      (spanningInnerSquare_ball.isCompact.isClosed.frontier_subset (hfront z))), (hfront z).2⟩
  let p : C(Circle, E.hole.sourceSet (.inl k)) :=
    ⟨fun z ↦ ⟨annulusRimPoint true z, hsource z⟩,
      (continuous_subtype_val.comp (continuous_annulusRimPoint true)).subtype_mk _⟩
  let q : C(Circle, Ann) :=
    ⟨fun z ↦ N.copy (.inl k) (p z), (N.copy_embedding (.inl k)).continuous.comp p.continuous⟩
  have hdepth (z : Circle) : depth 8 (q z : P2) = 1 :=
    (N.retained_inner spanningInnerSquare_ball k (p z)).mpr (hfront z)
  obtain ⟨H, hHval⟩ := exists_annulus_rim_circle_homeomorph true
  let r : C(Circle, Circle) :=
    ⟨fun z ↦ H.symm ⟨q z, hdepth z⟩, H.symm.continuous.comp (q.continuous.subtype_mk _)⟩
  have hcoord (z : Circle) : annulusRimPoint true (r z) = q z :=
    (hHval (r z)).symm.trans (congrArg Subtype.val (H.apply_symm_apply _))
  have hvalue : (planarAnnulusRim original true).comp r = planarAnnulusRim old true := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    change (original (annulusRimPoint true (r z)) : Y) = old (annulusRimPoint true z)
    rw [hcoord, hnew, hold]
    exact congrArg projection (hkeep (.inl k) (p z))
  have hinner : ¬ (planarAnnulusRim original true).Nullhomotopic := by
    intro hn
    exact hnon (hvalue ▸ hn.comp_left r)
  have hom : (planarAnnulusRim original false).Homotopy (planarAnnulusRim original true) :=
    { toFun z := original (annulusRimCylinder z)
      continuous_toFun := original.continuous.comp annulusRimCylinder.continuous
      map_zero_left z := by rw [annulusRimCylinder_zero]; rfl
      map_one_left z := by rw [annulusRimCylinder_one]; rfl }
  intro b
  cases b
  · rintro ⟨x, hx⟩
    exact hinner ⟨x, (show (planarAnnulusRim original true).Homotopic
      (planarAnnulusRim original false) from ⟨hom.symm⟩).trans hx⟩
  · exact hinner

end PoincareConjecture.M76.Dehn.NonspanningStripExteriors
