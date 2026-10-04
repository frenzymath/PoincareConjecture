import PoincareLib.Topology.Manifold.Surgery.GroupEffects.ConnectedSum.Coordinates
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.Regions

/-!
# Restricting a connected-sum source to its selected component

The two disjoint-union identifications locate an original piece inside a
surgery side. A surgery ball whose entire chart lies in that piece pulls
back to a ball in the piece, with its punctured-region coordinates intact.
This is the source restriction in Morgan--Tian Corollary 15.4(2), pp. 358-359.
The domain checks appear in
`proof-work/tasks/M74/derivations/component-source-restriction.md`.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

namespace SurgeryRegionEquivalence

/-- A full-source region identification into an open region is an open embedding.
Source: MT Corollary 15.4, pp. 358-359. -/
theorem isOpenEmbedding_map {P B : GeneralizedSliceCarrier.{u}} {W : Set B.carrier}
    (E : SurgeryRegionEquivalence P B univ W) (hW : IsOpen W) :
    Topology.IsOpenEmbedding E.map :=
  hW.isOpenEmbedding_subtypeVal.comp (E.toHomeomorph.isOpenEmbedding.comp
    (Homeomorph.Set.univ P.carrier).symm.isOpenEmbedding)

/-- Identify a smaller full source inside another source through their common target.
Source: MT Corollary 15.4, pp. 358-359. -/
noncomputable def factorThrough {P B X : GeneralizedSliceCarrier.{u}}
    {U V : Set X.carrier} (F : SurgeryRegionEquivalence P X univ U)
    (E : SurgeryRegionEquivalence B X univ V) (hUV : U ⊆ V) :
    SurgeryRegionEquivalence P B univ (E.map ⁻¹' U) where
  map := E.inverse ∘ F.map
  inverse := F.inverse ∘ E.map
  map_image := by
    ext y
    constructor
    · rintro ⟨x, _, rfl⟩
      change E.map (E.inverse (F.map x)) ∈ U
      have hx : F.map x ∈ U := F.map_image.subset (mem_image_of_mem _ (mem_univ x))
      rwa [E.right_inverse (hUV hx)]
    · intro hy
      refine ⟨F.inverse (E.map y), mem_univ _, ?_⟩
      change E.inverse (F.map (F.inverse (E.map y))) = y
      rw [F.right_inverse hy, E.left_inverse (mem_univ y)]
  inverse_image := by
    apply Subset.antisymm (subset_univ _)
    intro x hx
    have hxU : F.map x ∈ U := F.map_image.subset (mem_image_of_mem _ hx)
    refine ⟨E.inverse (F.map x), ?_, ?_⟩
    · change E.map (E.inverse (F.map x)) ∈ U
      rwa [E.right_inverse (hUV hxU)]
    · change F.inverse (E.map (E.inverse (F.map x))) = x
      rw [E.right_inverse (hUV hxU), F.left_inverse hx]
  left_inverse := by
    intro x hx
    change F.inverse (E.map (E.inverse (F.map x))) = x
    rw [E.right_inverse (hUV (F.map_image.subset (mem_image_of_mem _ hx))), F.left_inverse hx]
  right_inverse := by
    intro y hy
    change E.inverse (F.map (F.inverse (E.map y))) = y
    rw [F.right_inverse hy, E.left_inverse (mem_univ y)]
  map_smooth := E.inverse_smooth.comp F.map_smooth
    (fun _ hx => hUV (F.map_image.subset (mem_image_of_mem _ hx)))
  inverse_smooth := F.inverse_smooth.comp (E.map_smooth.mono (subset_univ _))
    (fun _ hx => hx)

/-- Restrict a region equivalence to a smaller source and its exact image.
Source: MT Corollary 15.4, pp. 358-359. -/
noncomputable def restrictSource {A B : GeneralizedSliceCarrier.{u}}
    {U U' : Set A.carrier} {V : Set B.carrier}
    (E : SurgeryRegionEquivalence A B U V) (hU : U' ⊆ U) :
    SurgeryRegionEquivalence A B U' (E.map '' U') where
  map := E.map
  inverse := E.inverse
  map_image := rfl
  inverse_image := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa only [E.left_inverse (hU hy)] using hy
    · intro hx
      exact ⟨E.map x, mem_image_of_mem _ hx, E.left_inverse (hU hx)⟩
  left_inverse := fun _ hx => E.left_inverse (hU hx)
  right_inverse := fun _ hy => E.right_inverse (E.map_image.subset (image_mono hU hy))
  map_smooth := E.map_smooth.mono hU
  inverse_smooth := E.inverse_smooth.mono (fun _ hy => E.map_image.subset (image_mono hU hy))

end SurgeryRegionEquivalence

namespace SurgeryBallEmbedding

variable {P B : GeneralizedSliceCarrier.{u}} {W : Set B.carrier}

/-- Full-chart containment contains the smaller removed closed ball as well.
Source: MT Corollary 15.4, pp. 358-359. -/
theorem closedBall_subset_of_chart_subset (b : SurgeryBallEmbedding B)
    (hchart : b.map '' ball (0 : StandardCapSpace) 2 ⊆ W) : b.closedBall ⊆ W :=
  (image_mono (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))).trans hchart

/-- Pull a surgery ball back to a full source whose open region contains its chart.
Source: MT Corollary 15.4, pp. 358-359. -/
noncomputable def restrictToRegion (b : SurgeryBallEmbedding B)
    (E : SurgeryRegionEquivalence P B univ W) (hW : IsOpen W)
    (hchart : b.map '' ball (0 : StandardCapSpace) 2 ⊆ W) :
    SurgeryBallEmbedding P where
  map := E.inverse ∘ b.map
  inverse := b.inverse ∘ E.map
  map_smooth := E.inverse_smooth.comp b.map_smooth
    (fun _ hx => hchart (mem_image_of_mem _ hx))
  inverse_smooth := by
    apply b.inverse_smooth.comp (E.map_smooth.mono (subset_univ _))
    rintro _ ⟨x, hx, rfl⟩
    change E.map (E.inverse (b.map x)) ∈ b.map '' ball 0 2
    rw [E.right_inverse (hchart (mem_image_of_mem _ hx))]
    exact mem_image_of_mem _ hx
  left_inverse := by
    intro x hx
    change b.inverse (E.map (E.inverse (b.map x))) = x
    rw [E.right_inverse (hchart (mem_image_of_mem _ hx)), b.left_inverse hx]
  right_inverse := by
    rintro _ ⟨x, hx, rfl⟩
    change E.inverse (b.map (b.inverse (E.map (E.inverse (b.map x))))) = E.inverse (b.map x)
    rw [E.right_inverse (hchart (mem_image_of_mem _ hx)), b.left_inverse hx]
  open_embedding := by
    apply (E.isOpenEmbedding_map hW).of_comp
      (fun x : ball (0 : StandardCapSpace) 2 => E.inverse (b.map x.1))
    have hcomp : E.map ∘ (fun x : ball (0 : StandardCapSpace) 2 => E.inverse (b.map x.1)) =
        (fun x : ball (0 : StandardCapSpace) 2 => b.map x.1) := by
      funext x
      exact E.right_inverse (hchart (mem_image_of_mem _ x.2))
    rw [hcomp]
    exact b.open_embedding

/-- Including a restricted chart point recovers the original ball coordinate.
Source: MT Corollary 15.4, pp. 358-359. -/
theorem map_restrictToRegion_map (b : SurgeryBallEmbedding B)
    (E : SurgeryRegionEquivalence P B univ W) (hW : IsOpen W)
    (hchart : b.map '' ball (0 : StandardCapSpace) 2 ⊆ W)
    {x : StandardCapSpace} (hx : x ∈ ball 0 2) :
    E.map ((b.restrictToRegion E hW hchart).map x) = b.map x :=
  E.right_inverse (hchart (mem_image_of_mem _ hx))

/-- The restricted removed ball is the inverse image in coordinates of the old ball.
Source: MT Corollary 15.4, pp. 358-359. -/
theorem restrictToRegion_closedBall (b : SurgeryBallEmbedding B)
    (E : SurgeryRegionEquivalence P B univ W) (hW : IsOpen W)
    (hchart : b.map '' ball (0 : StandardCapSpace) 2 ⊆ W) :
    (b.restrictToRegion E hW hchart).closedBall = E.inverse '' b.closedBall := by
  exact image_comp E.inverse b.map (Metric.closedBall 0 1)

/-- Membership in the restricted removed ball is exactly membership after inclusion.
Source: MT Corollary 15.4, pp. 358-359. -/
theorem restrictToRegion_closedBall_preimage (b : SurgeryBallEmbedding B)
    (E : SurgeryRegionEquivalence P B univ W) (hW : IsOpen W)
    (hchart : b.map '' ball (0 : StandardCapSpace) 2 ⊆ W) :
    (b.restrictToRegion E hW hchart).closedBall = E.map ⁻¹' b.closedBall := by
  rw [b.restrictToRegion_closedBall E hW hchart]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change E.map (E.inverse y) ∈ b.closedBall
    rwa [E.right_inverse (b.closedBall_subset_of_chart_subset hchart hy)]
  · intro hx
    exact ⟨E.map x, hx, E.left_inverse (mem_univ x)⟩

/-- Inclusion sends the whole restricted closed ball onto the old removed ball.
Source: MT Corollary 15.4, pp. 358-359. -/
theorem map_restrictToRegion_closedBall (b : SurgeryBallEmbedding B)
    (E : SurgeryRegionEquivalence P B univ W) (hW : IsOpen W)
    (hchart : b.map '' ball (0 : StandardCapSpace) 2 ⊆ W) :
    E.map '' (b.restrictToRegion E hW hchart).closedBall = b.closedBall := by
  rw [b.restrictToRegion_closedBall E hW hchart]
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rwa [E.right_inverse (b.closedBall_subset_of_chart_subset hchart hx)]
  · intro hy
    exact ⟨E.inverse y, mem_image_of_mem _ hy,
      E.right_inverse (b.closedBall_subset_of_chart_subset hchart hy)⟩

end SurgeryBallEmbedding

/-- Remove the corresponding balls from a full-source region identification.
The target remains intersected with the selected region of the surgery side.
Source: MT Corollary 15.4, pp. 358-359. -/
noncomputable def SurgeryRegionEquivalence.puncture
    {P B : GeneralizedSliceCarrier.{u}} {W : Set B.carrier}
    (E : SurgeryRegionEquivalence P B univ W) (b : SurgeryBallEmbedding B)
    (hW : IsOpen W) (hchart : b.map '' ball (0 : StandardCapSpace) 2 ⊆ W) :
    SurgeryRegionEquivalence P B (b.restrictToRegion E hW hchart).closedBallᶜ
      (W ∩ b.closedBallᶜ) where
  map := E.map
  inverse := E.inverse
  map_image := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨E.map_image.subset (mem_image_of_mem _ (mem_univ x)), ?_⟩
      simpa only [b.restrictToRegion_closedBall_preimage E hW hchart,
        mem_compl_iff, mem_preimage] using hx
    · intro hy
      refine ⟨E.inverse y, ?_, E.right_inverse hy.1⟩
      rw [b.restrictToRegion_closedBall_preimage E hW hchart]
      change E.map (E.inverse y) ∈ b.closedBallᶜ
      simpa only [E.right_inverse hy.1] using hy.2
  inverse_image := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [b.restrictToRegion_closedBall_preimage E hW hchart]
      change E.map (E.inverse y) ∈ b.closedBallᶜ
      simpa only [E.right_inverse hy.1] using hy.2
    · intro hx
      refine ⟨E.map x, ⟨E.map_image.subset (mem_image_of_mem _ (mem_univ x)), ?_⟩,
        E.left_inverse (mem_univ x)⟩
      simpa only [b.restrictToRegion_closedBall_preimage E hW hchart,
        mem_compl_iff, mem_preimage] using hx
  left_inverse := fun x _ => E.left_inverse (mem_univ x)
  right_inverse := fun _ hy => E.right_inverse hy.1
  map_smooth := E.map_smooth.mono (subset_univ _)
  inverse_smooth := E.inverse_smooth.mono inter_subset_left

namespace SmoothDisjointUnionData

variable {n m : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
  {sides : Fin m → GeneralizedSliceCarrier.{u}} {X : GeneralizedSliceCarrier.{u}}

/-- Identify an original piece with its region inside a displayed surgery side.
Source: MT Corollary 15.4, pp. 358-359. -/
noncomputable def pieceInSide (D : SmoothDisjointUnionData pieces X)
    (E : SmoothDisjointUnionData sides X) (i : Fin n) (j : Fin m)
    (hsub : D.region i ⊆ E.region j) :
    SurgeryRegionEquivalence (pieces i) (sides j) univ ((E.identify j).map ⁻¹' D.region i) :=
  (D.identify i).factorThrough (E.identify j) hsub

/-- The original piece selects a clopen region inside each displayed surgery side.
Source: MT Corollary 15.4, pp. 358-359. -/
theorem pieceInSide_region_isClopen (D : SmoothDisjointUnionData pieces X)
    (E : SmoothDisjointUnionData sides X) (i : Fin n) (j : Fin m) :
    IsClopen ((E.identify j).map ⁻¹' D.region i) := by
  have hcont := (contMDiffOn_univ.mp (E.identify j).map_smooth).continuous
  exact ⟨(D.region_closed i).preimage hcont, (D.region_open i).preimage hcont⟩

end SmoothDisjointUnionData

end PoincareMT
