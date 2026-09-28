import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.RemovedFrontier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.EndComponents



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductPieces
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

omit [T2Space X] in
theorem removed_longitudinal_slice_subset_closed
    (U : OriginalIntervalTube e R W S T C D f₀ f₁) (r : ℝ)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b)) (t : I) :
    removedLongitudinalSlice U r P t ⊆
      ⋃ i, range (fun z => pieceParameter U P r i (z, t)) := by
  rw [piece_slice_eq]
  apply union_subset_union
  · apply image_mono
    rintro z ⟨⟨hx, hy⟩, ht⟩
    exact ⟨⟨⟨hx.1.le, hx.2.le⟩, ⟨hy.1.le, hy.2.le⟩⟩, ht⟩
  · apply iUnion_mono
    intro b
    apply image_mono
    rintro z ⟨⟨hx, hs⟩, ht⟩
    exact ⟨⟨hx, by linarith [hs.1], hs.2.le⟩, ht⟩

variable (U : OriginalIntervalTube e R W S T C D f₀ f₁)
  (hR : IsCompact R) (he : PLDomain e R)
  {r w : ℝ} (hw : 0 < w) (hr1 : r ≤ 1)
  {j : Bool → V2 → X}
  (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
  (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
  (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r) (hwρ : ∀ b, w / ρ b ≤ 1)
  (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J,
    (P b).map (z, s) = F b (z, (w / ρ b) * s))
  (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
    F side (rimArmPoint b t, s) = prescribedArmBand U r (ρ side) 0 1 side b (s, t))
  (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
    F side (z, s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)

include hR he hw hr1 F ρ hρ hρr hwρ hmark harms hlateral

theorem removed_longitudinal_slice_subset_component
    (t : ℝ) (ht : t = 0 ∨ t = 1) :
    removedLongitudinalSlice U r P t ⊆
      connectedComponentIn (frontier R) (U.map ((0, 0), t)) := by
  have htI : t ∈ I := by rcases ht with rfl | rfl <;> norm_num
  exact (removed_longitudinal_slice_subset_closed U r P ⟨t, htI⟩).trans
    (closed_longitudinal_slice_subset_component U hR he hw hr1 P F ρ hρ hρr hwρ
      hmark harms hlateral ⟨t, htI⟩ ht)

theorem removed_neighborhood_inter_component
    (hdistinct : connectedComponentIn (frontier R) (U.map ((0, 0), 0)) ≠
      connectedComponentIn (frontier R) (U.map ((0, 0), 1)))
    (t : ℝ) (ht : t = 0 ∨ t = 1) :
    (U.map '' openTube r ∪ (P false).openStrip ∪ (P true).openStrip) ∩
      connectedComponentIn (frontier R) (U.map ((0, 0), t)) =
        removedLongitudinalSlice U r P t := by
  have hsplit := removed_neighborhood_inter_original_frontier U hR he hw hr1
    P F ρ hρ hρr hwρ hmark harms hlateral
  have hplace := removed_longitudinal_slice_subset_component U hR he hw hr1
    P F ρ hρ hρr hwρ hmark harms hlateral
  ext x
  constructor
  · intro hx
    have hboth := hsplit.subset ⟨hx.1, connectedComponentIn_subset _ _ hx.2⟩
    have hneq (hs : x ∈ connectedComponentIn (frontier R) (U.map ((0, 0), 0)))
        (ht : x ∈ connectedComponentIn (frontier R) (U.map ((0, 0), 1))) : False :=
      hdistinct ((connectedComponentIn_eq hs).trans (connectedComponentIn_eq ht).symm)
    rcases ht with rfl | rfl
    · exact hboth.elim id (fun h => False.elim (hneq hx.2 (hplace 1 (Or.inr rfl) h)))
    · exact hboth.elim (fun h => False.elim (hneq (hplace 0 (Or.inl rfl) h) hx.2)) id
  · intro hx
    refine ⟨?_, hplace t ht hx⟩
    apply (hsplit.symm.subset ?_).1
    rcases ht with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hx

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
