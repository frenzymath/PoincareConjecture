import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.NeighborhoodFrontier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.EndRim
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.ConnectedComplement

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution ProductPieces

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem isConnected_endpoint_complement
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r w : ℝ} (hw : 0 < w) (hr1 : r < 1)
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
    (hdis : Disjoint ((P false).map '' (Disk ×ˢ J)) ((P true).map '' (Disk ×ˢ J)))
    (hopen : ∀ b v, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹'
        ((P b).map '' (Disk ×ˢ Ioo (-v) v))))
    (hdistinct : connectedComponentIn (frontier R) (U.map ((0, 0), 0)) ≠
      connectedComponentIn (frontier R) (U.map ((0, 0), 1)))
    (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
    IsConnected (connectedComponentIn (frontier R) (U.map ((0, 0), t)) \
      removedLongitudinalSlice U r P t) := by
  let Z := connectedComponentIn (frontier R) (U.map ((0, 0), t))
  let O : Set Z := (Subtype.val : Z → X) ⁻¹' removedLongitudinalSlice U r P t
  let : PreconnectedSpace Z := isPreconnected_iff_preconnectedSpace.mp
    isPreconnected_connectedComponentIn
  have hclosed (b : Bool) : (P b).closedStrip ⊆ (P b).map '' (Disk ×ˢ J) := by
    apply image_mono
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  obtain ⟨c, γ, hc, _, _, hγ, hrim⟩ := exists_original_panel_end_rim U hR he hw
    hr1.le P F ρ hρ hρr hwρ hmark harms hlateral
      (hdis.mono (hclosed false) (hclosed true)) t ht
  obtain ⟨hO, _, hfront⟩ := removed_longitudinal_slice_relative_frontier U hR he
    hw hr1.le P F ρ hρ hρr hwρ hmark harms hlateral hr1 hdis hopen hdistinct t ht
  change IsOpen O at hO
  change frontier O = _ at hfront
  have hγimage : range γ = (Subtype.val : Z → X) ⁻¹' (c '' Rim) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      change (γ z : X) ∈ c '' Rim
      rw [hγ]
      exact mem_image_of_mem c z.property
    · rintro ⟨z, hz, hzx⟩
      exact ⟨⟨z, hz⟩, Subtype.ext ((hγ ⟨z, hz⟩).trans hzx)⟩
  have hγfront : frontier O = range γ := by rw [hfront, ← hrim, hγimage]
  let : ConnectedSpace Rim := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by simp) (0 : V2) zero_le_one)
  have hfrontconn : IsConnected (frontier O) := by
    rw [hγfront]
    exact isConnected_range γ.continuous
  have hcomp : IsConnected Oᶜ := by
    refine ⟨hfrontconn.nonempty.mono ?_,
      isPreconnected_compl_of_preconnected_frontier hO hfrontconn.isPreconnected⟩
    intro x hx
    rw [hO.frontier_eq] at hx
    exact hx.2
  have himage : (Subtype.val : Z → X) '' Oᶜ = Z \ removedLongitudinalSlice U r P t := by
    ext x
    exact ⟨fun ⟨z, hz, heq⟩ => heq ▸ ⟨z.property, hz⟩,
      fun hx => ⟨⟨x, hx.1⟩, hx.2, rfl⟩⟩
  rw [← himage]
  exact hcomp.image _ continuous_subtype_val.continuousOn

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
