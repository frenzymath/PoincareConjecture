import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Ambient.NeighborhoodTopology
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.OriginalTube

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

def OriginalIntervalTube.neighborhood_inclusion
    {X ι : Type*} [TopologicalSpace X] {N R W : Set X}
    {e : ι → OpenPartialHomeomorph X V3}
    {d : ι × N → OpenPartialHomeomorph N V3}
    (hsource : ∀ k, MapsTo (Subtype.val : N → X) (d k).source (e k.1).source)
    (hval : ∀ k, (d k : N → V3) = (e k.1) ∘ Subtype.val)
    (hfront : frontier ((Subtype.val : N → X) ⁻¹' R) =
      (Subtype.val : N → X) ⁻¹' frontier R)
    {S T C D : Set P2} {f₀ f₁ : P2 → N} {g₀ g₁ : P2 → X}
    (h₀ : EqOn ((Subtype.val : N → X) ∘ f₀) g₀ S)
    (h₁ : EqOn ((Subtype.val : N → X) ∘ f₁) g₁ T)
    (U : OriginalIntervalTube d ((Subtype.val : N → X) ⁻¹' R)
      ((Subtype.val : N → X) ⁻¹' W) S T C D f₀ f₁) :
    OriginalIntervalTube e R W S T C D g₀ g₁ := by
  have hmem {A : Set P2} {f : P2 → N} {g : P2 → X}
      (hf : EqOn ((Subtype.val : N → X) ∘ f) g A) (z : N) :
      (z : X) ∈ g '' A ↔ z ∈ f '' A := by
    constructor
    · rintro ⟨x, hx, hh⟩
      exact ⟨x, hx, Subtype.ext ((hf hx).trans hh)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hf hx).symm⟩
  refine {
    first := U.first
    second := U.second
    map := Subtype.val ∘ U.map
    first_pl := U.first_pl
    second_pl := U.second_pl
    first_embedding := U.first_embedding
    second_embedding := U.second_embedding
    first_mapsTo := U.first_mapsTo
    second_mapsTo := U.second_mapsTo
    pl := polyhedralPLInCharts_neighborhood_inclusion hsource hval U.pl
    embedding := IsEmbedding.subtypeVal.comp U.embedding
    mapsTo_region := U.mapsTo_region
    mapsTo_neighborhood := U.mapsTo_neighborhood
    first_sheet := fun p hp => (h₀ (U.first_mapsTo hp)).symm.trans
      (congrArg Subtype.val (U.first_sheet p hp))
    second_sheet := fun p hp => (h₁ (U.second_mapsTo hp)).symm.trans
      (congrArg Subtype.val (U.second_sheet p hp))
    first_preimage := ?_
    second_preimage := ?_
    first_center := U.first_center
    second_center := U.second_center
    first_trace := fun z hz => (hmem h₀ (U.map z)).trans (U.first_trace z hz)
    second_trace := fun z hz => (hmem h₁ (U.map z)).trans (U.second_trace z hz)
    frontier_iff := ?_ }
  · rw [← U.first_preimage]
    ext x
    constructor
    · rintro ⟨hx, z, hz, heq⟩
      exact ⟨hx, z, hz, Subtype.ext (heq.trans (h₀ hx).symm)⟩
    · rintro ⟨hx, z, hz, heq⟩
      exact ⟨hx, z, hz, (congrArg Subtype.val heq).trans (h₀ hx)⟩
  · rw [← U.second_preimage]
    ext x
    constructor
    · rintro ⟨hx, z, hz, heq⟩
      exact ⟨hx, z, hz, Subtype.ext (heq.trans (h₁ hx).symm)⟩
    · rintro ⟨hx, z, hz, heq⟩
      exact ⟨hx, z, hz, (congrArg Subtype.val heq).trans (h₁ hx)⟩
  · intro z hz
    have hh := U.frontier_iff z hz
    rw [hfront] at hh
    exact hh

end PoincareConjecture.M76.Dehn.Annuli
