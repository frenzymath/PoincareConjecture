import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.LateralArms

set_option autoImplicit false

open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior TubeExterior.CornerBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

def tubeNormal (j : Bool) (z : C3) : ℝ :=
  (if j then -z.1.2 else z.1.2) - z.1.1

theorem tubeNormal_bandMap_armCoordinates
    (r δ t₀ t₁ : ℝ) (j b : Bool) (p : P2) :
    tubeNormal j (bandMap r (b, if j then !b else b)
      (armCoordinates δ t₀ t₁ b p)) = δ * p.1 := by
  rw [armCoordinates_apply]
  cases j <;> cases b <;>
    simp [tubeNormal, bandMap, arcMap, sign]

theorem tubeNormal_signed_armCoordinates
    (r δ t₀ t₁ : ℝ) (j b o : Bool) (s t : ℝ) :
    tubeNormal j (bandMap r (b, if j then !b else b)
      (armCoordinates δ t₀ t₁ b (sign o * s, t))) = δ * (sign o * s) :=
  tubeNormal_bandMap_armCoordinates r δ t₀ t₁ j b _

theorem tubeNormal_of_map_eq_prescribedArmBand
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r δ t₀ t₁ : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hr1 : r ≤ 1)
    (horder : (t₀ = 0 ∧ t₁ = 1) ∨ (t₀ = 1 ∧ t₁ = 0))
    (j b : Bool) {p : P2} (hp : p ∈ parameter 1) {z : C3} (hz : z ∈ tube)
    (hvalue : U.map z = prescribedArmBand U r δ t₀ t₁ j b p) :
    tubeNormal j z = δ * p.1 := by
  have hparameter := (armCoordinates_bijOn hδ horder b).mapsTo hp
  have hband : bandMap r (b, if j then !b else b)
      (armCoordinates δ t₀ t₁ b p) ∈ tube :=
    closedTube_subset hr1 (lateral_subset r
      (bandMap_mapsTo_lateral hδ.le hδr _ hparameter))
  have heq : z = bandMap r (b, if j then !b else b)
      (armCoordinates δ t₀ t₁ b p) :=
    congrArg Subtype.val (U.embedding.injective
      (a₁ := ⟨z, hz⟩) (a₂ := ⟨_, hband⟩) hvalue)
  rw [heq]
  exact tubeNormal_bandMap_armCoordinates r δ t₀ t₁ j b p

end PoincareConjecture.M76.Dehn.Annuli.RimBands
