import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.PlanarSource
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.PositionData

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace Geometry.OriginalPLTower

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem Step.exists_planar_annulus_position_data
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {j : P2 → t.Carrier} (hj : PolyhedralPLInCharts t.charts j Ann)
    (hji : IsEmbedding (fun x : Ann => j x))
    (hjR : MapsTo j Ann (t.projection ⁻¹' R))
    (hproper : ∀ x : Ann, j x ∈ frontier (t.projection ⁻¹' R) ↔
      depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1)
    (hjF : ∀ x : Ann, (depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1) →
      t.projection (j x) ∈ Fmark) :
    ∃ K A : SimplicialComplex ℝ P2,
      K.space = Ann ∧ A.space = {x | depth 8 x = -1 ∨ depth 8 x = 1} ∧
      Nonempty (MarkedSurfacePositionData step K A j R Fmark) := by
  obtain ⟨K, A, hK, hA, hKs, hAs, hAK, hKd, hAd⟩ :=
    PoincareConjecture.M76.Dehn.exists_planar_annulus_rim_complexes
  have hjK : PolyhedralPLInCharts t.charts j K.space := by rwa [hKs]
  have hjiK : IsEmbedding (fun x : K.space => j x) :=
    hji.comp (Homeomorph.setCongr hKs).isEmbedding
  have hjKR : MapsTo j K.space (t.projection ⁻¹' R) := fun x hx => hjR (hKs.subset hx)
  have hproperK (x : K.space) :
      j x ∈ frontier (t.projection ⁻¹' R) ↔ (x : P2) ∈ A.space := by
    rw [hAs]
    exact hproper ⟨x, hKs.subset x.property⟩
  have hjAF (x : A.space) : t.projection (j x) ∈ Fmark :=
    hjF ⟨x, hKs.subset (hAK x.property)⟩ (hAs.subset x.property)
  exact ⟨K, A, hKs, hAs,
    step.nonempty_markedSurfacePositionData K A hK hA hKd hAd hAK
      he hF hopen hjK hjiK hjKR hproperK hjAF⟩

end Geometry.OriginalPLTower
