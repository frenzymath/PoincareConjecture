import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.Projection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.BoundaryReduction.Zero
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.CircleReduction.Construction

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.Annuli

namespace Geometry.OriginalPLTower

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Rim" => Set.ofPred (fun x : P2 => depth 8 x = -1 ∨ depth 8 x = 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}

structure OrdinaryMarkedPlanarAnnulus (s : Stage e S f r C)
    (R : Set M) (F : Bool → Set M) where
  map : P2 → s.Carrier
  original : C(Ann, R)
  original_eq : ∀ x : Ann, (original x : M) = s.projection (map x)
  piecewiseAffine : PolyhedralPLInCharts s.charts map Ann
  proper : ∀ x ∈ Ann, map x ∈ frontier (s.projection ⁻¹' R) ↔ x ∈ Rim
  mark : ∀ b z, s.projection (map (annulusRimPoint b z)) ∈ F b
  essential : ∀ b, ¬ (planarAnnulusRim original b).Nullhomotopic
  compact_double : IsCompact (doubleLocusOn map Ann)
  crossings : ∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → map x = map y →
    Nonempty (RawSourceCrossing s.charts map Ann (s.projection ⁻¹' R) x y)
  unique : ∀ x ∈ Ann, ∀ y ∈ Ann, ∀ z ∈ Ann,
    x ≠ y → x ≠ z → map x = map y → map x = map z → y = z

theorem MarkedEssentialPlanarAnnulus.nonempty_ordinary_projection
    {s t : Stage e S f r C} (step : Step s t)
    {R : Set M} {F : Bool → Set M} (A : MarkedEssentialPlanarAnnulus t R F)
    (he : PLDomain e R) (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true)) :
    Nonempty (OrdinaryMarkedPlanarAnnulus s R F) := by
  obtain ⟨p, original, hp, hv, _, hproper, hmark, hess, _, hc, hcross, hu, _⟩ :=
    A.exists_ordinary_projection step he hF hopen hdis
  exact ⟨⟨p, original, hv, hp, hproper, hmark, hess, hc, hcross, hu⟩⟩

namespace OrdinaryMarkedPlanarAnnulus

variable {s : Stage e S f r C} {R : Set M} {F : Bool → Set M}
  (A : OrdinaryMarkedPlanarAnnulus s R F)

theorem region : MapsTo A.map Ann (s.projection ⁻¹' R) := by
  intro x hx
  change s.projection (A.map x) ∈ R
  rw [← A.original_eq ⟨x, hx⟩]
  exact (A.original ⟨x, hx⟩).property

theorem nonempty_components :
    Nonempty (SourceDoubleComponents s.charts A.map Ann Rim (s.projection ⁻¹' R)) := by
  obtain ⟨K, hK, hKs⟩ := exists_planar_annulus_complex
  have hh := nonempty_sourceDoubleComponents s.compatible K hK Rim
    (show PolyhedralPLInCharts s.charts A.map K.space by simpa only [hKs] using A.piecewiseAffine)
    (show MapsTo A.map K.space (s.projection ⁻¹' R) by simpa only [hKs] using A.region)
    (show IsClosed (doubleLocusOn A.map K.space) by simpa only [hKs] using A.compact_double.isClosed)
    (by simpa only [hKs] using A.proper)
    (by simpa only [hKs] using A.crossings)
    (by simpa only [hKs] using A.unique)
  simpa only [hKs] using hh

noncomputable def boundaryCount : ℕ := doubleBoundaryComponentCount A.map Ann Rim

theorem nonempty_embedded_of_boundaryCount_zero (he : PLDomain e R)
    (hzero : A.boundaryCount = 0) : Nonempty (MarkedEssentialPlanarAnnulus s R F) := by
  obtain ⟨D⟩ := A.nonempty_components
  obtain ⟨B, _, _⟩ := s.exists_embedded_marked_planar_annulus he A.map A.original
    A.piecewiseAffine A.original_eq A.proper A.mark A.essential A.compact_double
    A.crossings A.unique (D.boundary_count_zero_iff_disjoint.mp hzero)
  exact ⟨B⟩

end OrdinaryMarkedPlanarAnnulus
end Geometry.OriginalPLTower
