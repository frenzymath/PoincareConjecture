import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.Normalization
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.Decomposition
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.ProjectedDoubleLocus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.ProjectedRawChart

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.Annuli

namespace Geometry.OriginalPLTower

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Rim" => (Set.ofPred fun x : P2 => depth 8 x = -1 ∨ depth 8 x = 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}

theorem MarkedEssentialPlanarAnnulus.exists_ordinary_projection
    {s t : Stage e S f r C} (step : Step s t)
    {R : Set M} {F : Bool → Set M}
    (A : MarkedEssentialPlanarAnnulus t R F)
    (he : PLDomain e R) (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true)) :
    ∃ (p : P2 → s.Carrier) (original : C(Ann, R)),
      PolyhedralPLInCharts s.charts p Ann ∧
      (∀ x : Ann, (original x : M) = s.projection (p x)) ∧
      MapsTo p Ann (s.projection ⁻¹' R) ∧
      (∀ x ∈ Ann, p x ∈ frontier (s.projection ⁻¹' R) ↔ x ∈ Rim) ∧
      (∀ b z, s.projection (p (annulusRimPoint b z)) ∈ F b) ∧
      (∀ b, ¬ (planarAnnulusRim original b).Nullhomotopic) ∧
      IsLocallyInjective (fun x : Ann => p x) ∧
      IsCompact (doubleLocusOn p Ann) ∧
      (∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → p x = p y →
        Nonempty (RawSourceCrossing s.charts p Ann (s.projection ⁻¹' R) x y)) ∧
      (∀ x ∈ Ann, ∀ y ∈ Ann, ∀ z ∈ Ann,
        x ≠ y → x ≠ z → p x = p y → p x = p z → y = z) ∧
      Nonempty (SourceDoubleComponents s.charts p Ann Rim (s.projection ⁻¹' R)) := by
  obtain ⟨B, hcross⟩ := A.exists_normalized step he hF hopen hdis
  obtain ⟨K, hK, hKs⟩ := exists_planar_annulus_complex
  have hBPL : PolyhedralPLInCharts t.charts B.map K.space := hKs.symm ▸ B.piecewiseAffine
  have hBi : IsEmbedding (fun x : K.space => B.map x) :=
    B.embedding.comp (Homeomorph.setCongr hKs).isEmbedding
  let p := (step.projection ∘ step.inclusion) ∘ B.map
  obtain ⟨hp, hlocal, _, G, _, _, _, _, hGs, hcompact, _⟩ :=
    step.exists_finite_source_double_locus K hK hBPL hBi
  have hpAnn : PolyhedralPLInCharts s.charts p Ann := hKs ▸ hp
  have hvalue (x : P2) : s.projection (p x) = t.projection (B.map x) :=
    (step.original_eq (B.map x)).symm
  have hpR : MapsTo p Ann (s.projection ⁻¹' R) := by
    intro x hx
    change s.projection (p x) ∈ R
    rw [hvalue]
    exact B.region hx
  have hproper (x : P2) (hx : x ∈ Ann) :
      p x ∈ frontier (s.projection ⁻¹' R) ↔ x ∈ Rim := by
    rw [s.frontier_region]
    change s.projection (p x) ∈ frontier R ↔ _
    rw [hvalue]
    have hh := B.proper ⟨x, hx⟩
    rw [t.frontier_region] at hh
    exact hh
  have hraw : ∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → p x = p y →
      Nonempty (RawSourceCrossing s.charts p Ann (s.projection ⁻¹' R) x y) := by
    intro x hx y hy hne hxy
    obtain ⟨T⟩ := hcross ⟨x, hx⟩ ⟨y, hy⟩
      (fun h => hne (congrArg Subtype.val h)) hxy
    exact nonempty_rawSourceCrossing_of_projected B.embedding hx hy hxy T
  have hunique : ∀ x ∈ Ann, ∀ y ∈ Ann, ∀ z ∈ Ann,
      x ≠ y → x ≠ z → p x = p y → p x = p z → y = z := by
    intro x hx y hy z hz hxy hxz hpy hpz
    exact step.projected_source_mate_unique
      (fun a ha b hb hab => congrArg Subtype.val (B.embedding.injective
        (show B.map (⟨a, ha⟩ : Ann) = B.map (⟨b, hb⟩ : Ann) from hab)))
      hx hy hz hxy hxz hpy hpz
  have hc : IsCompact (doubleLocusOn p Ann) := by
    simpa only [hGs, hKs] using hcompact
  have hcomponents : Nonempty (SourceDoubleComponents s.charts p Ann Rim
      (s.projection ⁻¹' R)) := by
    have hh := nonempty_sourceDoubleComponents s.compatible K hK Rim hp
      (fun x hx => hpR (hKs.subset hx))
      (show IsClosed (doubleLocusOn p K.space) by simpa only [hKs] using hc.isClosed)
      (fun x hx => hproper x (hKs.subset hx))
      (by simpa only [hKs] using hraw)
      (by simpa only [hKs] using hunique)
    simpa only [hKs] using hh
  refine ⟨p, B.original, hpAnn, fun x => (B.original_eq x).trans (hvalue x).symm,
    hpR, hproper, ?_, B.essential, ?_, hc, hraw, hunique, hcomponents⟩
  · intro b z
    rw [hvalue]
    exact B.mark b z
  · exact hlocal.comp_right (Homeomorph.setCongr hKs.symm).continuous
      (Homeomorph.setCongr hKs.symm).injective

end Geometry.OriginalPLTower
