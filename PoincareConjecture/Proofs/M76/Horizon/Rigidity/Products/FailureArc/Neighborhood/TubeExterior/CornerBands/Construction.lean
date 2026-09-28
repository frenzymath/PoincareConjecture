import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CornerBands.Incidence
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CutGeometry
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior.CornerBands
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

noncomputable def originalBandMap
    (U : OriginalIntervalTube e R W S T C D f₀ f₁) (r : ℝ) (i : Bool × Bool) : P2 → X :=
  U.map ∘ bandMap r i

theorem originalBandMap_properties
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r) (hr1 : r ≤ 1) (i : Bool × Bool) :
    PolyhedralPLInCharts e (originalBandMap U r i) (parameter δ) ∧
      IsEmbedding (fun p : parameter δ => originalBandMap U r i p) ∧
      MapsTo (originalBandMap U r i) (parameter δ) (frontier (R \ U.map '' openTube r)) ∧
      (∀ p ∈ parameter δ, originalBandMap U r i p ∈ f₀ '' S ↔ i.1 = i.2 ∧ p.1 = 0) ∧
      (∀ p ∈ parameter δ, originalBandMap U r i p ∈ f₁ '' T ↔ i.1 ≠ i.2 ∧ p.1 = 0) ∧
      (∀ p ∈ parameter δ, originalBandMap U r i p ∈ frontier R ↔ p.2 = 0 ∨ p.2 = 1) ∧
      originalBandMap U r i '' parameter δ = U.map '' band r δ i := by
  have hmap : MapsTo (bandMap r i) (parameter δ) tube :=
    fun p hp => closedTube_subset hr1 (lateral_subset r
      (bandMap_mapsTo_lateral hδ.le hδr.le i hp))
  have hPL : PolyhedralPLInCharts e (originalBandMap U r i) (parameter δ) := by
    have hf := bandMap_finitePL r hδ i
    have hf' := hf
    obtain ⟨K,hK,hKs,_⟩ := hf'
    have h := U.pl.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ hf)
      (fun p hp => hmap (hKs.subset hp))
    exact hKs ▸ h
  let : CompactSpace (parameter δ) :=
    isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  have hinj : InjOn (originalBandMap U r i) (parameter δ) := by
    intro p hp q hq hpq
    apply bandMap_injective r i
    exact congrArg Subtype.val (U.embedding.injective
      (a₁ := ⟨_,hmap hp⟩) (a₂ := ⟨_,hmap hq⟩) hpq)
  refine ⟨hPL,?_,?_,?_,?_,?_,?_⟩
  · exact (hPL.continuousOn.domRestrict.isClosedEmbedding
      (fun p q h => Subtype.ext (hinj p.property q.property h))).isEmbedding
  · intro p hp
    rw [TubeExterior.OriginalIntervalTube.frontier_exterior U hR he (hδ.trans hδr) hr1]
    exact Or.inr ⟨_,bandMap_mapsTo_lateral hδ.le hδr.le i hp,rfl⟩
  · intro p hp
    exact (U.first_trace _ (hmap hp)).trans (first_sheet_iff hδ.le hδr i hp.1)
  · intro p hp
    exact (U.second_trace _ (hmap hp)).trans (second_sheet_iff hδ.le hδr i hp.1)
  · intro p hp
    exact U.frontier_iff _ (hmap hp)
  · change (U.map ∘ bandMap r i) '' _ = _
    rw [← bandMap_image hδ.le i,image_image]
    rfl

omit [T2Space X] in
theorem original_bands_pairwise_disjoint
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r δ : ℝ} (hδ : 0 ≤ δ) (hδr : δ < r) (hr1 : r ≤ 1) :
    Pairwise (fun i j : Bool × Bool => Disjoint (U.map '' band r δ i) (U.map '' band r δ j)) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro x ⟨z,hz,rfl⟩ ⟨w,hw,hwz⟩
  have hsub (a : Bool × Bool) : band r δ a ⊆ tube :=
    (band_subset_lateral hδ hδr.le a).trans ((lateral_subset r).trans (closedTube_subset hr1))
  have heq : w = z := congrArg Subtype.val (U.embedding.injective
    (a₁ := ⟨w,hsub j hw⟩) (a₂ := ⟨z,hsub i hz⟩) hwz)
  exact disjoint_left.mp (bands_pairwise_disjoint hδr hij) hz (heq ▸ hw)

omit [T2Space X] in
theorem originalBandMap_first_center
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (b : Bool) {t : ℝ} (ht : t ∈ Icc 0 1) :
    originalBandMap U r (b,b) (0,t) = f₀ (U.first (t,sign b * r)) := by
  have hp : (t,sign b * r) ∈ source := by
    refine ⟨ht,?_⟩
    cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul]
    all_goals exact ⟨by linarith,by linarith⟩
  rw [U.first_sheet _ hp]
  simp [originalBandMap,bandMap,originalStripSheet]

omit [T2Space X] in
theorem originalBandMap_second_center
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (b : Bool) {t : ℝ} (ht : t ∈ Icc 0 1) :
    originalBandMap U r (b,!b) (0,t) = f₁ (U.second (t,sign b * r)) := by
  have hp : (t,sign b * r) ∈ source := by
    refine ⟨ht,?_⟩
    cases b <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul]
    all_goals exact ⟨by linarith,by linarith⟩
  rw [U.second_sheet _ hp]
  cases b <;> simp [originalBandMap,bandMap,originalStripSheet,sign]

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior.CornerBands
