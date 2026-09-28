import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Ambient.UnorientedNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Ambient.PairCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Ambient.IntervalTube
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Reduction.MarkedTube
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Reduction.SourceGeometry

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Src" => PolygonalCrossingResolution.source
local notation "Last" => Set.ofPred (fun x : P2 => depth 8 x = 1)

theorem exists_original_reduced_marked_tube_of_hausdorff
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X} (F : Bool → Set X)
    (hR : IsCompact R) (he : PLDomain e R) (hF : ∀ b, F b ⊆ frontier R)
    (hFopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F true))
    (hFdis : Disjoint (F false) (F true)) {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f Ann) (hg : PolyhedralPLInCharts e g Ann)
    (hfi : InjOn f Ann) (hgi : InjOn g Ann) (hfR : MapsTo f Ann R) (hgR : MapsTo g Ann R)
    (hfp : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (hgp : ∀ x ∈ Ann, g x ∈ frontier R ↔ x ∈ frontier Ann)
    (hfmark : ∀ x ∈ Ann, f x ∈ F false ↔ depth 8 x = -1)
    (hgmark : ∀ x ∈ Ann, g x ∈ F false ↔ depth 8 x = -1)
    (hflast : MapsTo f (Ann ∩ Last) (F true)) (hglast : MapsTo g (Ann ∩ Last) (F true))
    (p : X) (hpoint : ((f '' Ann) ∩ (g '' Ann)) ∩ F false = {p})
    (hboundary : ∀ x ∈ Ann ∩ frontier Ann, f x ∈ g '' Ann →
      ∃ B : OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ Ann \ frontier Ann, f x ∈ g '' Ann →
      Nonempty (OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) false))
    (hW : IsOpen W) (hCW : f '' Ann ∩ g '' Ann ⊆ W) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k Ann ∧ IsEmbedding (fun x : Ann => k x) ∧
      MapsTo k Ann R ∧ (∀ x ∈ Ann, k x ∈ frontier R ↔ x ∈ frontier Ann) ∧
      ∃ V : OriginalIntervalTube e R W Ann Ann
          (Ann ∩ g ⁻¹' (k '' Ann)) (Ann ∩ k ⁻¹' (g '' Ann)) g k,
        V.map ((0, 0), 0) = p ∧ V.map ((0, 0), 1) ∈ F true ∧
        (∀ q ∈ Src, depth 8 (V.first q) = -1 ↔ q.1 = 0) ∧
        (∀ q ∈ Src, depth 8 (V.first q) = 1 ↔ q.1 = 1) ∧
        (∀ q ∈ Src, depth 8 (V.second q) = -1 ↔ q.1 = 0) ∧
        (∀ q ∈ Src, depth 8 (V.second q) = 1 ↔ q.1 = 1) := by
  classical
  obtain ⟨N, hN, hRN, hm, d, hd, hdc, hds, hdt, hdv, hdi, hfront, hint, hRc⟩ :=
    he.exists_metrizable_neighborhood hR
  let : TopologicalSpace.MetrizableSpace N := hm
  let : MetricSpace N := TopologicalSpace.metrizableSpaceMetric N
  let v : N → X := Subtype.val
  let R' := v ⁻¹' R
  let F' (b : Bool) := v ⁻¹' F b
  obtain ⟨K, hK, hKs⟩ := exists_planar_annulus_complex
  have hpR : p ∈ R := he.closed.frontier_subset
    (hF false (hpoint.symm.subset (mem_singleton p)).2)
  let p' : N := ⟨p, hRN hpR⟩
  obtain ⟨x, hx, _⟩ := (hpoint.symm.subset (mem_singleton p)).1.1
  let x₀ : K.space := ⟨x, hKs.symm.subset hx⟩
  obtain ⟨f', hf', hfi', hfR', hfv, hfim, hfp'⟩ :=
    exists_original_parameter_in_neighborhood hRN d hdc hdv hfront K hK x₀ f
      (hKs.symm ▸ hf) (hKs.symm ▸ hfi) (hKs.symm ▸ hfR)
  obtain ⟨g', hg', hgi', hgR', hgv, hgim, hgp'⟩ :=
    exists_original_parameter_in_neighborhood hRN d hdc hdv hfront K hK x₀ g
      (hKs.symm ▸ hg) (hKs.symm ▸ hgi) (hKs.symm ▸ hgR)
  rw [hKs] at hf' hfi' hfR' hfv hfim hfp' hg' hgi' hgR' hgv hgim hgp'
  have hfv' (z) (hz : z ∈ Ann) : (f' z : X) = f z := hfv hz
  have hgv' (z) (hz : z ∈ Ann) : (g' z : X) = g z := hgv hz
  have hF' (b) : F' b ⊆ frontier R' := by
    intro z hz
    exact hfront.symm.subset (hF b hz)
  have hFopen' : IsOpen ((Subtype.val : frontier R' → N) ⁻¹' F' true) := by
    let q : frontier R' → frontier R := fun z => ⟨z.val.val, hfront.subset z.property⟩
    have hq : Continuous q :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact hFopen.preimage hq
  have hdis' : Disjoint (F' false) (F' true) := hFdis.preimage v
  have hp' : ((f' '' Ann) ∩ (g' '' Ann)) ∩ F' false = {p'} := by
    rw [hfim, hgim]
    change (v ⁻¹' (f '' Ann) ∩ v ⁻¹' (g '' Ann)) ∩ v ⁻¹' F false = {p'}
    rw [← preimage_inter, ← preimage_inter, hpoint]
    ext z
    change (z : X) = (p' : X) ↔ z = p'
    exact Subtype.val_injective.eq_iff
  have hboundary' : ∀ z ∈ Ann ∩ frontier Ann, f' z ∈ g' '' Ann →
      ∃ B : OriginalSurfacePairChart d (g' '' Ann) (f' '' Ann) (f' z) true,
        (∀ w ∈ B.coordinates.source, B.chart.symm w ∈ R' ↔ 0 ≤ (B.coordinates w).1.2) ∧
        ∀ w ∈ B.coordinates.source, B.chart.symm w ∈ frontier R' ↔ (B.coordinates w).1.2 = 0 := by
    intro z hz hzg
    have hzg' : f z ∈ g '' Ann := by
      rw [hgim] at hzg
      exact (hfv' z hz.1) ▸ hzg
    obtain ⟨C, hCR, hCF⟩ :
        ∃ C : OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f' z : X) true,
          (∀ w ∈ C.coordinates.source, C.chart.symm w ∈ R ↔ 0 ≤ (C.coordinates w).1.2) ∧
          ∀ w ∈ C.coordinates.source, C.chart.symm w ∈ frontier R ↔ (C.coordinates w).1.2 = 0 := by
      rw [hfv' z hz.1]
      exact hboundary z hz hzg'
    obtain ⟨B, hsub, hcoord, hinv⟩ := C.exists_neighborhood_restriction hN d hdt hdi (f' z)
    rw [hgim, hfim]
    refine ⟨B, ?_, ?_⟩
    · intro w hw
      change (B.chart.symm w : X) ∈ R ↔ _
      rw [hinv w hw, hcoord]
      exact hCR w (hsub hw)
    · intro w hw
      rw [hfront]
      change (B.chart.symm w : X) ∈ frontier R ↔ _
      rw [hinv w hw, hcoord]
      exact hCF w (hsub hw)
  have hinterior' : ∀ z ∈ Ann \ frontier Ann, f' z ∈ g' '' Ann →
      Nonempty (OriginalSurfacePairChart d (g' '' Ann) (f' '' Ann) (f' z) false) := by
    intro z hz hzg
    have hzg' : f z ∈ g '' Ann := by
      rw [hgim] at hzg
      exact (hfv' z hz.1) ▸ hzg
    obtain ⟨C⟩ := hinterior z hz hzg'
    have C' : OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f' z : X) false :=
      (hfv' z hz.1).symm ▸ C
    obtain ⟨B, _⟩ := C'.exists_neighborhood_restriction hN d hdt hdi (f' z)
    rw [← hgim, ← hfim] at B
    exact ⟨B⟩
  have hfproper : ∀ z ∈ Ann, f' z ∈ frontier R' ↔ z ∈ frontier Ann :=
    fun z hz => (hfp' z hz).trans (hfp z hz)
  have hgproper : ∀ z ∈ Ann, g' z ∈ frontier R' ↔ z ∈ frontier Ann :=
    fun z hz => (hgp' z hz).trans (hgp z hz)
  have hfmark' : ∀ z ∈ Ann, f' z ∈ F' false ↔ depth 8 z = -1 := by
    intro z hz
    change (f' z : X) ∈ F false ↔ _
    rw [hfv' z hz]
    exact hfmark z hz
  have hgmark' : ∀ z ∈ Ann, g' z ∈ F' false ↔ depth 8 z = -1 := by
    intro z hz
    change (g' z : X) ∈ F false ↔ _
    rw [hgv' z hz]
    exact hgmark z hz
  have hflast' : MapsTo f' (Ann ∩ Last) (F' true) := by
    intro z hz
    change (f' z : X) ∈ F true
    rw [hfv' z hz.1]
    exact hflast hz
  have hglast' : MapsTo g' (Ann ∩ Last) (F' true) := by
    intro z hz
    change (g' z : X) ∈ F true
    rw [hgv' z hz.1]
    exact hglast hz
  have hCW' : f' '' Ann ∩ g' '' Ann ⊆ v ⁻¹' W := by
    rw [hfim, hgim]
    exact fun _ hz => hCW hz
  obtain ⟨k', hk', hki', hkR', _, _, hkp', _, _, _, _, _, _, _, U,
      hu0, hu1, _, _, hs00, hs01, hs10, hs11, _⟩ :=
    exists_original_reduced_annulus_with_marked_interval_tube F' hRc hd hF' hFopen'
      hdis' hf' hg' hfi' hgi' hfR' hgR' hfproper hgproper hfmark' hgmark'
      hflast' hglast' p' hp' hboundary' hinterior' (hW.preimage continuous_subtype_val) hCW'
  let k : P2 → X := v ∘ k'
  have hmem (z : N) : (z : X) ∈ k '' Ann ↔ z ∈ k' '' Ann := by
    constructor
    · rintro ⟨w, hw, hval⟩
      exact ⟨w, hw, Subtype.ext hval⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
  have hC : Ann ∩ g' ⁻¹' (k' '' Ann) = Ann ∩ g ⁻¹' (k '' Ann) := by
    ext z
    constructor
    · rintro ⟨hz, hh⟩
      refine ⟨hz, ?_⟩
      change g z ∈ k '' Ann
      rw [← hgv' z hz]
      exact (hmem (g' z)).mpr hh
    · rintro ⟨hz, hh⟩
      exact ⟨hz, (hmem (g' z)).mp ((hgv' z hz).symm ▸ hh)⟩
  have hD : Ann ∩ k' ⁻¹' (g' '' Ann) = Ann ∩ k ⁻¹' (g '' Ann) := by
    rw [hgim]
    rfl
  let U' := U.neighborhood_inclusion hds hdv hfront hgv (fun _ _ => rfl : EqOn (v ∘ k') k Ann)
  let V : OriginalIntervalTube e R W Ann Ann
      (Ann ∩ g ⁻¹' (k '' Ann)) (Ann ∩ k ⁻¹' (g '' Ann)) g k :=
    { first := U'.first
      second := U'.second
      map := U'.map
      first_pl := U'.first_pl
      second_pl := U'.second_pl
      first_embedding := U'.first_embedding
      second_embedding := U'.second_embedding
      first_mapsTo := U'.first_mapsTo
      second_mapsTo := U'.second_mapsTo
      pl := U'.pl
      embedding := U'.embedding
      mapsTo_region := U'.mapsTo_region
      mapsTo_neighborhood := U'.mapsTo_neighborhood
      first_sheet := U'.first_sheet
      second_sheet := U'.second_sheet
      first_preimage := U'.first_preimage
      second_preimage := U'.second_preimage
      first_center := U'.first_center.trans hC
      second_center := U'.second_center.trans hD
      first_trace := U'.first_trace
      second_trace := U'.second_trace
      frontier_iff := U'.frontier_iff }
  refine ⟨k, polyhedralPLInCharts_neighborhood_inclusion hds hdv hk',
    IsEmbedding.subtypeVal.comp hki', hkR', ?_, V, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hh := hkp' z hz
    rw [hfront] at hh
    exact hh
  · exact congrArg Subtype.val hu0
  · exact hu1
  · exact hs00
  · exact hs01
  · exact hs10
  · exact hs11

end PoincareConjecture.M76.Dehn.Annuli
