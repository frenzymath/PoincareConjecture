import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.State
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Circles.DetectedRim
import PoincareConjecture.Proofs.M76.Dehn.OriginalRegionBranchCharts










set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.Annuli

namespace Geometry.OriginalPLTower

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Q" => Metric.sphere (0 : V2) 1
local notation "Rim" => Set.ofPred (fun z : P2 => depth 8 z = -1 ∨ depth 8 z = 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}

theorem Stage.exists_embedded_marked_planar_annulus
    (s : Stage e S f r C) {R : Set M} {F : Bool → Set M}
    (he : PLDomain e R) (p : P2 → s.Carrier) (original : C(Ann, R))
    (hp : PolyhedralPLInCharts s.charts p Ann)
    (hvalue : ∀ x : Ann, (original x : M) = s.projection (p x))
    (hproper : ∀ x ∈ Ann, p x ∈ frontier (s.projection ⁻¹' R) ↔ x ∈ Rim)
    (hmark : ∀ b z, s.projection (p (annulusRimPoint b z)) ∈ F b)
    (hessential : ∀ b, ¬ (planarAnnulusRim original b).Nullhomotopic)
    (hcompact : IsCompact (doubleLocusOn p Ann))
    (hcross : ∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → p x = p y →
      Nonempty (RawSourceCrossing s.charts p Ann (s.projection ⁻¹' R) x y))
    (hunique : ∀ x ∈ Ann, ∀ y ∈ Ann, ∀ z ∈ Ann,
      x ≠ y → x ≠ z → p x = p y → p x = p z → y = z)
    (havoid : Disjoint (doubleLocusOn p Ann) Rim) :
    ∃ (B : MarkedEssentialPlanarAnnulus s R F) (q : Bool → Circle ≃ₜ Circle),
      ∀ b z, B.map (annulusRimPoint b z) = p (annulusRimPoint b (q b z)) := by
  have hpR : MapsTo p Ann (s.projection ⁻¹' R) := by
    intro x hx
    change s.projection (p x) ∈ R
    rw [← hvalue ⟨x, hx⟩]
    exact (original ⟨x, hx⟩).property
  have hinterior : MapsTo p (doubleLocusOn p Ann) (interior (s.projection ⁻¹' R)) := by
    intro x hx
    by_contra hn
    exact disjoint_left.mp havoid hx
      ((hproper x hx.1).mp ⟨subset_closure (hpR hx.1), hn⟩)
  obtain ⟨K, hK, hKs⟩ := exists_planar_annulus_complex
  have hdecomp : Nonempty (SourceCircleDecomposition p Ann) := by
    have hh := nonempty_sourceCircleDecomposition s.compatible K hK
      (show PolyhedralPLInCharts s.charts p K.space by simpa only [hKs] using hp)
      (show MapsTo p K.space (s.projection ⁻¹' R) by simpa only [hKs] using hpR)
      (show IsClosed (doubleLocusOn p K.space) by simpa only [hKs] using hcompact.isClosed)
      (by simpa only [hKs] using hinterior)
      (by simpa only [hKs] using hcross)
      (by simpa only [hKs] using hunique)
    simpa only [hKs] using hh
  obtain ⟨D⟩ := hdecomp
  obtain ⟨period, _H, _hperiod, _hH, _hHi, _hHr, _hHb⟩ :=
    ProtectedAnnulus.exists_planar_source_coordinates (S := ProtectedAnnulus.source) rfl
  let projection : C(s.projection ⁻¹' R, R) :=
    ⟨fun x => ⟨s.projection x, x.property⟩,
      (s.projection.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let rim : C(Q, R) := (planarAnnulusRim original false).comp
    ⟨period.symm, period.symm.continuous⟩
  have hrim : ¬ rim.Nullhomotopic := by
    intro h
    have hh : rim.comp ⟨period, period.continuous⟩ = planarAnnulusRim original false := by
      ext z
      exact congrArg (fun x => (planarAnnulusRim original false x : M))
        (period.symm_apply_apply z)
    exact hessential false (hh ▸ h.comp_left ⟨period, period.continuous⟩)
  have hdetector (u : Q) :
      projection ⟨p (annulusRimPoint false (period.symm u)),
        hpR (annulusRimPoint false (period.symm u)).property⟩ = rim u := by
    apply Subtype.ext
    exact (hvalue (annulusRimPoint false (period.symm u))).symm
  obtain ⟨g, q, hg, hgi, hgin, hgproper, hgwhole⟩ :=
    exists_embedded_planar_region_annulus_of_detected_rim s.charts s.compatible period
      (s.plDomain_region he) p hp hpR hproper projection rim hrim hdetector
      D hinterior hcross
  let original' : C(Ann, R) :=
    ⟨fun x => ⟨s.projection (g x), hgin x.property⟩,
      (s.projection.continuous.comp hgi.continuous).subtype_mk _⟩
  have hnewrim (b : Bool) : planarAnnulusRim original' b =
      (planarAnnulusRim original b).comp ⟨q b, (q b).continuous⟩ := by
    ext z
    change s.projection (g (annulusRimPoint b z)) =
      (original (annulusRimPoint b (q b z)) : M)
    rw [hgwhole]
    exact (hvalue _).symm
  let B : MarkedEssentialPlanarAnnulus s R F := {
    map := g
    original := original'
    original_eq := fun _ => rfl
    piecewiseAffine := hg
    embedding := hgi
    proper := fun x => hgproper x x.property
    mark := fun b z => by rw [hgwhole]; exact hmark b (q b z)
    essential := fun b h => by
      have hh : (planarAnnulusRim original' b).comp
          ⟨(q b).symm, (q b).symm.continuous⟩ = planarAnnulusRim original b := by
        rw [hnewrim]
        ext z
        exact congrArg (fun x => (planarAnnulusRim original b x : M))
          ((q b).apply_symm_apply z)
      exact hessential b (hh ▸ h.comp_left ⟨(q b).symm, (q b).symm.continuous⟩) }
  exact ⟨B, q, hgwhole⟩

end Geometry.OriginalPLTower

