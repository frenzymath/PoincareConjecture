import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.Ordinary
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.Reparametrization.Reflection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.Reparametrization.Counts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.CrossingFamily

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.Annuli

namespace Geometry.OriginalPLTower

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Rim" => Set.ofPred (fun x : P2 => depth 8 x = -1 ∨ depth 8 x = 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s : Stage e S f r C} {R : Set M} {F : Bool → Set M}

theorem OrdinaryMarkedPlanarAnnulus.exists_depth_reflection
    (A : OrdinaryMarkedPlanarAnnulus s R F) :
    ∃ (H : Ann ≃ₜ Ann) (B : OrdinaryMarkedPlanarAnnulus s R (fun b => F (!b))),
      H.IsFinitePL ∧ Function.Involutive H ∧
      (∀ x : Ann, depth 8 (H x : P2) = -depth 8 (x : P2)) ∧
      (∀ x : Ann, B.map x = A.map (H x)) ∧
      (∀ b z, B.map (annulusRimPoint b z) = A.map (annulusRimPoint (!b) z)) ∧
      B.boundaryCount = A.boundaryCount ∧
      doubleInteriorComponentCount B.map Ann Rim =
        doubleInteriorComponentCount A.map Ann Rim := by
  classical
  obtain ⟨H, hH, hinv, hdepth, hrims⟩ := exists_planar_annulus_depth_reflection
  obtain ⟨G, hG, hGvalue⟩ := hH
  let g := A.map ∘ G
  have hvalue (x : Ann) : g x = A.map (H x) := congrArg A.map (hGvalue x).symm
  have hmap : MapsTo G Ann Ann := by
    intro x hx
    rw [← hGvalue ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hG' := hG
  obtain ⟨K, hK, hKs, _⟩ := hG'
  have hg : PolyhedralPLInCharts s.charts g Ann := by
    have hh := A.piecewiseAffine.comp_finitePiecewiseAffineOn K hK
      (by simpa only [hKs] using hG) (fun x hx => hmap (hKs.subset hx))
    simpa only [hKs] using hh
  have hcompact : IsCompact (doubleLocusOn g Ann) := by
    let := isCompact_iff_compactSpace.mp A.compact_double
    let D := doubleLocusOnSourceHomeomorph H hvalue
    let : CompactSpace (doubleLocusOn g Ann) := D.symm.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hne (x y : Ann) (hxy : (x : P2) ≠ y) : (H x : P2) ≠ H y := by
    intro hh
    exact hxy (congrArg Subtype.val (H.injective (Subtype.ext hh)))
  have hgu : ∀ x ∈ Ann, ∀ y ∈ Ann, ∀ z ∈ Ann,
      x ≠ y → x ≠ z → g x = g y → g x = g z → y = z := by
    intro x hx y hy z hz hxy hxz hxyv hxzv
    have hh := A.unique (H ⟨x, hx⟩) (H ⟨x, hx⟩).property
      (H ⟨y, hy⟩) (H ⟨y, hy⟩).property (H ⟨z, hz⟩) (H ⟨z, hz⟩).property
      (hne _ _ hxy) (hne _ _ hxz)
      ((hvalue ⟨x, hx⟩).symm.trans (hxyv.trans (hvalue ⟨y, hy⟩)))
      ((hvalue ⟨x, hx⟩).symm.trans (hxzv.trans (hvalue ⟨z, hz⟩)))
    exact congrArg Subtype.val (H.injective (Subtype.ext hh))
  obtain ⟨D⟩ := A.nonempty_components
  let mate : doubleLocusOn A.map Ann → doubleLocusOn A.map Ann := fun x =>
    ⟨D.partner ⟨x, D.space.symm.subset x.property⟩,
      D.space.subset (D.partner ⟨x, D.space.symm.subset x.property⟩).property⟩
  have hmate (x : doubleLocusOn A.map Ann) (y : P2) (hy : y ∈ Ann)
      (hxy : A.map x = A.map y) (hne : (x : P2) ≠ y) : y = (mate x : P2) :=
    D.unique ⟨x, D.space.symm.subset x.property⟩ y hy hne hxy
  have hcross : ∀ x ∈ Ann, ∀ y ∈ Ann, x ≠ y → g x = g y →
      Nonempty (RawSourceCrossing s.charts g Ann (s.projection ⁻¹' R) x y) := by
    have hh := raw_source_crossings_of_retained_open_copy isCompact_planar_annulus
      isCompact_planar_annulus (Subset.refl Ann) (Subset.refl Ann)
      (by simp) (by simp) A.piecewiseAffine.continuousOn hg.continuousOn H.symm
      (fun x => (hvalue (H.symm x)).trans
        (congrArg (fun z : Ann => A.map z) (H.apply_symm_apply x)))
      mate hmate (fun _ hx => hx.1) (fun x hx y hy hxy hne => A.crossings x hx y hy hne hxy)
    exact fun x hx y hy hne hxy => hh x hx y hy hxy hne
  have hboundary (x : Ann) : (H x : P2) ∈ Rim ↔ (x : P2) ∈ Rim := by
    change (depth 8 (H x : P2) = -1 ∨ depth 8 (H x : P2) = 1) ↔
      depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1
    rw [hdepth]
    constructor
    · rintro (h | h)
      · right; linarith
      · left; linarith
    · rintro (h | h)
      · right; linarith
      · left; linarith
  let original : C(Ann, R) := A.original.comp ⟨H, H.continuous⟩
  have horiginal (x : Ann) : (original x : M) = s.projection (g x) := by
    rw [hvalue]
    exact A.original_eq (H x)
  have hrim (b : Bool) : planarAnnulusRim original b = planarAnnulusRim A.original (!b) := by
    ext z
    change (A.original (H (annulusRimPoint b z)) : M) = _
    rw [hrims]
    rfl
  let B : OrdinaryMarkedPlanarAnnulus s R (fun b => F (!b)) := {
    map := g
    original := original
    original_eq := horiginal
    piecewiseAffine := hg
    proper := fun x hx => by
      rw [hvalue ⟨x, hx⟩, A.proper _ (H ⟨x, hx⟩).property]
      exact hboundary ⟨x, hx⟩
    mark := fun b z => by rw [hvalue, hrims]; exact A.mark (!b) z
    essential := fun b => by rw [hrim]; exact A.essential (!b)
    compact_double := hcompact
    crossings := hcross
    unique := hgu }
  have hcounts := double_marked_component_counts_source_homeomorph H hvalue hboundary
  refine ⟨H, B, ⟨G, hG, hGvalue⟩, hinv, hdepth, hvalue, ?_, hcounts.1, hcounts.2⟩
  intro b z
  rw [show B.map (annulusRimPoint b z) = A.map (H (annulusRimPoint b z)) from hvalue _, hrims]

end Geometry.OriginalPLTower
