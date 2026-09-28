import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.Position
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Composition.Construction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Composition.RimHomotopy



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}

theorem MarkedEssentialPlanarAnnulus.exists_normalized
    {s t : Stage e S f r C} (step : Step s t)
    {R : Set M} {F : Bool → Set M}
    (A : MarkedEssentialPlanarAnnulus t R F)
    (he : PLDomain e R) (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true)) :
    ∃ B : MarkedEssentialPlanarAnnulus t R F,
      ∀ x y : Ann, x ≠ y →
        (step.projection ∘ step.inclusion) (B.map x) =
          (step.projection ∘ step.inclusion) (B.map y) →
        Nonempty (ProjectedSourceCrossing s.charts (step.projection ∘ step.inclusion)
          B.map Ann (s.projection ⁻¹' R) x y) := by
  obtain ⟨K, Kboundary, hK, hKb, ⟨D⟩⟩ := A.exists_position_data step he hF hopen
  have hAnn : D.K.space = Ann := D.source_space.trans hK
  obtain ⟨repairs⟩ := D.nonempty_finite_marked_annulus_repairs hAnn hKb he
    (union_subset (hF false) (hF true)) ((hopen false).union (hopen true))
  let g := repairs.composite 1 ∘ D.endpoint
  obtain ⟨hgPL, hgi, hgR, hproper, _⟩ := repairs.endpoint_properties
  have hgPLAnn : PolyhedralPLInCharts t.charts g Ann := hAnn ▸ hgPL
  have hgiAnn : IsEmbedding (fun x : Ann => g x) :=
    hgi.comp (Homeomorph.setCongr hAnn.symm).isEmbedding
  let original : C(Ann, R) :=
    ⟨fun x => ⟨t.projection (g x), hgR (hAnn.symm.subset x.property)⟩,
      (t.projection.continuous.comp hgiAnn.continuous).subtype_mk _⟩
  have hrims (b : Bool) : ∃ gamma' : C(Circle, F b),
      (∀ z, (gamma' z : M) = t.projection (g (annulusRimPoint b z))) ∧
      ¬ (planarAnnulusRim original b).Nullhomotopic := by
    let u : C(Circle, Kboundary.space) :=
      ⟨fun z => ⟨annulusRimPoint b z, hKb.symm.subset (by
          simp only [mem_ofPred_eq, depth_annulusRimPoint]
          cases b <;> simp)⟩,
        (continuous_subtype_val.comp (continuous_annulusRimPoint b)).subtype_mk _⟩
    let gamma : C(Circle, F b) :=
      ⟨fun z => ⟨t.projection (A.map (annulusRimPoint b z)), A.mark b z⟩,
        (t.projection.continuous.comp
          (A.embedding.continuous.comp (continuous_annulusRimPoint b))).subtype_mk _⟩
    let projection : C(F b, R) :=
      ⟨fun x => ⟨x, he.closed.frontier_subset (hF b x.property)⟩,
        continuous_subtype_val.subtype_mk _⟩
    have hess : ¬ (projection.comp gamma).Nullhomotopic := by
      have hh : projection.comp gamma = planarAnnulusRim A.original b := by
        apply ContinuousMap.ext
        intro z
        exact Subtype.ext (A.original_eq (annulusRimPoint b z)).symm
      rw [hh]
      exact A.essential b
    obtain ⟨gamma', _, hvalue, hnon⟩ :=
      repairs.exists_original_essential_marked_rim F hF hopen hdis b u gamma
        (fun _ => rfl) projection hess
    refine ⟨gamma', hvalue, ?_⟩
    have hh : projection.comp gamma' = planarAnnulusRim original b := by
      apply ContinuousMap.ext
      intro z
      exact Subtype.ext (hvalue z)
    rwa [hh] at hnon
  let B : MarkedEssentialPlanarAnnulus t R F := {
    map := g
    original := original
    original_eq := fun _ => rfl
    piecewiseAffine := hgPLAnn
    embedding := hgiAnn
    proper := fun x => (hproper x (hAnn.symm.subset x.property)).trans
      (by rw [hKb]; rfl)
    mark := fun b z => by
      obtain ⟨gamma', hvalue, _⟩ := hrims b
      rw [← hvalue z]
      exact (gamma' z).property
    essential := fun b => (hrims b).choose_spec.2 }
  refine ⟨B, ?_⟩
  intro x y hne hxy
  have hh := repairs.nonempty_projected_crossing
    ⟨x, hAnn.symm.subset x.property⟩ ⟨y, hAnn.symm.subset y.property⟩
    (fun h => hne (Subtype.ext (congrArg (fun z : D.K.space => (z : P2)) h))) hxy
  simpa only [hAnn] using hh

end Geometry.OriginalPLTower
