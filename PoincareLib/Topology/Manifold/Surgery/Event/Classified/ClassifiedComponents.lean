import PoincareLib.Topology.Manifold.Surgery.Event.Whole.WholeComponentGeometry
import PoincareLib.Topology.Manifold.Surgery.Event.Component.ComponentDecomposition
import PoincareLib.Topology.Manifold.Surgery.Event.Region.RegionEquivalences
import PoincareLib.Topology.Manifold.Surgery.Event.Survivors.Survivors
import PoincareLib.Topology.Manifold.Surgery.Event.Whole.WholeComponentAssembly
import PoincareLib.Topology.Manifold.Surgery.Event.Refined.RefinedVanishingReconstruction

/-!
# Reconstruction from mixed whole standard components

Actual sphere-bundle and positive-spaceform components assemble by their
finite disjoint union. A projective double contributes its actual two-piece
connected sum. Strong vanishing therefore has a complete reconstruction
with no survivor pieces.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M38

/-- The actual compact components, each equipped with one of the two
standard geometries, reconstruct any specified diffeomorphic pre-slice
with no survivors. Source: Proposition 15.3, pp. 357-358, whole components. -/
theorem standard_components_conclusion {S A B : GeneralizedSliceCarrier.{u}}
    [IsEmpty B.carrier] (hS : IsCompact (Set.univ : Set S.carrier))
    (hstandard : ∀ x : S.carrier,
      Nonempty (SurgerySphereBundle (componentCarrier S x)) ∨
      Nonempty (SurgeryPositiveSpaceform (componentCarrier S x)))
    (e : Diffeomorph (𝓡 3) (𝓡 3) S.carrier A.carrier ∞) :
    Nonempty (SurgeryTopologyConclusion A B) := by
  classical
  obtain ⟨n, r, D, _⟩ := exists_component_decomposition S hS
  let kind : Fin n → SurgerySummandKind := fun i =>
    if Nonempty (SurgerySphereBundle (componentCarrier S (r i))) then
      .sphereBundle else .spaceform
  have hnon (i : Fin n) : kind i ≠ .survivor := by
    dsimp only [kind]
    split <;> decide
  exact ⟨{
    piece_count := n
    piece := fun i => componentCarrier S (r i)
    piece_compact := fun i => componentCarrier_compact S hS (r i)
    piece_connected := fun i => componentCarrier_connected S (r i)
    kind := kind
    survivor_region := fun _ => ∅
    survivor := fun i hi => (hnon i hi).elim
    survivor_component := fun i hi => (hnon i hi).elim
    survivor_cover := by ext x; exact isEmptyElim x
    survivor_disjoint := fun i _ _ hi _ => (hnon i hi).elim
    bundles := fun i hi => by
      by_cases h : Nonempty (SurgerySphereBundle (componentCarrier S (r i)))
      · exact h
      · simp [kind, h] at hi
    spaceforms := fun i hi => by
      have h : ¬ Nonempty (SurgerySphereBundle (componentCarrier S (r i))) := by
        intro hb
        simp [kind, hb] at hi
      exact (hstandard (r i)).resolve_left h
    reconstruction := {
      initial := A
      disjoint_union := transportUnion D e
      operations := .refl } }⟩

/-- Strong vanishing and the supplied Appendix A theory give a complete
no-survivor reconstruction from the actual late components. Projective
doubles contribute their two projective summands. Source: Proposition 15.3,
pp. 357-358, Assumption (6) and the MT-NECK-SEPARATION correction. -/
theorem canonical_vanishing_reconstruction
    (N : RepairedNeckCapTopologyTheory.{u}) (F : SurgeryFlowData.{u})
    (hF : SurgeryFlowAdmissible F) (T : ℝ) (hT : T ∈ F.surgery_times)
    [IsEmpty (F.slice T).carrier]
    (hepsilon : 2 * F.parameters.epsilon ≤ N.epsilon₀) :
    Nonempty (RawVanishingTopologyWitness F T hT) := by
  obtain ⟨t, _, _, htcompact, hcontrol⟩ :=
    exists_vanishing_late_slice F hF T hT
  have hcanonical (y : (F.slice t.1).carrier) :
      SurgeryCanonicalControl F t.1 y F.parameters.epsilon F.parameters.C := by
    simpa only [Diffeomorph.apply_symm_apply] using
      hcontrol (((F.vanishing_event T hT).pre_identify t).symm y)
  let : CompactSpace (F.slice t.1).carrier := isCompact_univ_iff.mp htcompact
  obtain ⟨n, D, hc, hn, hs, ⟨S⟩⟩ :=
    exists_classifiedAssembly_of_components (F.slice t.1) htcompact
      (fun x => whole_canonical_component_assembly N F t.1 x
        isClosed_connectedComponent.isCompact (fun y _ => hcanonical y)
        (epsilon_le_threshold N F hepsilon))
  exact ⟨vanishingWitnessOfClassifiedAssembly F T hT t D hc hn hs S⟩

end PoincareMT.M38
