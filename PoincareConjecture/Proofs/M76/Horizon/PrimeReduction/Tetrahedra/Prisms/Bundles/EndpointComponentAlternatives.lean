import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointFiniteTopology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointMidpointGeometry
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.PhysicalIntervalComponentHomology

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry CategoryTheory Limits HomologicalComplex
open scoped Topology
universe u v
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

def subtypeConnectedComponentHomeomorph {E : Type*} [TopologicalSpace E]
    {U : Set E} (x : U) : connectedComponent x ≃ₜ connectedComponentIn U (x : E) :=
  (Topology.IsEmbedding.subtypeVal.homeomorphImage (connectedComponent x)).trans
    (Homeomorph.setCongr (connectedComponentIn_eq_image x.property).symm)

variable {E : Type u} {ι : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι] {A B : ι → Set E}
  (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i) (hH : ∀ i, (H i).IsFinitePL)
  (τ : (⋃ i, prismEnds (H i)) ≃ₜ (⋃ i, prismEnds (H i)))
  (hτ : Function.Involutive τ)
  (W : TwistedInvolutionInterval.Model τ hτ ≃ₜ (⋃ i, B i))
  (hW : ∀ p, W (TwistedInvolutionInterval.boundaryMap τ hτ p) = prismEndpointInclusion H p)

include hH hW

theorem exists_endpoint_in_prism_component (x : (⋃ i, B i : Set E)) :
    ∃ p : (⋃ i, prismEnds (H i) : Set E),
      connectedComponentIn (⋃ i, B i) (p : E) = connectedComponentIn (⋃ i, B i) (x : E) := by
  let : LocallyPathConnectedSpace (⋃ i, prismEnds (H i) : Set E) :=
    locallyPathConnectedSpace_prism_endpoints H hH
  obtain ⟨z,hz⟩ := Quotient.mk_surjective (W.symm x)
  have hq : TwistedInvolutionInterval.projection τ hτ z = W.symm x := hz
  have hmem : TwistedInvolutionInterval.projection τ hτ z ∈
      connectedComponent (TwistedInvolutionInterval.boundaryMap τ hτ z.1) :=
    (TwistedInvolutionInterval.componentImage_eq τ hτ z.1).le
      ⟨z,⟨mem_connectedComponent,mem_univ _⟩,rfl⟩
  have hm := W.continuous.image_connectedComponent_subset
    (TwistedInvolutionInterval.boundaryMap τ hτ z.1) ⟨_,hmem,rfl⟩
  rw [hq,W.apply_symm_apply,hW] at hm
  refine ⟨z.1,?_⟩
  change connectedComponentIn (⋃ i, B i) (prismEndpointInclusion H z.1 : E) = _
  rw [connectedComponentIn_eq_image (prismEndpointInclusion H z.1).property,
    connectedComponentIn_eq_image x.property]
  exact congrArg (fun C => (Subtype.val : (⋃ i, B i : Set E) → E) '' C)
    (connectedComponent_eq hm)

theorem endpoint_invariant_component_homology_retract
    (hfree : ∀ p, τ p ≠ p) (p : (⋃ i, prismEnds (H i) : Set E))
    (hp : τ p ∈ connectedComponent p) (R : ModuleCat.{u} (ZMod 2)) :
    ∃ (i : R ⟶ (TopCat.toSSet.obj
        (TopCat.of (connectedComponentIn (⋃ i, B i) (p : E)))).homology R 1)
      (r : (TopCat.toSSet.obj
        (TopCat.of (connectedComponentIn (⋃ i, B i) (p : E)))).homology R 1 ⟶ R),
      i ≫ r = 𝟙 R := by
  obtain ⟨K,hK,hKs⟩ := exists_finite_prism_endpoint_triangulation H hH
  let : CompactSpace (⋃ i, prismEnds (H i) : Set E) :=
    isCompact_iff_compactSpace.mp (hKs ▸ K.isCompact_space_of_finite hK)
  let : LocallyPathConnectedSpace (⋃ i, prismEnds (H i) : Set E) :=
    locallyPathConnectedSpace_prism_endpoints H hH
  obtain ⟨i,r,hir⟩ := TwistedInvolutionInterval.physical_invariant_component_homology_retract
    τ hτ W hfree p hp R
  let V := (Homeomorph.setCongr (congrArg connectedComponent (hW p))).trans
    (subtypeConnectedComponentHomeomorph (prismEndpointInclusion H p))
  let iso := TopCat.toSSet.mapIso
    (TopCat.isoOfHomeo (X := TopCat.of
      (connectedComponent (W (TwistedInvolutionInterval.boundaryMap τ hτ p))))
      (Y := TopCat.of (connectedComponentIn (⋃ i, B i) (p : E))) V)
  let e := (homologyFunctor (ModuleCat.{u} (ZMod 2)) (.down ℕ) 1).mapIso
    (((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj R).mapIso iso)
  refine ⟨i ≫ e.hom,e.inv ≫ r,?_⟩
  simp only [Category.assoc,Iso.hom_inv_id_assoc,hir]

theorem endpoint_invariant_component_h1_not_isZero
    (hfree : ∀ p, τ p ≠ p) (p : (⋃ i, prismEnds (H i) : Set E))
    (hp : τ p ∈ connectedComponent p) (R : ModuleCat.{u} (ZMod 2)) [Nontrivial R] :
    ¬ IsZero ((TopCat.toSSet.obj
      (TopCat.of (connectedComponentIn (⋃ i, B i) (p : E)))).homology R 1) := by
  obtain ⟨i,r,hir⟩ := endpoint_invariant_component_homology_retract H hH τ hτ W hW hfree p hp R
  intro hz
  have hi : i = 0 := hz.eq_of_tgt i 0
  have hid : 𝟙 R = 0 := hir.symm.trans (by rw [hi,zero_comp])
  have : Subsingleton R := ModuleCat.isZero_iff_subsingleton.mp
    ((IsZero.iff_id_eq_zero R).mpr hid)
  exact false_of_nontrivial_of_subsingleton R

theorem exists_endpoint_exchanged_component_product
    (p : (⋃ i, prismEnds (H i) : Set E)) (hp : τ p ∉ connectedComponent p) :
    ∃ V : (connectedComponent p × unitInterval) ≃ₜ connectedComponentIn (⋃ i, B i) (p : E),
      ∀ z, (V z : E) = W (TwistedInvolutionInterval.projection τ hτ (z.1.val,z.2)) := by
  obtain ⟨K,hK,hKs⟩ := exists_finite_prism_endpoint_triangulation H hH
  let : CompactSpace (⋃ i, prismEnds (H i) : Set E) :=
    isCompact_iff_compactSpace.mp (hKs ▸ K.isCompact_space_of_finite hK)
  let : LocallyPathConnectedSpace (⋃ i, prismEnds (H i) : Set E) :=
    locallyPathConnectedSpace_prism_endpoints H hH
  obtain ⟨V,hV⟩ := TwistedInvolutionInterval.exists_physical_exchanged_component_product τ hτ W p hp
  let T := (Homeomorph.setCongr (congrArg connectedComponent (hW p))).trans
    (subtypeConnectedComponentHomeomorph (prismEndpointInclusion H p))
  exact ⟨V.trans T,fun z => congrArg Subtype.val (hV z)⟩

end PoincareConjecture.M76.PrismBelt
