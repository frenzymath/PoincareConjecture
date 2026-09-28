import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointComponentAlternatives
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.ExchangedComponentFinitePL
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.FiniteCarrierComponents

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry CategoryTheory Limits HomologicalComplex
open scoped Topology
universe u v
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

def carrierComponentHomeomorph
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {A : Set E} {B : Set F} (T : A ≃ₜ B) (x : A) :
    connectedComponentIn A (x : E) ≃ₜ connectedComponentIn B (T x : F) :=
  (subtypeConnectedComponentHomeomorph x).symm.trans
    ((TwistedInvolutionInterval.physicalComponentHomeomorph T x).trans
      (subtypeConnectedComponentHomeomorph (T x)))

theorem carrierComponentHomeomorph_value
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {A : Set E} {B : Set F} (T : A ≃ₜ B) (x : A) (y : connectedComponentIn A (x : E)) :
    (carrierComponentHomeomorph T x y : F) = T ⟨y,connectedComponentIn_subset _ _ y.property⟩ := by
  have hy : (((subtypeConnectedComponentHomeomorph x).symm y).val : E) = y :=
    congrArg Subtype.val ((subtypeConnectedComponentHomeomorph x).apply_symm_apply y)
  exact congrArg (fun z : A => (T z : F)) (Subtype.ext hy)

theorem carrierComponentHomeomorph_finitePL
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : Set E} {B : Set F} (T : A ≃ₜ B) (hT : T.IsFinitePL) (x : A) :
    (carrierComponentHomeomorph T x).IsFinitePL := by
  obtain ⟨f,⟨K,hK,hKA,hKf⟩,hfv⟩ := hT
  obtain ⟨J,hJ,hJC⟩ := exists_finite_triangulation_connectedComponentIn K hK (x : E)
  have hJspace : J.space = connectedComponentIn A (x : E) := by simpa only [hKA] using hJC
  have hf : FinitePiecewiseAffineOn f A := ⟨K,hK,hKA,hKf⟩
  refine ⟨f,hJspace ▸ hf.restrict J hJ
    (hJspace.subset.trans (connectedComponentIn_subset A (x : E))),?_⟩
  intro y
  exact (carrierComponentHomeomorph_value T x y).trans (hfv _)

theorem transported_endpoint_component_homology_retract
    {E : Type u} {ι : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι] {A B : ι → Set E} {V : Set E}
    (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i) (hH : ∀ i, (H i).IsFinitePL)
    (τ : (⋃ i, prismEnds (H i)) ≃ₜ (⋃ i, prismEnds (H i)))
    (hτ : Function.Involutive τ)
    (W : TwistedInvolutionInterval.Model τ hτ ≃ₜ (⋃ i, B i))
    (hW : ∀ p, W (TwistedInvolutionInterval.boundaryMap τ hτ p) = prismEndpointInclusion H p)
    (hfree : ∀ p, τ p ≠ p) (T : (⋃ i, B i) ≃ₜ V)
    (p : (⋃ i, prismEnds (H i) : Set E)) (hp : τ p ∈ connectedComponent p)
    (R : ModuleCat.{u} (ZMod 2)) :
    ∃ (i : R ⟶ (TopCat.toSSet.obj
        (TopCat.of (connectedComponentIn V (T (prismEndpointInclusion H p) : E)))).homology R 1)
      (r : (TopCat.toSSet.obj
        (TopCat.of (connectedComponentIn V (T (prismEndpointInclusion H p) : E)))).homology R 1 ⟶ R),
      i ≫ r = 𝟙 R := by
  obtain ⟨i,r,hir⟩ := endpoint_invariant_component_homology_retract H hH τ hτ W hW hfree p hp R
  let C := carrierComponentHomeomorph T (prismEndpointInclusion H p)
  let iso := TopCat.toSSet.mapIso
    (TopCat.isoOfHomeo (X := TopCat.of (connectedComponentIn (⋃ i, B i) (p : E)))
      (Y := TopCat.of (connectedComponentIn V (T (prismEndpointInclusion H p) : E))) C)
  let e := (homologyFunctor (ModuleCat.{u} (ZMod 2)) (.down ℕ) 1).mapIso
    (((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj R).mapIso iso)
  exact ⟨i ≫ e.hom,e.inv ≫ r,by simp only [Category.assoc,Iso.hom_inv_id_assoc,hir]⟩

theorem exists_transported_finitePL_exchanged_prism_component
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι] {A B : ι → Set E} {V : Set E}
    (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i) (hH : ∀ i, (H i).IsFinitePL)
    (L : C((⋃ i, B i) × I, (⋃ i, B i)))
    (hL : ∀ i (x : B i) (t : I), (L (⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩,t) : E) =
      prismFiberInterpolation (H i) x t)
    (hpair : ∀ i j (x : E) (hi : x ∈ B i) (hj : x ∈ B j),
      prismFiberEndPair (H i) ⟨x,hi⟩ = prismFiberEndPair (H j) ⟨x,hj⟩)
    (τ : (⋃ i, prismEnds (H i)) ≃ₜ (⋃ i, prismEnds (H i)))
    (hτ : Function.Involutive τ)
    (hτends : ∀ i (x : A i) (b : Bool),
      (τ (prismEndpointLift H i x b) : E) = prismEndMap (H i) x (!b))
    (T : (⋃ i, B i) ≃ₜ V) (hT : T.IsFinitePL)
    (p : (⋃ i, prismEnds (H i) : Set E)) (hp : τ p ∉ connectedComponent p) :
    ∃ U : (connectedComponentIn (⋃ i, prismEnds (H i)) (p : E) ×ˢ I : Set (E × ℝ)) ≃ₜ
        connectedComponentIn V (T (prismEndpointInclusion H p) : E),
      U.IsFinitePL ∧
      ∀ z, (U z : E) = T (prismEndpointFiberMap H L
        (⟨(z : E × ℝ).1,connectedComponentIn_subset _ _ z.property.1⟩,
          ⟨(z : E × ℝ).2,z.property.2⟩)) := by
  obtain ⟨U,hU,hUv⟩ := exists_finitePL_exchanged_prism_component H hH L hL hpair τ hτ hτends p hp
  let C := carrierComponentHomeomorph T (prismEndpointInclusion H p)
  refine ⟨U.trans C,hU.trans (carrierComponentHomeomorph_finitePL T hT _),?_⟩
  intro z
  change (C (U z) : E) = _
  rw [carrierComponentHomeomorph_value]
  exact congrArg (fun y => (T y : E)) (Subtype.ext (hUv z))

end PoincareConjecture.M76.PrismBelt
