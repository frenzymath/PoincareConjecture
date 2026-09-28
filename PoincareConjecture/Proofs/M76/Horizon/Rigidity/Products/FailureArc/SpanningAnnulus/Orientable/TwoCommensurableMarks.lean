import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.SpanningAnnulus.Orientable.Terminal
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.SpanningAnnulus.MarkedSlope
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.SpanningAnnulus.PlanarReturn
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.Cylinder
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.Tower
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.TwoCommensurableAnnularMarks

set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip Geometry.OriginalPLTower
open Poincare.Topology.Orientation.ProjectivePlane

namespace PoincareConjecture.M76.PeriodicSquare
open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "P2" => (ℝ × ℝ)
local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem SourceSquareMap.exists_two_original_spanning_annuli_of_localOrientation
    {E : Type*} {X ι : Type} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E}
    (M : SourceSquareMap p K) (O : LocalOrientation X)
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) (hcompactR : IsCompact R) (hR : IsConnected R)
    {S₀ S₁ : Set X} (hS₀ : S₀ ⊆ frontier R) (hS₁ : S₁ ⊆ frontier R)
    (hdis : Disjoint S₀ S₁) (x₀ : S₀) (x₁ : S₁)
    (hcomponent₀ : connectedComponentIn (frontier R) (x₀ : X) = S₀)
    (hcomponent₁ : connectedComponentIn (frontier R) (x₁ : X) = S₁)
    (hinj : ∀ x : S₀, Function.Injective (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)) x))
    (k₀ : Path
      ((ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)) x₀)
      ((ContinuousMap.inclusion (hS₁.trans he.closed.frontier_subset)) x₁))
    (hcomm : (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)) x₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k₀.symm).toMonoidHom.comp
        (FundamentalGroup.map
          (ContinuousMap.inclusion (hS₁.trans he.closed.frontier_subset)) x₁)).range))
    (H : K.space ≃ₜ S₀) (F : E → X)
    (hF : PolyhedralPLInCharts e F K.space) (hFval : ∀ x : K.space, F x = (H x : X)) :
    ∃ h : (AddCircle p × AddCircle p) ≃ₜ S₀,
      (∀ z : Square p, h (projection p z) = H (M.map z)) ∧
      ∀ side : Bool,
      ∃ (B : Set X) (hBS : B ⊆ S₀) (A : Ann ≃ₜ B) (j : P2 → X),
        IsCompact B ∧ IsClosed B ∧
        PolyhedralPLInCharts e j Ann ∧ (∀ z : Ann, j z = (A z : X)) ∧
        IsOpen ((Subtype.val : frontier R → X) ⁻¹' originalAnnulusOpenMark A) ∧
        (∀ z : Circle, (A (annulusCoreCircle z) : X) =
          (h (if side then (((p / 2 : ℝ) : AddCircle p),
            AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
              (Fact.out : (0 : ℝ) < p).ne' z)
          else (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
            (Fact.out : (0 : ℝ) < p).ne' z, ((p / 2 : ℝ) : AddCircle p))) : X)) ∧
        ∃ retract : C(S₀, Circle), (∀ z, retract (sourceAnnularCore A hBS z) = z) ∧
        let marks : Bool → Set X := fun b => if b then S₁ else originalAnnulusOpenMark A
        ∃ (g : (V1 × V2) → X) (original : C(source, R)),
          PolyhedralPLInCharts e g source ∧ IsEmbedding (fun x : source => g x) ∧
          (∀ x : source, g x = (original x : X)) ∧
          (∀ x : source, g x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1) ∧
          (∀ b (z : Q2), g (endpoint b,z) ∈ marks b) ∧
          ∀ b, ¬ (sourceAnnulusRim original b).Nullhomotopic := by
  obtain ⟨h,hvalue,hside⟩ := M.exists_two_essential_annuli_in_original_marks_of_commensurable
    he hcompactR hR hS₀ hS₁ hdis x₀ x₁ hcomponent₀ hcomponent₁ hinj k₀ hcomm H F hF hFval
  have hopen₁ := he.isOpen_preimage_frontier_component hcompactR
    (hS₁ x₁.property) hcomponent₁
  refine ⟨h,hvalue,?_⟩
  intro side
  obtain ⟨B,hBS,A,j,hcB,hclosedB,hj,hjval,hopen,hcore,retract,hret,
    g,f,hg,hgf,hmark,hessential,_⟩ := hside side
  let marks : Bool → Set X := fun b => if b then S₁ else originalAnnulusOpenMark A
  have hmarks : ∀ b, marks b ⊆ frontier R := by
    intro b
    cases b
    · exact (originalAnnulusOpenMark_subset A).trans (hBS.trans hS₀)
    · exact hS₁
  have hmarksOpen : ∀ b, IsOpen ((Subtype.val : frontier R → X) ⁻¹' marks b) := by
    intro b
    cases b
    · exact hopen
    · exact hopen₁
  have hmarksDis : Disjoint (marks false) (marks true) :=
    hdis.mono_left ((originalAnnulusOpenMark_subset A).trans hBS)
  obtain ⟨L,_,_,r,C,s0,st,hs0,hreach,k,original,hk,hki,hkv,hrims,hnon,hproper⟩ :=
    exists_terminal_spanning_annulus_of_essential_source_of_localOrientation O he marks hmarks hmarksDis
      g f hg hgf hmark hessential
  obtain ⟨At⟩ := nonempty_markedEssentialPlanarAnnulus_of_cylinder
    k original hk hki hkv hrims hnon hproper
  obtain ⟨A0⟩ := At.nonempty_of_reaches hreach he hmarks hmarksOpen hmarksDis
  obtain ⟨j0,hj0,hji0,_,hv0,hp0,hm0,hn0⟩ := A0.exists_original_embedded_annulus hs0
  refine ⟨B,hBS,A,j,hcB,hclosedB,hj,hjval,hopen,hcore,retract,hret,?_⟩
  exact exists_original_cylinder_of_planar_annulus j0 A0.original hj0 hji0 hv0 hp0 hm0 hn0

end PoincareConjecture.M76.PeriodicSquare
