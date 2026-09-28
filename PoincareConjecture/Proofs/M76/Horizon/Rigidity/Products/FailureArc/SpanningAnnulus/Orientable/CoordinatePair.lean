import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.SpanningAnnulus.Orientable.TwoCommensurableMarks
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Collars.SpanningAnnulusStraightening
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.TwoCommensurableAnnularMarks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.PLDomainInteriorConnected

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

theorem SourceSquareMap.exists_original_coordinate_pair_of_localOrientation
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
    ∃ (h : (AddCircle p × AddCircle p) ≃ₜ S₀) (g : Bool → V1 × V2 → X)
        (q : Bool → Q2 ≃ₜ AddCircle p),
      (∀ z : Square p, h (projection p z) = H (M.map z)) ∧
      (∀ b, PolyhedralPLInCharts e (g b) source ∧
        InjOn (g b) source ∧ MapsTo (g b) source R ∧
        (∀ z ∈ source, g b z ∈ frontier R ↔ z.1 ∈ sphere (0 : V1) 1) ∧
        (∀ z : Q2, g b (endpoint false, z) =
          (h (if b then (((p / 2 : ℝ) : AddCircle p), q b z)
            else (q b z, ((p / 2 : ℝ) : AddCircle p))) : X)) ∧
        ∀ z : Q2, g b (endpoint true, z) ∈ S₁) := by
  classical
  obtain ⟨h, hvalue, hside⟩ := M.exists_two_original_spanning_annuli_of_localOrientation O
    he hcompactR hR hS₀ hS₁ hdis x₀ x₁ hcomponent₀ hcomponent₁ hinj k₀ hcomm H F hF hFval
  have hex (side : Bool) :
      ∃ (g : V1 × V2 → X) (q : Q2 ≃ₜ AddCircle p),
        PolyhedralPLInCharts e g source ∧ InjOn g source ∧ MapsTo g source R ∧
        (∀ z ∈ source, g z ∈ frontier R ↔ z.1 ∈ sphere (0 : V1) 1) ∧
        (∀ z : Q2, g (endpoint false, z) =
          (h (if side then (((p / 2 : ℝ) : AddCircle p), q z)
            else (q z, ((p / 2 : ℝ) : AddCircle p))) : X)) ∧
        ∀ z : Q2, g (endpoint true, z) ∈ S₁ := by
    obtain ⟨B, hBS, A, j, _, hclosedB, hj, hjval, hopen, hcore, retract, hret,
        g, original, hg, hemb, hval, hproper, hmark, hessential⟩ := hside side
    have hfalse (z : Q2) : g (endpoint false, z) ∈ originalAnnulusOpenMark A := hmark false z
    have htrue (z : Q2) : g (endpoint true, z) ∈ S₁ := hmark true z
    have hother (z : Q2) : g (endpoint true, z) ∉ originalAnnulusOpenMark A := by
      intro hz
      exact Set.disjoint_left.mp hdis
        (hBS (originalAnnulusOpenMark_subset A hz)) (htrue z)
    obtain ⟨G, q, g', moved, _, _, _, _, _, hg', hemb', _,
        hval', hproper', _, hcore', hrim, _, _, _⟩ :=
      CollarIsotopy.exists_original_spanning_annulus_core_straightening
        he hcompactR (he.isConnected_interior hR).nonempty isOpen_univ (subset_univ _)
        A (hBS.trans hS₀) hclosedB j hj hjval hopen g original hg hemb hval hproper hessential
        hfalse hother
    let q' : Q2 ≃ₜ AddCircle p := q.trans
      (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
        (Fact.out : (0 : ℝ) < p).ne')
    refine ⟨g', q', hg', ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy hxy
      exact congrArg Subtype.val (hemb'.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
    · intro x hx
      rw [hval' ⟨x, hx⟩]
      exact (moved ⟨x, hx⟩).property
    · intro x hx
      exact hproper' ⟨x, hx⟩
    · intro z
      exact (hcore' z).trans (hcore (q z))
    · intro z
      have hnew : g' (endpoint true, z) = (sourceAnnulusRim moved true z : X) :=
        hval' ⟨(endpoint true, z), sphere_subset_closedBall (endpoint_mem_sphere true), z.property⟩
      rw [hnew, hrim]
      have hold : (sourceAnnulusRim original true z : X) = g (endpoint true, z) :=
        (hval ⟨(endpoint true, z), sphere_subset_closedBall (endpoint_mem_sphere true), z.property⟩).symm
      rw [hold]
      exact htrue z
  choose g q hg using hex
  exact ⟨h, g, q, hvalue, hg⟩

end PoincareConjecture.M76.PeriodicSquare
