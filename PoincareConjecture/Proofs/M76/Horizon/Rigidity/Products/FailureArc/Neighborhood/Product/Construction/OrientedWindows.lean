import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.CollaredWindows
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.OrientedTorusPair



set_option autoImplicit false
open Set Geometry Metric
open Poincare.Topology.Orientation.ProjectivePlane

namespace PoincareConjecture.M76.PeriodicSquare
open PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1

theorem exists_marked_product_of_original_periodic_windows
    {E₀ E₁ I J : Type*} {X ι : Type}
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace X] [T2Space X] (O : LocalOrientation X) {e : ι → OpenPartialHomeomorph X V3}
    {R S₀ S₁ : Set X} (hI : IsPLIrreducible e R) (hR : IsCompact R) (hconn : IsConnected R)
    (hS₀ : S₀ ⊆ frontier R) (hS₁ : S₁ ⊆ frontier R) (hdis : Disjoint S₀ S₁)
    (x₀ : S₀) (x₁ : S₁)
    (hcomponent₀ : connectedComponentIn (frontier R) (x₀ : X) = S₀)
    (hcomponent₁ : connectedComponentIn (frontier R) (x₁ : X) = S₁)
    {p₀ p₁ : ℝ} [Fact (0 < p₀)] [Fact (0 < p₁)]
    {K₀ : SimplicialComplex ℝ E₀} {K₁ : SimplicialComplex ℝ E₁}
    (M₀ : SourceSquareMap p₀ K₀) (H₀ : K₀.space ≃ₜ S₀)
    (F₀ : E₀ → X) (hF₀ : PolyhedralPLInCharts e F₀ K₀.space)
    (hFval₀ : ∀ x : K₀.space, F₀ x = (H₀ x : X))
    (h₀ : (AddCircle p₀ × AddCircle p₀) ≃ₜ S₀)
    (hvalue₀ : ∀ z : Square p₀, h₀ (projection p₀ z) = H₀ (M₀.map z))
    (M₁ : SourceSquareMap p₁ K₁) (hK₁ : K₁.faces.Finite) (H₁ : K₁.space ≃ₜ S₁)
    (F₁ : E₁ → X) (hF₁ : PolyhedralPLInCharts e F₁ K₁.space)
    (hFval₁ : ∀ x : K₁.space, F₁ x = (H₁ x : X))
    (h₁ : (AddCircle p₁ × AddCircle p₁) ≃ₜ S₁)
    (hvalue₁ : ∀ z : Square p₁, h₁ (projection p₁ z) = H₁ (M₁.map z))
    (f : Bool → V1 × V2 → X) (q : Bool → Q ≃ₜ AddCircle p₀)
    (hf : ∀ i, PolyhedralPLInCharts e (f i) source)
    (hfi : ∀ i, InjOn (f i) source) (hfR : ∀ i, MapsTo (f i) source R)
    (hproper : ∀ i z, z ∈ source → (f i z ∈ frontier R ↔ z.1 ∈ sphere (0 : V1) 1))
    (hlower : ∀ i (z : Q), f i (endpoint false, z) =
      (h₀ (if i then (((p₀ / 2 : ℝ) : AddCircle p₀), q i z)
        else (q i z, ((p₀ / 2 : ℝ) : AddCircle p₀))) : X))
    (hupper : ∀ i (z : Q), f i (endpoint true, z) ∈ S₁)
    [Finite I] [Finite J] (a b : I → P2) (c d : J → P2)
    (hcd : ∀ j, c j ≠ d j)
    (hselfA : ∀ i k, i ≠ k →
      segment ℝ (a i) (b i) ∩ segment ℝ (a k) (b k) ⊆ {a i, b i})
    (hselfB : ∀ j k, j ≠ k →
      segment ℝ (c j) (d j) ∩ segment ℝ (c k) (d k) ⊆ {c j, d j})
    (hwindow₀ : ∀ z ∈ Icc (-p₁) (2 * p₁) ×ˢ Icc (-p₁) (2 * p₁),
      (h₁ ((z.1 : AddCircle p₁), (z.2 : AddCircle p₁)) : X) ∈
        (fun u => f false (endpoint true, u)) '' Q ↔ z ∈ ⋃ i, segment ℝ (a i) (b i))
    (hwindow₁ : ∀ z ∈ Icc (-p₁) (2 * p₁) ×ˢ Icc (-p₁) (2 * p₁),
      (h₁ ((z.1 : AddCircle p₁), (z.2 : AddCircle p₁)) : X) ∈
        (fun u => f true (endpoint true, u)) '' Q ↔ z ∈ ⋃ j, segment ℝ (c j) (d j)) :
    ∃ H : ((S₀) × unitInterval) ≃ₜ R,
      (∀ x, (H (x,⟨0,by norm_num⟩) : X) = x) ∧
      range (fun x => (H (x,⟨1,by norm_num⟩) : X)) = S₁ ∧
      (∀ x t, (H (x,t) : X) ∈ frontier R ↔ (t : ℝ) = 0 ∨ (t : ℝ) = 1) ∧
      ∃ (s : Finset R) (G : X → (s → ℝ × V3))
        (HG : ((G '' S₀) ×ˢ Set.Icc (0 : ℝ) 1) ≃ₜ (G '' R)),
        Continuous G ∧
        (∀ i, LocallyPiecewiseAffineOn (G ∘ (e i).symm) (e i).target) ∧
        (∀ x ∈ R, ∀ y : X, G x = G y → x = y) ∧
        HG.IsFinitePL ∧ HG.symm.IsFinitePL ∧
        (∀ (x : S₀) (t : unitInterval),
          (HG ⟨(G x,t),⟨mem_image_of_mem G x.property,t.property⟩⟩ : s → ℝ × V3) =
            G (H (x,t))) ∧
        ∀ x ∈ R, ∃ (i : ι) (V : Set X) (b : (s → ℝ × V3) →ᴬ[ℝ] V3),
          IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (b ∘ G) (e i) V := by
  have hclopen : IsClopen ((Subtype.val : frontier R → X) ⁻¹' S₁) :=
    hI.1.isClopen_preimage_frontier_component hR (hS₁ x₁.property) hcomponent₁
  obtain ⟨g, hg, hpoint, hboundary⟩ :=
    exists_original_collared_pair_of_periodic_windows hI.1 hR hconn
      hS₀ hS₁ hdis hclopen M₀ H₀ F₀ hF₀ hFval₀ h₀ hvalue₀
      M₁ hK₁ H₁ F₁ hF₁ hFval₁ h₁ hvalue₁ f q hf hfi hfR hproper hlower hupper
      a b c d hcd hselfA hselfB hwindow₀ hwindow₁
  let S (b : Bool) := if b then S₁ else S₀
  let period (b : Bool) := if b then p₁ else p₀
  have hS (b : Bool) : S b ⊆ frontier R := by cases b <;> assumption
  let x (b : Bool) : S b := by cases b; exact x₀; exact x₁
  have hc (b : Bool) : connectedComponentIn (frontier R) (x b : X) = S b := by
    cases b; exact hcomponent₀; exact hcomponent₁
  have hp (b : Bool) : 0 < period b := by
    cases b
    · exact (Fact.out : 0 < p₀)
    · exact (Fact.out : 0 < p₁)
  have T (b : Bool) : (AddCircle (period b) × AddCircle (period b)) ≃ₜ S b := by
    cases b; exact h₀; exact h₁
  have hmark (i b : Bool) (z : Q) : g i (endpoint b, z) ∈ S b := by
    cases b
    · change g i (endpoint false, z) ∈ S₀
      rw [(hg i).2.2.2.2.1 z, hlower]
      exact (h₀ _).property
    · exact (hg i).2.2.2.2.2 z
  exact exists_marked_product_of_torus_source_annulus_pair_of_localOrientation
    O S hR hI hconn.isPreconnected hS hdis x hc period hp T g
    (fun i => (hg i).1) (fun i => (hg i).2.1) (fun i => (hg i).2.2.1)
    (fun i z => (hg i).2.2.2.1 z z.property) hmark
    (h₀ (((p₀ / 2 : ℝ) : AddCircle p₀), ((p₀ / 2 : ℝ) : AddCircle p₀)))
    hpoint (fun y hy hyR => by
      obtain ⟨C, hCR, _⟩ := hboundary y hy hyR
      exact ⟨C, hCR⟩)

end PoincareConjecture.M76.PeriodicSquare
