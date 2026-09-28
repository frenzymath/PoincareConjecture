import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Extension.TorusMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Extension.AnnulusPair



set_option autoImplicit false
open Set Geometry Metric Topology

namespace PoincareConjecture.M76.PeriodicSquare
open Dehn.ProtectedAnnulus
local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "P2" => (ℝ × ℝ)

theorem SourceSquareMap.exists_original_pair_with_translated_upper_rim
    {E X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S₀ S₁ : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hconn : IsConnected R)
    (hS₀ : S₀ ⊆ frontier R) (hS₁ : S₁ ⊆ frontier R) (hdis : Disjoint S₀ S₁)
    (hS : IsClopen ((Subtype.val : frontier R → X) ⁻¹' S₁))
    {p : ℝ} [Fact (0 < p)] {A : SimplicialComplex ℝ E}
    (model : SourceSquareMap p A) (hA : A.faces.Finite)
    (F : E → X) (hF : PolyhedralPLInCharts e F A.space)
    (H : A.space ≃ₜ S₁) (hFval : ∀ x : A.space, F x = (H x : X))
    (h : (AddCircle p × AddCircle p) ≃ₜ S₁)
    (hvalue : ∀ z : Square p, h (projection p z) = H (model.map z)) (v : P2)
    (f : Bool → V1 × V2 → X)
    (hf : ∀ b, PolyhedralPLInCharts e (f b) source)
    (hi : ∀ b, InjOn (f b) source) (hfR : ∀ b, MapsTo (f b) source R)
    (hproper : ∀ b x, x ∈ source →
      (f b x ∈ frontier R ↔ x.1 ∈ sphere (0 : V1) 1))
    (hlower : ∀ b (u : Q), f b (endpoint false, u) ∈ S₀)
    (hupper : ∀ b (u : Q), f b (endpoint true, u) ∈ S₁) :
    ∃ j : Bool → V1 × V2 → X,
      (∀ b, PolyhedralPLInCharts e (j b) source) ∧
      (∀ b, InjOn (j b) source) ∧ (∀ b, MapsTo (j b) source R) ∧
      (∀ b x, x ∈ source → (j b x ∈ frontier R ↔ x.1 ∈ sphere (0 : V1) 1)) ∧
      (∀ b (u : Q), j b (endpoint false, u) = f b (endpoint false, u)) ∧
      (∀ u : Q, j false (endpoint true, u) = f false (endpoint true, u)) ∧
      (∀ u : Q, j true (endpoint true, u) =
        (h (h.symm ⟨f true (endpoint true, u), hupper true u⟩ +
          ((v.1 : AddCircle p), (v.2 : AddCircle p))) : X)) ∧
      ∀ b (u : Q), j b (endpoint true, u) ∈ S₁ := by
  obtain ⟨M, _, _, _, hMPL, htranslate, hout, hfront, _⟩ :=
    model.exists_original_torus_translation_motion he hR hconn hS₁ hS hA F hF H hFval h hvalue v
  have hfix (x : R) (hx : (x : X) ∈ S₀) : M 1 x = x :=
    hout 1 x (hS₀ hx) (disjoint_left.mp hdis hx)
  obtain ⟨j, _, _, hj, hji, hjR, hjp, hjlo, hjfalse, hjtrue⟩ :=
    exists_original_moved_annulus_pair (M 1) (hMPL 1).1 (hfront 1) hfix
      f hf hi hfR hproper hlower
  have htrue (u : Q) : j true (endpoint true, u) =
      (h (h.symm ⟨f true (endpoint true, u), hupper true u⟩ +
        ((v.1 : AddCircle p), (v.2 : AddCircle p))) : X) := by
    rw [hjtrue]
    simpa only [show ((1 : unitInterval) : ℝ) = 1 from rfl, one_mul] using
      htranslate 1 ⟨f true (endpoint true, u), hupper true u⟩
  refine ⟨j, hj, hji, hjR, hjp, hjlo, hjfalse, htrue, ?_⟩
  intro b u
  cases b
  · rw [hjfalse]
    exact hupper false u
  · rw [htrue]
    exact (h _).property

end PoincareConjecture.M76.PeriodicSquare
