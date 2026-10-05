import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.SpanningAnnulus.Orientable.Terminal
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.SpanningAnnulus.MarkedSlope
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.SpanningAnnulus.PlanarReturn
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Annulus.Cylinder
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Annulus.Tower

/-! # Original spanning annuli from commensurability and local orientation -/

set_option autoImplicit false
open Set Metric Topology Geometry
open Geometry.OriginalPLTower
open Poincare.Topology.Orientation.ProjectivePlane

namespace PoincareMT.M76
open Dehn Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem exists_commensurable_original_spanning_annulus_of_localOrientation
    {E₀ E₁ : Type*} {X ι : Type}
    [TopologicalSpace E₀] [TopologicalSpace E₁] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (O : LocalOrientation X) (he : PLDomain e R)
    (F : Bool → Set X) (hF : ∀ b, F b ⊆ frontier R)
    (hFopen : ∀ b, IsOpen ((Subtype.val : frontier R → X) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true))
    (i₀ : C(E₀, R)) (i₁ : C(E₁, R))
    (hi₁ : ∀ x, (i₁ x : X) ∈ F true)
    (e₀ : E₀) (e₁ : E₁) (k : Path (i₀ e₀) (i₁ e₁))
    (hc : (FundamentalGroup.map i₀ e₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
        (FundamentalGroup.map i₁ e₁)).range)
    (hinj : Function.Injective (FundamentalGroup.map i₀ e₀))
    (alpha : Path e₀ e₀) (halpha : ∀ t, (i₀ (alpha t) : X) ∈ F false)
    (ha : orderOf (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk alpha)) = 0) :
    ∃ (g : (V1 × V2) → X) (original : C(source, R)),
      PolyhedralPLInCharts e g source ∧ IsEmbedding (fun x : source => g x) ∧
      (∀ x : source, g x = (original x : X)) ∧
      (∀ x : source, g x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1) ∧
      (∀ b (z : Q2), g (endpoint b, z) ∈ F b) ∧
      ∀ b, ¬ (sourceAnnulusRim original b).Nullhomotopic := by
  obtain ⟨g, f, hg, hgf, hmark, hessential, _⟩ :=
    exists_essential_marked_PL_annulus_of_commensurable_open_marks he F hF hFopen hdis
      i₀ i₁ hi₁ e₀ e₁ k hc hinj alpha halpha ha
  obtain ⟨S, _, _, r, C, s0, st, hs0, hreach,
      j, original, hj, hji, hvalue, hmark, hessential, hproper⟩ :=
    exists_terminal_spanning_annulus_of_essential_source_of_localOrientation
      O he F hF hdis g f hg hgf hmark hessential
  obtain ⟨A⟩ := nonempty_markedEssentialPlanarAnnulus_of_cylinder
    j original hj hji hvalue hmark hessential hproper
  obtain ⟨B⟩ := A.nonempty_of_reaches hreach he hF hFopen hdis
  obtain ⟨j0, hj0, hji0, _, hvalue0, hproper0, hmark0, hessential0⟩ :=
    B.exists_original_embedded_annulus hs0
  exact exists_original_cylinder_of_planar_annulus j0 B.original
    hj0 hji0 hvalue0 hproper0 hmark0 hessential0

end PoincareMT.M76
