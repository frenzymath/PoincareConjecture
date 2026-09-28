import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.SpanningAnnulus.TerminalOpenMarks
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.SpanningAnnulus.PlanarReturn
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.Cylinder
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.Tower










set_option autoImplicit false
open Set Metric Topology Geometry
open Geometry.OriginalPLTower

namespace PoincareConjecture.M76

open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

theorem exists_commensurable_original_spanning_annulus_in_open_marks
    {E₀ E₁ : Type*} {ι : Type} [TopologicalSpace E₀] [TopologicalSpace E₁]
    {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0} (he : PLDomain e R)
    (F : Bool → Set X0) (hF : ∀ b, F b ⊆ frontier R)
    (hFopen : ∀ b, IsOpen ((Subtype.val : frontier R → X0) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true))
    (i₀ : C(E₀, R)) (i₁ : C(E₁, R))
    (hi₁ : ∀ x, (i₁ x : X0) ∈ F true)
    (e₀ : E₀) (e₁ : E₁) (k : Path (i₀ e₀) (i₁ e₁))
    (hc : (FundamentalGroup.map i₀ e₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
        (FundamentalGroup.map i₁ e₁)).range)
    (hinj : Function.Injective (FundamentalGroup.map i₀ e₀))
    (alpha : Path e₀ e₀) (halpha : ∀ t, (i₀ (alpha t) : X0) ∈ F false)
    (ha : orderOf (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk alpha)) = 0) :
    ∃ (g : (V1 × V2) → X0) (original : C(source, R)),
      PolyhedralPLInCharts e g source ∧ IsEmbedding (fun x : source => g x) ∧
      (∀ x : source, g x = (original x : X0)) ∧
      (∀ x : source, g x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1) ∧
      (∀ b (z : Q2), g (endpoint b, z) ∈ F b) ∧
      ∀ b, ¬ (sourceAnnulusRim original b).Nullhomotopic := by
  obtain ⟨g, S, _, _, _, r, C, s0, st, hs0, hreach,
    j, original, hj, hji, hvalue, hmark, hessential, hproper⟩ :=
    exists_commensurable_terminal_spanning_annulus_in_open_marks he F hF hFopen hdis
      i₀ i₁ hi₁ e₀ e₁ k hc hinj alpha halpha ha
  obtain ⟨A⟩ := nonempty_markedEssentialPlanarAnnulus_of_cylinder
    j original hj hji hvalue hmark hessential hproper
  obtain ⟨B⟩ := A.nonempty_of_reaches hreach he hF hFopen hdis
  obtain ⟨j0, hj0, hji0, _, hvalue0, hproper0, hmark0, hessential0⟩ :=
    B.exists_original_embedded_annulus hs0
  exact exists_original_cylinder_of_planar_annulus j0 B.original
    hj0 hji0 hvalue0 hproper0 hmark0 hessential0

end PoincareConjecture.M76
