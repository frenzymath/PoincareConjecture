import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.OriginalTower
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.TerminalEmbeddedRims
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Boundary.StageAnnulus

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

theorem exists_terminal_spanning_annulus_of_essential_source
    {ι : Type} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    (he : PLDomain e R) (F : Bool → Set X0) (hF : ∀ b, F b ⊆ frontier R)
    (hdis : Disjoint (F false) (F true))
    (g : (V1 × V2) → X0) (f : C(source, R))
    (hg : PolyhedralPLInCharts e g source)
    (hgf : ∀ x : source, g x = (f x : X0))
    (hmark : ∀ (b : Bool) (u : Q2), g (endpoint b, u) ∈ F b)
    (hessential : ∀ b, ¬ (sourceAnnulusRim f b).Nullhomotopic) :
    ∃ S : SimplicialComplex ℝ (V1 × V2), S.faces.Finite ∧ S.space = source ∧
      ∃ (r : X0 → ℝ) (C : Set X0) (s0 st : Stage e S g r C),
        IsOpenEmbedding s0.projection ∧ Reaches s0 st ∧
        ∃ (k : (V1 × V2) → st.Carrier) (f : C(source, R)),
          PolyhedralPLInCharts st.charts k source ∧
          Topology.IsEmbedding (fun x : source ↦ k x) ∧
          (∀ x : source, (f x : X0) = st.projection (k x)) ∧
          (∀ (b : Bool) (u : Q2), st.projection (k (endpoint b, u)) ∈ F b) ∧
          (∀ b, ¬ (sourceAnnulusRim f b).Nullhomotopic) ∧
          ∀ x : source, k x ∈ frontier (st.projection ⁻¹' R) ↔
            (x : V1 × V2).1 ∈ sphere (0 : V1) 1 := by
  classical
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  let : LocallyCompactSpace X0 := he.locallyCompactSpace
  have hgR : MapsTo g source R := by
    intro x hx
    rw [hgf ⟨x, hx⟩]
    exact (f ⟨x, hx⟩).property
  have hfront (b : Bool) (u : Q2) : g (endpoint b, u) ∈ frontier R := hF b (hmark b u)
  obtain ⟨S, hS, hSs, r, C, s0, st, hs0, hreach, ⟨N⟩, hterminal⟩ :=
    exists_original_singular_annulus_terminal_region he hg hgR (hfront false)
  obtain ⟨a, gamma, haPL, hai, hgamma, hnon, hsub, hadis⟩ :=
    N.exists_disjoint_essential_embedded_rims hSs hfront f hgf hessential F hdis hmark
  have hgammaMark (b : Bool) (u : Q2) : (N.originalProjection (gamma b u) : X0) ∈ F b := by
    obtain ⟨v, hv⟩ := hsub b (mem_image_of_mem (a b) u.property)
    have heq : N.singularBoundaryRim hSs hfront b v = gamma b u :=
      Subtype.ext (hv.trans (hgamma b u).symm)
    rw [← heq, N.originalProjection_singularBoundaryRim]
    exact hmark b v
  obtain ⟨P⟩ := N.nonempty_paired_boundary hSs (hfront false) hterminal
    a gamma haPL hai hgamma hnon hadis F hgammaMark
  obtain ⟨j, f', hj, hji, hjf, hjmark, hjnon, hjproper⟩ := P.exists_proper_stage_annulus hF
  exact ⟨S, hS, hSs, r, C, s0, st, hs0, hreach,
    j, f', hj, hji, hjf, hjmark, hjnon, hjproper⟩

theorem exists_commensurable_terminal_spanning_annulus
    {E₀ E₁ : Type*} {ι : Type} [TopologicalSpace E₀] [TopologicalSpace E₁]
    {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0} (he : PLDomain e R)
    (F : Bool → Set X0) (hF : ∀ b, F b ⊆ frontier R)
    (hFclopen : ∀ b, IsClopen ((Subtype.val : frontier R → X0) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true))
    (i₀ : C(E₀, R)) (i₁ : C(E₁, R))
    (hi₀ : ∀ x, (i₀ x : X0) ∈ F false) (hi₁ : ∀ x, (i₁ x : X0) ∈ F true)
    (e₀ : E₀) (e₁ : E₁) (k : Path (i₀ e₀) (i₁ e₁))
    (hc : (FundamentalGroup.map i₀ e₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
        (FundamentalGroup.map i₁ e₁)).range)
    (hinj : Function.Injective (FundamentalGroup.map i₀ e₀))
    (alpha : Path e₀ e₀)
    (ha : orderOf (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk alpha)) = 0) :
    ∃ (g : (V1 × V2) → X0) (S : SimplicialComplex ℝ (V1 × V2)),
      PolyhedralPLInCharts e g source ∧ S.faces.Finite ∧ S.space = source ∧
      ∃ (r : X0 → ℝ) (C : Set X0) (s0 st : Stage e S g r C),
        IsOpenEmbedding s0.projection ∧ Reaches s0 st ∧
        ∃ (k : (V1 × V2) → st.Carrier) (f : C(source, R)),
          PolyhedralPLInCharts st.charts k source ∧
          Topology.IsEmbedding (fun x : source ↦ k x) ∧
          (∀ x : source, (f x : X0) = st.projection (k x)) ∧
          (∀ (b : Bool) (u : Q2), st.projection (k (endpoint b, u)) ∈ F b) ∧
          (∀ b, ¬ (sourceAnnulusRim f b).Nullhomotopic) ∧
          ∀ x : source, k x ∈ frontier (st.projection ⁻¹' R) ↔
            (x : V1 × V2).1 ∈ sphere (0 : V1) 1 := by
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  obtain ⟨g, f, hg, hgf, hmark, hessential, _⟩ :=
    exists_essential_marked_PL_annulus_of_commensurable he F hF hFclopen
      i₀ i₁ hi₀ hi₁ e₀ e₁ k hc hinj alpha ha
  obtain ⟨S, hS, hSs, hrest⟩ := exists_terminal_spanning_annulus_of_essential_source
    he F hF hdis g f hg hgf hmark hessential
  exact ⟨g, S, hg, hS, hSs, hrest⟩

end PoincareConjecture.M76
