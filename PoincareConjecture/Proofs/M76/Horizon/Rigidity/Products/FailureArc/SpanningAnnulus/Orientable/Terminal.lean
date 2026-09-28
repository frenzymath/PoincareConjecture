import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.OriginalTower
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.TerminalEmbeddedRims
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Boundary.Orientable.StageAnnulus

set_option autoImplicit false
open Set Metric Topology Geometry
open Geometry.OriginalPLTower
open Poincare.Topology.Orientation.ProjectivePlane

namespace PoincareConjecture.M76

open Dehn Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem exists_terminal_spanning_annulus_of_essential_source_of_localOrientation
    {X ι : Type} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (O : LocalOrientation X) (he : PLDomain e R)
    (F : Bool → Set X) (hF : ∀ b, F b ⊆ frontier R)
    (hdis : Disjoint (F false) (F true))
    (g : (V1 × V2) → X) (f : C(source, R))
    (hg : PolyhedralPLInCharts e g source)
    (hgf : ∀ x : source, g x = (f x : X))
    (hmark : ∀ (b : Bool) (u : Q2), g (endpoint b, u) ∈ F b)
    (hessential : ∀ b, ¬ (sourceAnnulusRim f b).Nullhomotopic) :
    ∃ S : SimplicialComplex ℝ (V1 × V2), S.faces.Finite ∧ S.space = source ∧
      ∃ (r : X → ℝ) (C : Set X) (s0 st : Stage e S g r C),
        IsOpenEmbedding s0.projection ∧ Reaches s0 st ∧
        ∃ (k : (V1 × V2) → st.Carrier) (f : C(source, R)),
          PolyhedralPLInCharts st.charts k source ∧
          Topology.IsEmbedding (fun x : source ↦ k x) ∧
          (∀ x : source, (f x : X) = st.projection (k x)) ∧
          (∀ (b : Bool) (u : Q2), st.projection (k (endpoint b, u)) ∈ F b) ∧
          (∀ b, ¬ (sourceAnnulusRim f b).Nullhomotopic) ∧
          ∀ x : source, k x ∈ frontier (st.projection ⁻¹' R) ↔
            (x : V1 × V2).1 ∈ sphere (0 : V1) 1 := by
  classical
  let : LocallyCompactSpace X := he.locallyCompactSpace
  have hgR : MapsTo g source R := by
    intro x hx
    rw [hgf ⟨x, hx⟩]
    exact (f ⟨x, hx⟩).property
  have hfront (b : Bool) (u : Q2) : g (endpoint b, u) ∈ frontier R := hF b (hmark b u)
  obtain ⟨S, hS, hSs, r, C, s0, st, hs0, hreach, ⟨N⟩, hterminal⟩ :=
    exists_original_singular_annulus_terminal_region he hg hgR (hfront false)
  obtain ⟨a, gamma, haPL, hai, hgamma, hnon, hsub, hadis⟩ :=
    N.exists_disjoint_essential_embedded_rims hSs hfront f hgf hessential F hdis hmark
  have hgammaMark (b : Bool) (u : Q2) : (N.originalProjection (gamma b u) : X) ∈ F b := by
    obtain ⟨v, hv⟩ := hsub b (mem_image_of_mem (a b) u.property)
    have heq : N.singularBoundaryRim hSs hfront b v = gamma b u :=
      Subtype.ext (hv.trans (hgamma b u).symm)
    rw [← heq, N.originalProjection_singularBoundaryRim]
    exact hmark b v
  obtain ⟨P⟩ := N.nonempty_paired_boundary hSs (hfront false) hterminal
    a gamma haPL hai hgamma hnon hadis F hgammaMark
  obtain ⟨O', _⟩ := exists_localOrientation_of_isLocalHomeomorph
    st.projection st.projectionLocal O
  obtain ⟨j, f', hj, hji, hjf, hjmark, hjnon, hjproper⟩ :=
    P.exists_proper_stage_annulus_of_localOrientation O' hF
  exact ⟨S, hS, hSs, r, C, s0, st, hs0, hreach,
    j, f', hj, hji, hjf, hjmark, hjnon, hjproper⟩

end PoincareConjecture.M76
