import PoincareConjecture.Proofs.M76.Dehn.MarkedSquarePLApproximation
import PoincareConjecture.Proofs.M76.Dehn.OriginalTerminalProperDisk
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTowerDescent

set_option autoImplicit false
open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem exists_continuous_terminal_marked_disk
    {M ι : Type*} [TopologicalSpace M] [T2Space M]
    {e : ι → OpenPartialHomeomorph M V3} {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    (f : C(D2, R)) (gamma : C(Q2, Fmark))
    (hpair : ∀ x : Q2,
      (f ⟨x, sphere_subset_closedBall x.property⟩ : M) = (gamma x : M))
    (J : Subgroup (FundamentalGroup Fmark (gamma squareRimBase)))
    (houtside : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ∉ J) :
    ∃ (g : V2 → M) (S : SimplicialComplex ℝ V2) (r : M → ℝ) (C : Set M)
      (s0 st : Stage e S g r C), S.space = D2 ∧
      IsOpenEmbedding s0.projection ∧ Reaches s0 st ∧
      Nonempty (StageMarkedDisk st R Fmark (gamma squareRimBase) J) := by
  obtain ⟨g, rim, hg, hgR, hgr, eta, hout⟩ :=
    exists_marked_PL_square_pair he Fmark hF hopen f gamma hpair J houtside
  obtain ⟨S, r, C, s0, st, hS, hs0, hreach, j, rim', q, hj, hji, hjR, hjrim,
    hjfront, hjout⟩ := exists_original_terminal_proper_disk he hF hg hgR rim hgr
      (eta.evalAt squareRimBase) J hout
  exact ⟨g, S, r, C, s0, st, hS, hs0, hreach,
    ⟨{ map := j
       rim := rim'
       piecewiseAffine := hj
       embedding := hji
       inside := hjR
       boundary_values := hjrim
       whole_boundary_iff := hjfront
       basepath := q
       outside := hjout }⟩⟩

end Geometry.OriginalPLTower
