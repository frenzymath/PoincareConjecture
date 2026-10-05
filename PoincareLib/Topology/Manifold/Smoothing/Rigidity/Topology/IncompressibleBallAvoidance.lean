import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.OriginalBallTopology
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Isotopy.Mathlib.HomotopyFundamentalGroup
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Incompressible surfaces avoid disjoint PL sphere fillings

A connected surface disjoint from the whole marked sphere is either
outside its filling or contained in that filling. In the latter case its
fundamental group map factors through the actual contractible ball. An
injective, nontrivial group therefore excludes the latter case. This is
the ball-avoidance step for the source-cut irreducibility obligation in
the Waldhausen hierarchy (1968, pp. 59--60).
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76.ChartwisePLBall

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {D S R M : Set X}

omit [T2Space X] in
/-- The actual parametrization contracts the complete original ball. -/
theorem contractibleSpace (b : ChartwisePLBall e D S) : ContractibleSpace D := by
  let : ContractibleSpace (closedBall (0 : Fin 3 → ℝ) 1) :=
    (convex_closedBall (0 : Fin 3 → ℝ) 1).contractibleSpace
      ⟨0, mem_closedBall_self (by norm_num)⟩
  exact b.parametrization.symm.contractibleSpace

/-- An incompressible connected carrier with nontrivial based groups
cannot enter a PL ball when it misses the entire marked boundary. The
group injection is into the original ambient domain, not into the ball. -/
theorem disjoint_of_pi1_injective (b : ChartwisePLBall e D S)
    (hDR : D ⊆ R) (hMR : M ⊆ R) (hM : IsPreconnected M)
    (hMS : Disjoint M S)
    (hpi : ∀ x : M, Nontrivial (FundamentalGroup M x) ∧
      Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hMR) x)) :
    Disjoint D M := by
  classical
  rw [Set.disjoint_left]
  intro x hxD hxM
  have hxS : x ∉ S := fun hx => Set.disjoint_left.mp hMS hxM hx
  have hxint : x ∈ interior D := by
    rw [b.interior_eq_sdiff]
    exact ⟨hxD, hxS⟩
  have hMint : M ⊆ interior D := by
    apply hM.subset_of_closure_inter_subset isOpen_interior ⟨x, hxM, hxint⟩
    rw [b.closure_interior, b.interior_eq_sdiff]
    exact fun y hy => ⟨hy.1, fun hyS => Set.disjoint_left.mp hMS hy.2 hyS⟩
  have hMD : M ⊆ D := hMint.trans interior_subset
  let q : C(M, D) := ContinuousMap.inclusion hMD
  let r : C(D, R) := ContinuousMap.inclusion hDR
  let : ContractibleSpace D := b.contractibleSpace
  let xM : M := ⟨x, hxM⟩
  let : Nontrivial (FundamentalGroup M xM) := (hpi xM).1
  obtain ⟨a, c, hac⟩ := exists_pair_ne (FundamentalGroup M xM)
  apply hac
  apply (hpi xM).2
  have hcomp := FundamentalGroup.map_comp_apply q r xM
  exact (hcomp a).trans
    ((congrArg (FundamentalGroup.map r (q xM))
      (Subsingleton.elim (FundamentalGroup.map q xM a)
        (FundamentalGroup.map q xM c))).trans (hcomp c).symm)

end PoincareMT.M76.ChartwisePLBall
