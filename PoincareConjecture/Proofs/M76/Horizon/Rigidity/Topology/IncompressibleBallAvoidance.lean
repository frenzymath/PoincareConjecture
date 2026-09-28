import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.HomotopyFundamentalGroup
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected












set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.ChartwisePLBall

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {D S R M : Set X}

omit [T2Space X] in

theorem contractibleSpace (b : ChartwisePLBall e D S) : ContractibleSpace D := by
  let : ContractibleSpace (closedBall (0 : Fin 3 → ℝ) 1) :=
    (convex_closedBall (0 : Fin 3 → ℝ) 1).contractibleSpace
      ⟨0, mem_closedBall_self (by norm_num)⟩
  exact b.parametrization.symm.contractibleSpace




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

end PoincareConjecture.M76.ChartwisePLBall
