import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.StandardFrontier










set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Ann" => squareAnnulus 8 1



theorem exists_original_to_standard_frontier_homeomorph
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B)
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (A : ∀ theta ∈ ({(a : C), (b : C)} : Set C), Ann ≃ₜ sourceSurface phi theta)
    (hA : ∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C)), ∀ side z,
      (A theta htheta (Dehn.annulusRimPoint side z) : X) =
        (sourceBoundaryCircle phi theta F (originalIntervalEndpoint side)
          (originalIntervalEndpoint_norm side)
          (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p
            (by norm_num) (by norm_num) z) : X)) :
    ∃ E : ↥(frontier (sourceSlab phi a b)) ≃ₜ
        ↥(frontier (sourceSlab (ContinuousMap.id H) a b)),
      (∀ x : frontier (sourceSlab phi a b), (x : X) ∈ frontier R → (E x : X) = x) ∧
      ∀ theta (htheta : theta ∈ ({(a : C), (b : C)} : Set C))
        (x : sourceSurface phi theta),
        (E ⟨x, hfront.symm ▸ Or.inr (by
          rcases htheta with rfl | rfl
          · exact Or.inl x.property
          · exact Or.inr x.property)⟩ : X) =
          standardTargetAnnulus theta ((A theta htheta).symm x) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  have hne : (a : C) ≠ (b : C) := by
    intro heq
    have haI : a ∈ Ico c (c + p) := ⟨ha.le, hab.trans hb⟩
    have hbI : b ∈ Ico c (c + p) := ⟨(ha.trans hab).le, hb⟩
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico haI hbI).mp heq)
  exact exists_marked_slab_frontier_homeomorph phi (ContinuousMap.id H) F (.refl _ _)
    a b hne hfront (frontier_standard_sourceSlab ha hab.le hb) A
    (fun theta _ => standardTargetAnnulus theta)
    (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num) (by norm_num)) hA
    (fun theta _ => standardTargetAnnulus_rim theta)

end PoincareConjecture.M76.HamiltonIntervalTorus
