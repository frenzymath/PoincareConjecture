import PoincareConjecture.Proofs.M02.Topology.IntegralSubdivision

set_option autoImplicit false

open CategoryTheory Limits

universe u v

namespace PoincareConjecture.Proofs.M02

open PoincareConjecture.Proofs.M02.Topology

noncomputable section

variable {X : Type u} [TopologicalSpace X] {I : Type v}

theorem exists_integral_small_homology_representative
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (n : Nat)
    (c : integralCoefficient ⟶ (integralChains X).X (n + 1))
    (hc : c ≫ (integralChains X).d (n + 1) n = 0) :
    ∃ k : Nat,
      (integralSubdivisionIterate X k).f (n + 1) (c (ULift.up 1)) ∈
        integralSmallChains U (n + 1) ∧
      c ≫ (integralSubdivisionIterate X k).f (n + 1) ≫
          (integralChains X).d (n + 1) n = 0 ∧
      (integralChains X).liftCycles c n (by simp) hc ≫
          (integralChains X).homologyπ (n + 1) =
        (integralChains X).liftCycles
          (c ≫ (integralSubdivisionIterate X k).f (n + 1)) n (by simp)
          (by
            rw [Category.assoc, (integralSubdivisionIterate X k).comm,
              ← Category.assoc, hc, zero_comp]) ≫
          (integralChains X).homologyπ (n + 1) := by
  obtain ⟨k, hk⟩ := integral_subdivision_eventually_small U hU hcover
    (n + 1) (c (ULift.up 1))
  refine ⟨k, hk, ?_, ?_⟩
  · rw [(integralSubdivisionIterate X k).comm,
      ← Category.assoc, hc, zero_comp]
  let S := integralSubdivisionIterate X k
  have hS : (integralChains X).homologyMap S (n + 1) = 𝟙 _ := by
    have h := (integralIteratedSubdivisionPrism X k).homologyMap_eq (n + 1)
    simpa only [HomologicalComplex.homologyMap_id] using h.symm
  let z := (integralChains X).liftCycles c n (by simp) hc
  let z' := (integralChains X).liftCycles (c ≫ S.f (n + 1)) n (by simp)
    (by
      rw [Category.assoc, S.comm, ← Category.assoc, hc, zero_comp])
  have hz : z ≫ (integralChains X).iCycles (n + 1) = c :=
    (integralChains X).liftCycles_i c n (by simp) hc
  have hz' : z' ≫ (integralChains X).iCycles (n + 1) = c ≫ S.f (n + 1) :=
    (integralChains X).liftCycles_i (c ≫ S.f (n + 1)) n (by simp) _
  have hcycles : z ≫ (integralChains X).cyclesMap S (n + 1) = z' := by
    rw [HomologicalComplex.liftCycles_comp_cyclesMap]
  calc
    z ≫ (integralChains X).homologyπ (n + 1) =
        z ≫ (integralChains X).homologyπ (n + 1) ≫
          (integralChains X).homologyMap S (n + 1) := by
      rw [hS, Category.comp_id]
    _ = z ≫ (integralChains X).cyclesMap S (n + 1) ≫
          (integralChains X).homologyπ (n + 1) := by
      simpa only [Category.assoc] using congrArg (fun q => z ≫ q)
        (HomologicalComplex.homologyπ_naturality (φ := S) (i := n + 1))
    _ = z' ≫ (integralChains X).homologyπ (n + 1) := by
      rw [← Category.assoc, hcycles]

end

end PoincareConjecture.Proofs.M02
