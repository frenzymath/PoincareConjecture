import PoincareConjecture.Proofs.M02.IntegralChains
import PoincareConjecture.Proofs.M02.Topology.IntegralSubdivision





set_option autoImplicit false

open CategoryTheory Limits

universe u

namespace PoincareConjecture.Proofs.M02

open PoincareConjecture.Proofs.M02.Topology

noncomputable section



theorem exists_integral_homology_cycle
    (K : ChainComplex (ModuleCat.{u} Int) Nat) (n : Nat)
    (h : integralCoefficient ⟶ K.homology (n + 1)) :
    ∃ z : integralCoefficient ⟶ K.X (n + 1),
      ∃ hz : z ≫ K.d (n + 1) n = 0,
        K.liftCycles z n (by simp) hz ≫ K.homologyπ (n + 1) = h := by
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ (n + 1))).mp
    inferInstance (h (ULift.up 1))
  let u : integralCoefficient ⟶ K.cycles (n + 1) :=
    (integralCoefficientHomEquiv (K.cycles (n + 1))).symm y
  let z := u ≫ K.iCycles (n + 1)
  have hz : z ≫ K.d (n + 1) n = 0 := by
    simp only [z, Category.assoc, HomologicalComplex.iCycles_d, comp_zero]
  refine ⟨z, hz, ?_⟩
  have hlift : K.liftCycles z n (by simp) hz = u := by
    apply (cancel_mono (K.iCycles (n + 1))).mp
    rw [HomologicalComplex.liftCycles_i]
  rw [hlift]
  apply (integralCoefficientHomEquiv (K.homology (n + 1))).injective
  rw [integralCoefficientHomEquiv_apply, integralCoefficientHomEquiv_apply]
  change K.homologyπ (n + 1) (u (ULift.up 1)) = h (ULift.up 1)
  have hu : u (ULift.up 1) = y := by
    simpa [u] using integralCoefficientHomEquiv_symm_apply _ y (ULift.up 1)
  rw [hu]
  exact hy

end

end PoincareConjecture.Proofs.M02
