import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.Monochromatic
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dual.Basis

open Poincare.Topology.Plane.Meshes
open Set
namespace PoincareConjecture.Topology.Surface
noncomputable section
open Classical
set_option autoImplicit false

theorem exists_affineBasis_coords_of_independent_functionals
    (l m : Plane →ᵃ[ℝ] ℝ) (q : Plane) (hlq : l q = 0) (hmq : m q = 0)
    (hind : LinearIndependent ℝ (![l.linear, m.linear] : Fin 2 → Module.Dual ℝ Plane)) :
    ∃ c : AffineBasis (Fin 3) ℝ Plane, c 0 = q ∧ c.coord 1 = l ∧ c.coord 2 = m := by
  let B := basisOfLinearIndependentOfCardEqFinrank hind
    (by simp [Subspace.dual_finrank_eq, Plane])
  let v : Fin 2 → Plane := fun i => (Module.evalEquiv ℝ Plane).symm (B.dualBasis i)
  have he (i j : Fin 2) : (![l.linear, m.linear] : Fin 2 → Module.Dual ℝ Plane) i (v j) =
      if i = j then 1 else 0 := by
    have hB : (B : Fin 2 → Module.Dual ℝ Plane) = ![l.linear, m.linear] :=
      coe_basisOfLinearIndependentOfCardEqFinrank _ _
    rw [← hB]
    change B i ((Module.evalEquiv ℝ Plane).symm (B.dualBasis j)) = _
    rw [Module.apply_evalEquiv_symm_apply, B.dualBasis_apply_self]
  have hlv : l.linear (v 0) = 1 := by simpa using he 0 0
  have hlw : l.linear (v 1) = 0 := by simpa using he 0 1
  have hmv : m.linear (v 0) = 0 := by simpa using he 1 0
  have hmw : m.linear (v 1) = 1 := by simpa using he 1 1
  have hvec : AffineIndependent ℝ (![0, v 0, v 1] : Fin 3 → Plane) := by
    rw [affineIndependent_iff_of_fintype]
    intro w hw hz i
    rw [Finset.weightedVSub_eq_linear_combination _ hw] at hz
    have h1 : w 1 = 0 := by
      have h := congrArg l.linear hz
      simpa [Fin.sum_univ_succ, map_sum, hlv, hlw] using h
    have h2 : w 2 = 0 := by
      have h := congrArg m.linear hz
      simpa [Fin.sum_univ_succ, map_sum, hmv, hmw] using h
    have h0 : w 0 = 0 := by simpa [Fin.sum_univ_succ, h1, h2] using hw
    fin_cases i <;> assumption
  let f : Fin 3 → Plane := fun i => q + (![0, v 0, v 1] : Fin 3 → Plane) i
  have hf : AffineIndependent ℝ f := hvec.vadd
  let c : AffineBasis (Fin 3) ℝ Plane := ⟨f, hf,
    hf.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [Plane])⟩
  refine ⟨c, by change q + 0 = q; exact add_zero _, ?_, ?_⟩
  · apply AffineMap.ext_on c.tot
    rintro z ⟨i, rfl⟩
    have hval : l (c i) = l.linear ((![0, v 0, v 1] : Fin 3 → Plane) i) := by
      change l (q + _) = _
      simpa only [vadd_eq_add, hlq, add_zero, add_comm, zero_add] using l.map_vadd q
        ((![0, v 0, v 1] : Fin 3 → Plane) i)
    rw [c.coord_apply, hval]
    fin_cases i <;> simp [hlv, hlw]
  · apply AffineMap.ext_on c.tot
    rintro z ⟨i, rfl⟩
    have hval : m (c i) = m.linear ((![0, v 0, v 1] : Fin 3 → Plane) i) := by
      change m (q + _) = _
      simpa only [vadd_eq_add, hmq, add_zero, add_comm, zero_add] using m.map_vadd q
        ((![0, v 0, v 1] : Fin 3 → Plane) i)
    rw [c.coord_apply, hval]
    fin_cases i <;> simp [hmv, hmw]
end
end PoincareConjecture.Topology.Surface
