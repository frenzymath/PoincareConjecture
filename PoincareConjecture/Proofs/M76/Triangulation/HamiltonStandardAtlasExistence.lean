import PoincareConjecture.Proofs.M76.Mathlib.AdditiveQuotientPLAtlas
import PoincareConjecture.Proofs.M76.Mathlib.CoveringProduct
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLatticeHandleModel
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]

theorem exists_standard_lattice_coordinate_cover
    (hdim : Fintype.card ι + Fintype.card κ = 3) :
    ∃ d : ((ι → ℝ) × (κ → ℝ)) →
        OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ),
      (∀ x, ∃ j, x ∈ (d j).source) ∧
      (∀ i j, (d i).symm.trans (d j) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ)) ∧
      ∀ j, ∃ a : (Fin 3 → ℝ) ≃ᴬ[ℝ] ((ι → ℝ) × (κ → ℝ)),
        ∀ z ∈ (d j).target,
          (d j).symm z = ((a z).1, QuotientAddGroup.mk (a z).2) := by
  let p : ((ι → ℝ) × (κ → ℝ)) →+ LatticeHandleAmbient ι κ L :=
    (AddMonoidHom.id (ι → ℝ)).prodMap (QuotientAddGroup.mk' L.toAddSubgroup)
  have hq : IsCoveringMap
      (QuotientAddGroup.mk : (κ → ℝ) → ((κ → ℝ) ⧸ L.toAddSubgroup)) :=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap
  have hp : IsLocalHomeomorph p := hq.id_prod.isLocalHomeomorph
  have hsurj : Function.Surjective p := by
    rintro ⟨x, y⟩
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact ⟨(x, z), rfl⟩
  let a : ((ι → ℝ) × (κ → ℝ)) ≃ᴬ[ℝ] (Fin 3 → ℝ) :=
    (LinearEquiv.ofFinrankEq _ _ (by
      simpa only [Module.finrank_prod, Module.finrank_pi, Module.finrank_self,
        Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
        Fintype.card_fin] using hdim)).toContinuousLinearEquiv.toContinuousAffineEquiv
  obtain ⟨d, hdcover, hdcompat, hdformula⟩ :=
    p.exists_piecewiseAffine_quotient_cover hp hsurj a
  exact ⟨d, hdcover, hdcompat, fun j => ⟨a.symm, fun z _ => hdformula j z⟩⟩

theorem exists_zero_standard_lattice_handle_atlas [IsEmpty ι]
    (hdim : Fintype.card κ = 3) :
    ∃ d : ((ι → ℝ) × (κ → ℝ)) →
        OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ),
      StandardLatticeHandleAtlas ι κ L d := by
  obtain ⟨d, hdcover, hdcompat, hdformula⟩ :=
    exists_standard_lattice_coordinate_cover ι κ L (by simpa using hdim)
  have hdomain : latticeHandleDomain ι κ L = univ := by
    ext x
    have hx : x.1 = 0 := Subsingleton.elim _ _
    simp [latticeHandleDomain, hx]
  refine ⟨d, ⟨?_, hdformula⟩⟩
  rw [hdomain]
  exact {
    cover := hdcover
    compatible := hdcompat
    closed := isClosed_univ
    halfspace := by
      intro x hx
      simp only [frontier_univ, mem_empty_iff_false] at hx
  }

end PoincareConjecture.M76
