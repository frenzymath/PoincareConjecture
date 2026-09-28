import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.CylindricalFrontier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.LocallyFlatSphereLift
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardSphereLift
import PoincareConjecture.Proofs.M76.Brown.LocallyFlatBoundedRegion










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.not_subset_latticeHandle_frontier
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {S : Set (LatticeHandleAmbient ι κ L)}
    (s : ChartwisePLSphere e S)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hindex : Fintype.card ι ≤ 2) :
    ¬ S ⊆ frontier (latticeHandleDomain ι κ L) := by
  intro hS
  let : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
  let V := (ι → ℝ) × (κ → ℝ)
  let a : V ≃L[ℝ] V3 := ContinuousLinearEquiv.ofFinrankEq (by
    simpa only [V, Module.finrank_prod, Module.finrank_pi, Module.finrank_self,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Fintype.card_fin] using hdim)
  let p : V → LatticeHandleAmbient ι κ L :=
    fun z => (z.1, QuotientAddGroup.mk z.2)
  have hp : IsLocalHomeomorph p :=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap.id_prod.isLocalHomeomorph
  obtain ⟨l, hli, hl⟩ := s.exists_standard_lattice_lift ι κ L
  let l' : C(sphere (0 : V3) 1, V3) := ⟨fun x => a (l x), a.continuous.comp l.continuous⟩
  have hl' (x : sphere (0 : V3) 1) :
      (p ∘ a.symm) (l' x) = (s.parametrization x : LatticeHandleAmbient ι κ L) := by
    simpa only [Function.comp_apply, l', ContinuousMap.coe_mk, a.symm_apply_apply] using hl x
  obtain ⟨hflat⟩ := s.locallyFlat_lift he.compatible (fun x _ => he.cover x)
    (hp.comp a.symm.toHomeomorph.isLocalHomeomorph) l' (a.injective.comp hli) hl'
  obtain ⟨U, _, hU, _, hUc, _, _, _, hfront, _, _, _, hcompact, _⟩ :=
    hflat.exists_bounded_complement_components
  have hbound : Bornology.IsBounded (a.symm '' U) :=
    (hcompact.image a.symm.continuous).isBounded.subset (image_mono subset_closure)
  have hfront' : frontier (a.symm '' U) ⊆
      sphere (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ)) := by
    change frontier (a.symm.toHomeomorph '' U) ⊆ _
    rw [← a.symm.toHomeomorph.image_frontier, hfront]
    rintro y ⟨z, ⟨x, rfl⟩, rfl⟩
    have hx := hS (s.parametrization x).property
    rw [latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero] at hx
    have hfst := congrArg Prod.fst (hl x)
    change (a.symm (a (l x))).1 ∈ sphere (0 : ι → ℝ) 1 ∧ _
    rw [a.symm_apply_apply, hfst]
    exact ⟨hx.1, mem_univ _⟩
  have hempty := (a.symm.toHomeomorph.isOpenMap _ hU).eq_empty_of_bounded_frontier_subset_cylinder
    (interior_sphere _ one_ne_zero) hbound hfront'
  exact (hUc.nonempty.image a.symm).ne_empty hempty

end PoincareConjecture.M76
