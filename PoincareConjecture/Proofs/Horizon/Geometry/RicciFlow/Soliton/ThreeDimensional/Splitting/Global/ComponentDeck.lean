import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.ComponentCover










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem unitRicciKernelProjection_fiber_eq_reverse (D : LeviCivitaData g)
    (hcard : ∀ x, Nat.card (unitRicciKernelProjection D ⁻¹' {x}) = 2)
    (p q : UnitRicciKernel D) :
    unitRicciKernelProjection D p = unitRicciKernelProjection D q ↔
      q = p ∨ q = unitRicciKernelReverse D p := by
  classical
  let A := unitRicciKernelProjection D ⁻¹' {unitRicciKernelProjection D p}
  have hA : A.ncard = 2 := hcard _
  have hfinite : A.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hsub : {p, unitRicciKernelReverse D p} ⊆ A := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> rfl
  have heq : {p, unitRicciKernelReverse D p} = A :=
    Set.eq_of_subset_of_ncard_le hsub (by
      rw [hA, Set.ncard_pair (unitRicciKernelReverse_fixedPointFree D p).symm]) hfinite
  constructor
  · intro h
    have hq : q ∈ A := h.symm
    rw [← heq] at hq
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hq
  · rintro (rfl | rfl) <;> rfl

theorem unitRicciKernelReverse_mem_component (D : LeviCivitaData g)
    {p q : UnitRicciKernel D} (hq : q ∈ connectedComponent p)
    (hp : unitRicciKernelReverse D p ∈ connectedComponent p) :
    unitRicciKernelReverse D q ∈ connectedComponent p := by
  have h := (continuous_unitRicciKernelReverse D).mapsTo_connectedComponent p hq
  rwa [← connectedComponent_eq hp] at h

theorem unitRicciKernelComponent_projection_injective_of_reverse_not_mem
    [ConnectedSpace M] (D : LeviCivitaData g)
    (hc : IsCoveringMap (unitRicciKernelProjection D))
    (hcard : ∀ x, Nat.card (unitRicciKernelProjection D ⁻¹' {x}) = 2)
    (p : UnitRicciKernel D)
    (hp : unitRicciKernelReverse D p ∉ connectedComponent p) :
    letI := unitRicciKernelChartedSpace D hc
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    Function.Injective (fun q : C => unitRicciKernelProjection D q.1) := by
  let := unitRicciKernelChartedSpace D hc
  dsimp only
  intro a b hab
  rcases (unitRicciKernelProjection_fiber_eq_reverse D hcard a.1 b.1).mp hab with he | he
  · exact Subtype.ext he.symm
  · have hr : unitRicciKernelReverse D a.1 ∈ connectedComponent
        (unitRicciKernelReverse D p) :=
      (continuous_unitRicciKernelReverse D).mapsTo_connectedComponent p a.2
    rw [← he] at hr
    have heq := (connectedComponent_eq b.2).trans (connectedComponent_eq hr).symm
    exact (hp (heq.symm ▸ mem_connectedComponent)).elim

theorem exists_nullComponent_diffeomorph_of_reverse_not_mem
    [ConnectedSpace M] (D : LeviCivitaData g)
    (hc : IsCoveringMap (unitRicciKernelProjection D))
    (hcard : ∀ x, Nat.card (unitRicciKernelProjection D ⁻¹' {x}) = 2)
    (p : UnitRicciKernel D)
    (hp : unitRicciKernelReverse D p ∉ connectedComponent p) :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    ∃ e : C ≃ₘ⟮𝓡 n, 𝓡 n⟯ M, ∀ q, e q = unitRicciKernelProjection D q.1 := by
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  let e := (unitRicciKernelComponent_projection_isLocalDiffeomorph D hc p)
    |>.diffeomorphOfBijective
      ⟨unitRicciKernelComponent_projection_injective_of_reverse_not_mem D hc hcard p hp,
        unitRicciKernelComponent_projection_surjective D hc hcard p⟩
  exact ⟨e, fun _ => rfl⟩

end PoincareConjecture.RicciFlow.Splitting
