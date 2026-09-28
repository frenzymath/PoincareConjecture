import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Completeness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Components

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [T3Space M] in
theorem unitRicciKernelComponent_projection_surjective (D : LeviCivitaData g)
    (hc : IsCoveringMap (unitRicciKernelProjection D))
    (hcard : ∀ x, Nat.card (unitRicciKernelProjection D ⁻¹' {x}) = 2)
    (p : UnitRicciKernel D) :
    letI := unitRicciKernelChartedSpace D hc
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    Function.Surjective (fun q : C => unitRicciKernelProjection D q.1) := by
  let := unitRicciKernelChartedSpace D hc
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  have hopen : IsOpen (unitRicciKernelProjection D '' (C : Set (UnitRicciKernel D))) :=
    hc.isOpenMap _ C.isOpen
  have hclosed : IsClosed (unitRicciKernelProjection D '' (C : Set (UnitRicciKernel D))) :=
    (unitRicciKernelProjection_isProperMap D hc hcard).isClosedMap _ isClosed_connectedComponent
  have heq : unitRicciKernelProjection D '' (C : Set (UnitRicciKernel D)) = univ :=
    (show IsClopen _ from ⟨hclosed, hopen⟩).eq_univ
      ⟨unitRicciKernelProjection D p, p, mem_connectedComponent, rfl⟩
  dsimp only
  intro x
  have hx : x ∈ unitRicciKernelProjection D '' (C : Set (UnitRicciKernel D)) := by
    rw [heq]
    trivial
  obtain ⟨q, hq, he⟩ := hx
  exact ⟨⟨q, hq⟩, he⟩

omit [T3Space M] [ConnectedSpace M] in
theorem unitRicciKernelComponent_projection_isLocalDiffeomorph (D : LeviCivitaData g)
    (hc : IsCoveringMap (unitRicciKernelProjection D)) (p : UnitRicciKernel D) :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞
      (fun q : C => unitRicciKernelProjection D q.1) := by
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  dsimp only
  intro q
  exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) C q).comp
    (𝓡 n) M (unitRicciKernelProjection_isLocalDiffeomorph D hc q.1)

omit [T3Space M] in
theorem unitRicciKernelComponent_projection_fiber_card (D : LeviCivitaData g)
    (hc : IsCoveringMap (unitRicciKernelProjection D))
    (hcard : ∀ x, Nat.card (unitRicciKernelProjection D ⁻¹' {x}) = 2)
    (p : UnitRicciKernel D) :
    letI := unitRicciKernelChartedSpace D hc
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    ∀ x : M, Nat.card ((fun q : C => unitRicciKernelProjection D q.1) ⁻¹' {x}) = 1 ∨
      Nat.card ((fun q : C => unitRicciKernelProjection D q.1) ⁻¹' {x}) = 2 := by
  let := unitRicciKernelChartedSpace D hc
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  dsimp only
  intro x
  let A := (fun q : C => unitRicciKernelProjection D q.1) ⁻¹' {x}
  let B := unitRicciKernelProjection D ⁻¹' {x}
  let i : A → B := fun q => ⟨q.1.1, q.2⟩
  have hi : Function.Injective i := by
    intro a b hab
    have hab' : a.1.1 = b.1.1 := congrArg (fun z : B => z.1) hab
    exact Subtype.ext (Subtype.ext hab')
  let : Finite B := Nat.finite_of_card_ne_zero (by rw [hcard x]; decide)
  let : Finite A := Finite.of_injective i hi
  obtain ⟨q, hq⟩ := unitRicciKernelComponent_projection_surjective D hc hcard p x
  let : Nonempty A := ⟨⟨q, hq⟩⟩
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hle : Nat.card A ≤ 2 := (Nat.card_le_card_of_injective i hi).trans_eq (hcard x)
  change Nat.card A = 1 ∨ Nat.card A = 2
  omega

omit [T3Space M] [ConnectedSpace M] in
theorem unitRicciKernelComponent_projection_isProperMap (D : LeviCivitaData g)
    (hc : IsCoveringMap (unitRicciKernelProjection D))
    (hcard : ∀ x, Nat.card (unitRicciKernelProjection D ⁻¹' {x}) = 2)
    (p : UnitRicciKernel D) :
    letI := unitRicciKernelChartedSpace D hc
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    IsProperMap (fun q : C => unitRicciKernelProjection D q.1) := by
  let := unitRicciKernelChartedSpace D hc
  exact (unitRicciKernelProjection_isProperMap D hc hcard).comp
    isClosed_connectedComponent.isProperMap_subtypeVal

theorem unitRicciKernelComponent_projection_isCoveringMap (D : LeviCivitaData g)
    (hc : IsCoveringMap (unitRicciKernelProjection D))
    (hcard : ∀ x, Nat.card (unitRicciKernelProjection D ⁻¹' {x}) = 2)
    (p : UnitRicciKernel D) :
    letI := unitRicciKernelChartedSpace D hc
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
    IsCoveringMap (fun q : C => unitRicciKernelProjection D q.1) := by
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  let := unitRicciKernelT3Space D hc
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  have hf := unitRicciKernelComponent_projection_isLocalDiffeomorph D hc p
  have hfin (x : M) : ((fun q : C => unitRicciKernelProjection D q.1) ⁻¹' {x}).Finite := by
    have hnum := unitRicciKernelComponent_projection_fiber_card D hc hcard p x
    change Nat.card ((fun q : C => unitRicciKernelProjection D q.1) ⁻¹' {x}) = 1 ∨
      Nat.card ((fun q : C => unitRicciKernelProjection D q.1) ⁻¹' {x}) = 2 at hnum
    let : Finite ((fun q : C => unitRicciKernelProjection D q.1) ⁻¹' {x}) :=
      Nat.finite_of_card_ne_zero (by omega)
    exact Set.toFinite _
  have hcov := (unitRicciKernelComponent_projection_isProperMap D hc hcard p).isClosedMap
    |>.isCoveringMapOn_of_isLocalHomeomorphOn (s := univ)
      (fun x _ => hfin x) (fun q _ => hf.isLocalHomeomorph q)
  exact fun x => hcov x (mem_univ x)

end PoincareConjecture.RicciFlow.Splitting
