import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cover
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Separation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Ends









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

namespace NeckOnlyCover



theorem exists_neck_center_mem_frontier (H : NeckOnlyCover g) {U : Set M}
    (hU : IsOpen U) (hmeet : (H.X ∩ U).Nonempty) (hmiss : ¬ H.X ⊆ U) :
    ∃ N ∈ H.necks, N.center ∈ H.X ∧ N.center ∈ frontier U := by
  classical
  have hfrontier : (H.X ∩ frontier U).Nonempty := by
    by_contra h
    have hcover : H.X ⊆ U ∪ (closure U)ᶜ := by
      intro x hx
      by_cases hxu : x ∈ U
      · exact Or.inl hxu
      · right
        intro hxc
        exact h ⟨x, hx, by rw [hU.frontier_eq]; exact ⟨hxc, hxu⟩⟩
    have hdisjoint : Disjoint U (closure U)ᶜ :=
      Set.disjoint_left.mpr fun _ hx hy => hy (subset_closure hx)
    rcases H.connected_X.isPreconnected.subset_or_subset hU
      isClosed_closure.isOpen_compl hdisjoint hcover with hin | hout
    · exact hmiss hin
    · obtain ⟨x, hx, hxu⟩ := hmeet
      exact hout hx (subset_closure hxu)
  obtain ⟨x, hx, hxf⟩ := hfrontier
  obtain ⟨N, hN, rfl⟩ := H.pointwise_center_cover x hx
  exact ⟨N, hN, hx, hxf⟩




theorem exists_neck_at_chain_frontier (H : NeckOnlyCover g)
    (C : BalancedNeckChain g H.epsilon)
    (hcenters : ∀ i ∈ C.shape.active, (C.neck i).center ∈ H.X)
    (hmiss : ¬ H.X ⊆ ⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier) :
    ∃ N ∈ H.necks, N.center ∈ H.X ∧
      N.center ∈ frontier (⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier) ∧
      (∀ i ∈ C.shape.active, N.center ≠ (C.neck i).center) ∧
      (N.carrier ∩ ⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier).Nonempty := by
  let U : Set M := ⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier
  have hU : IsOpen U := isOpen_iUnion fun i => (C.neck i.1).carrier_open
  have hmeet : (H.X ∩ U).Nonempty := by
    obtain ⟨i, hi⟩ := C.active_nonempty
    exact ⟨(C.neck i).center, hcenters i hi,
      mem_iUnion.mpr ⟨⟨i, hi⟩, (C.neck i).central_sphere_subset
        (C.neck i).center_on_central_sphere⟩⟩
  obtain ⟨N, hN, hx, hxf⟩ := H.exists_neck_center_mem_frontier hU hmeet hmiss
  have hxU : N.center ∉ U := (hU.frontier_eq ▸ hxf).2
  refine ⟨N, hN, hx, hxf, ?_, ?_⟩
  · intro i hi heq
    apply hxU
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, heq.symm ▸
      (C.neck i).central_sphere_subset (C.neck i).center_on_central_sphere⟩
  · exact mem_closure_iff_nhds.mp (frontier_subset_closure hxf) N.carrier
      (N.carrier_open.mem_nhds (N.central_sphere_subset N.center_on_central_sphere))

end NeckOnlyCover

namespace BalancedNeckChain



theorem exists_mem_frontier_of_finite {ε : ℝ} (C : BalancedNeckChain g ε)
    (hfinite : C.shape.active.Finite) {x : M}
    (hx : x ∈ frontier (⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier)) :
    ∃ i ∈ C.shape.active, x ∈ frontier (C.neck i).carrier := by
  have : Finite {i // i ∈ C.shape.active} := hfinite.to_subtype
  have hxc := frontier_subset_closure hx
  rw [closure_iUnion_of_finite] at hxc
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxc
  refine ⟨i.1, i.2, ?_⟩
  rw [(C.neck i.1).carrier_open.frontier_eq]
  refine ⟨hi, ?_⟩
  intro hxi
  have hU : IsOpen (⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier) :=
    isOpen_iUnion fun i => (C.neck i.1).carrier_open
  exact (hU.frontier_eq ▸ hx).2 (mem_iUnion.mpr ⟨i, hxi⟩)

end BalancedNeckChain

namespace NeckOnlyCover

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]



theorem exists_neck_at_finite_chain_end (H : NeckOnlyCover g)
    (C : BalancedNeckChain g H.epsilon) (hfinite : C.shape.active.Finite)
    (hcenters : ∀ i ∈ C.shape.active, (C.neck i).center ∈ H.X)
    (hmiss : ¬ H.X ⊆ ⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier) :
    ∃ N ∈ H.necks, N.center ∈ H.X ∧
      N.center ∈ frontier (⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier) ∧
      ∃ i ∈ C.shape.active,
        N.center ∈ closure ((C.neck i).region (-H.epsilon⁻¹) (-H.epsilon⁻¹ / 2)) ∨
        N.center ∈ closure ((C.neck i).region (H.epsilon⁻¹ / 2) H.epsilon⁻¹) := by
  obtain ⟨N, hN, hx, hxf, -, -⟩ := H.exists_neck_at_chain_frontier C hcenters hmiss
  obtain ⟨i, hi, hxi⟩ := C.exists_mem_frontier_of_finite hfinite hxf
  refine ⟨N, hN, hx, hxf, i, hi, ?_⟩
  have he : 0 < H.epsilon⁻¹ := inv_pos.mpr H.epsilon_pos
  have hleft : -(C.neck i).epsilon⁻¹ < -H.epsilon⁻¹ / 2 := by
    rw [C.epsilon_eq i hi]
    linarith
  have hright : H.epsilon⁻¹ / 2 < (C.neck i).epsilon⁻¹ := by
    rw [C.epsilon_eq i hi]
    linarith
  simpa only [C.epsilon_eq i hi, mem_union] using
    (C.neck i).frontier_subset_closure_ends hleft hright hxi

end NeckOnlyCover

end PoincareConjecture
