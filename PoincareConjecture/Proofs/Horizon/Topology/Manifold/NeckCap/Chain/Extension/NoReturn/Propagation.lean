import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn.Tail
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.ThreeQuarter
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Connected
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Union
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Finite.InitialEnd










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.BalancedNeckChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {ε : ℝ}

theorem positive_half_subset_component_complement_of_outer_frontier
    (C : BalancedNeckChain g ε) {b : ℤ} (hb : b ∈ C.shape.active)
    {p : M} (hp : p ∈ closure ((C.neck b).region (ε⁻¹ / 2) ε⁻¹))
    (hpout : p ∉ C.unionOpen) {i : ℤ} (hi : i ∈ C.shape.active) (hib : i ≤ b) :
    (C.neck i).region 0 ε⁻¹ ⊆
      connectedComponentIn (C.neck i).central_sphereᶜ p := by
  have hεi := C.epsilon_eq i hi
  have hεb := C.epsilon_eq b hb
  rcases eq_or_lt_of_le hib with rfl | hib
  · simpa only [hεi] using
      (C.neck i).positive_half_subset_component_complement_of_mem_closure_positive_quarter
        (by simpa only [hεi] using hp)
  have hactive : Ioc i b ⊆ C.shape.active := by
    intro j hj
    exact C.shape.ordConnected_active.out hi hb ⟨hj.1.le, hj.2⟩
  have hT := C.isConnected_subchain_union
    (show (Ioc i b).Nonempty from ⟨b, hib, le_rfl⟩) inferInstance hactive
  have hεpos : 0 < ε := hεi ▸ (C.neck i).epsilon_pos
  obtain ⟨c, hc, havoid⟩ := C.exists_common_negative_end_cut hi (Finset.Ioc i b)
    (fun j hj => ⟨hactive (Finset.mem_Ioc.mp hj), (Finset.mem_Ioc.mp hj).1⟩)
    (b := 0) (neg_lt_zero.mpr (inv_pos.mpr hεpos))
  have hdisjoint : Disjoint (⋃ j ∈ Ioc i b, (C.neck j).carrier)
      ((C.neck i).region (-ε⁻¹) c) := by
    apply disjoint_left.mpr
    intro x hx hxend
    rcases mem_iUnion.mp hx with ⟨j, hx⟩
    rcases mem_iUnion.mp hx with ⟨hj, hx⟩
    exact disjoint_left.mp (havoid j (Finset.mem_Ioc.mpr hj)) hx hxend
  have hnext : i + 1 ∈ Ioc i b := ⟨by omega, by omega⟩
  have hquarter : (C.neck i).region (ε⁻¹ / 2) ε⁻¹ ⊆
      ⋃ j ∈ Ioc i b, (C.neck j).carrier := by
    intro x hx
    exact mem_iUnion.mpr ⟨i + 1, mem_iUnion.mpr ⟨hnext,
      (C.overlap_contains_quarters i hi (hactive hnext)).1 hx⟩⟩
  have hpT : p ∈ closure (⋃ j ∈ Ioc i b, (C.neck j).carrier) := by
    apply closure_mono (s := (C.neck b).region (ε⁻¹ / 2) ε⁻¹) _ hp
    intro x hx
    exact mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨⟨hib, le_rfl⟩, hx.1⟩⟩
  have hpN : p ∉ (C.neck i).carrier := by
    intro hpN
    exact hpout (mem_iUnion.mpr ⟨⟨i, hi⟩, hpN⟩)
  simpa only [hεi] using (C.neck i).positive_half_subset_component_complement_of_tail
    hT.isPreconnected (by simpa only [hεi] using hc.1)
    (by simpa only [hεi] using hdisjoint)
    (by simpa only [hεi] using hquarter) hpT hpN

end PoincareConjecture.BalancedNeckChain
