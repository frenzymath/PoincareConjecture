import PoincareConjecture.Proofs.M02.Topology.CWThreeHomotopyEquivalence
import PoincareConjecture.Proofs.M02.Topology.SphereGeneratorMap









set_option autoImplicit false

open Set Metric
open scoped Topology unitInterval ContinuousMap

universe u

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

open _root_.Topology.RelCWComplex

theorem nonempty_cw_zero_cell
    {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X}
    [_root_.Topology.CWComplex C] (hC : C.Nonempty) : Nonempty (cell C 0) := by
  classical
  have hcells : ∃ n : Nat, Nonempty (cell C n) := by
    obtain ⟨x, hx⟩ := hC
    rw [← _root_.Topology.CWComplex.iUnion_openCell_eq_complex (C := C)] at hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨j, _⟩ := mem_iUnion.mp hn
    exact ⟨n, ⟨j⟩⟩
  by_cases hzero : Nat.find hcells = 0
  · simpa only [hzero] using Nat.find_spec hcells
  · obtain ⟨j⟩ := Nat.find_spec hcells
    obtain ⟨x, hx⟩ := nonempty_cellFrontier hzero j
    obtain ⟨m, hm, j', _⟩ := _root_.Topology.CWComplex.mem_skeletonLT_iff.mp
      (cellFrontier_subset_skeletonLT (Nat.find hcells) j hx)
    have hlt : m < Nat.find hcells := by exact_mod_cast hm
    exact False.elim (Nat.find_min hcells hlt ⟨j'⟩)

theorem nonempty_homotopyEquiv_sphere_of_cw_three_pi_int
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {C : Set X} [_root_.Topology.CWComplex C] [PathConnectedSpace C]
    (hdim : (skeletonLT C ((3 : ℕ∞) + 1) : Set X) = C)
    (hpi1 : ∀ x : C, Subsingleton (HomotopyGroup.Pi 1 C x))
    (hpi2 : ∀ x : C, Subsingleton (HomotopyGroup.Pi 2 C x))
    (eC : ∀ x : C, HomotopyGroup.Pi 3 C x ≃* Multiplicative Int)
    (eS : ∀ s : sphere (0 : EuclideanSpace Real (Fin 4)) 1,
      HomotopyGroup.Pi 3 (sphere (0 : EuclideanSpace Real (Fin 4)) 1) s ≃*
        Multiplicative Int) :
    Nonempty (C ≃ₕ sphere (0 : EuclideanSpace Real (Fin 4)) 1) := by
  obtain ⟨j0⟩ := nonempty_cw_zero_cell (C := C)
    (Set.nonempty_coe_sort.mp (inferInstance : Nonempty C))
  let x0 : C := ⟨map 0 j0 0,
    (skeletonLT C 3).subset_complex (skeletonLT_mono (by norm_num)
      (closedCell_subset_skeletonLT 0 j0 ⟨0, by simp, rfl⟩))⟩
  obtain ⟨q, hq, hfiber⟩ := exists_cube_boundary_sphere_quotient 2
  obtain ⟨f, hbase, hbij⟩ := exists_sphere_map_of_homotopyGroup_int_equiv
    2 q hq hfiber x0 (eS _) (eC x0)
  exact nonempty_homotopyEquiv_of_cw_three_pi_bijective
    hdim hpi1 hpi2 x0 j0 rfl q hq hfiber f hbase hbij

end

end PoincareConjecture.Proofs.M02.Topology
