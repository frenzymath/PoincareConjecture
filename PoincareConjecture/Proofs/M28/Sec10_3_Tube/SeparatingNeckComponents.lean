import PoincareConjecture.Proofs.M28.Mathlib.CollarComplementComponents
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalGraphRegions
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckCollar










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}




theorem complement_components_of_isSeparating (N : EpsilonNeck g) (hsep : N.IsSeparating)
    {x₀ x₁ : M} (hx₀ : x₀ ∈ N.belowGraph_m28 (fun _ => 0))
    (hx₁ : x₁ ∈ N.aboveGraph_m28 (fun _ => 0)) :
    let C₀ := connectedComponentIn N.central_sphereᶜ x₀
    let C₁ := connectedComponentIn N.central_sphereᶜ x₁
    IsOpen C₀ ∧ IsOpen C₁ ∧ IsConnected C₀ ∧ IsConnected C₁ ∧
      Disjoint C₀ C₁ ∧ C₀ ∪ C₁ = N.central_sphereᶜ ∧
      frontier C₀ = N.central_sphere ∧ frontier C₁ = N.central_sphere ∧
      closure C₀ = C₀ ∪ N.central_sphere ∧ closure C₁ = C₁ ∪ N.central_sphere ∧
      N.belowGraph_m28 (fun _ => 0) ⊆ C₀ ∧ N.aboveGraph_m28 (fun _ => 0) ⊆ C₁ := by
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let C₀ := connectedComponentIn N.central_sphereᶜ x₀
  let C₁ := connectedComponentIn N.central_sphereᶜ x₁
  have hzero (q : UnitTwoSphere) : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hbelow := N.isConnected_belowGraph_m28 _ continuous_const hzero
  have habove := N.isConnected_aboveGraph_m28 _ continuous_const hzero
  have hbelowS : N.belowGraph_m28 (fun _ => 0) ⊆ N.central_sphereᶜ := by
    intro x hx hS
    exact (ne_of_lt hx.2) ((N.mem_central_sphere_iff_of_mem_carrier hx.1).mp hS)
  have haboveS : N.aboveGraph_m28 (fun _ => 0) ⊆ N.central_sphereᶜ := by
    intro x hx hS
    exact (ne_of_gt hx.2) ((N.mem_central_sphere_iff_of_mem_carrier hx.1).mp hS)
  have hpartition : N.carrier \ N.central_sphere =
      N.belowGraph_m28 (fun _ => 0) ∪ N.aboveGraph_m28 (fun _ => 0) := by
    ext x
    constructor
    · intro hx
      have hne : (N.coordinate_inverse x).2 ≠ 0 :=
        fun hz => hx.2 ((N.mem_central_sphere_iff_of_mem_carrier hx.1).mpr hz)
      exact (lt_or_gt_of_ne hne).imp (fun h => ⟨hx.1, h⟩) (fun h => ⟨hx.1, h⟩)
    · rintro (hx | hx)
      · exact ⟨hx.1, hbelowS hx⟩
      · exact ⟨hx.1, haboveS hx⟩
  have hunion : N.central_sphereᶜ = C₀ ∪ C₁ :=
    compl_eq_union_connectedComponentIn_of_two_half_collar N.isClosed_central_sphere
      ⟨N.center, N.center_on_central_sphere⟩ N.carrier_open N.central_sphere_subset
      hpartition hbelow.isPreconnected habove.isPreconnected hx₀ hx₁
  have hC₀ : IsConnected C₀ := isConnected_connectedComponentIn_iff.mpr (hbelowS hx₀)
  have hC₁ : IsConnected C₁ := isConnected_connectedComponentIn_iff.mpr (haboveS hx₁)
  have hne : C₀ ≠ C₁ := by
    intro heq
    apply hsep.2
    rw [PreconnectedSpace.connectedComponent_eq_univ, ← compl_eq_univ_sdiff,
      hunion, heq, union_self]
    exact hC₁
  have hdisjoint : Disjoint C₀ C₁ := by
    apply disjoint_left.mpr
    intro x hx₀ hx₁
    exact hne ((connectedComponentIn_eq hx₀).trans (connectedComponentIn_eq hx₁).symm)
  have hbelowC : N.belowGraph_m28 (fun _ => 0) ⊆ C₀ :=
    hbelow.isPreconnected.subset_connectedComponentIn hx₀ hbelowS
  have haboveC : N.aboveGraph_m28 (fun _ => 0) ⊆ C₁ :=
    habove.isPreconnected.subset_connectedComponentIn hx₁ haboveS
  have hclosure : N.central_sphere ⊆ closure (N.belowGraph_m28 (fun _ => 0)) ∩
      closure (N.aboveGraph_m28 (fun _ => 0)) := by
    intro x hx
    have hxN := N.central_sphere_subset hx
    have hxzero := (N.mem_central_sphere_iff_of_mem_carrier hxN).mp hx
    have heq : N.coordinate_map ((N.coordinate_inverse x).1, 0) = x := by
      rw [← hxzero, Prod.mk.eta, N.coordinate_map_coordinate_inverse hxN]
    exact heq ▸ ⟨N.coordinate_graph_mem_closure_belowGraph_m28 _ hzero _,
      N.coordinate_graph_mem_closure_aboveGraph_m28 _ hzero _⟩
  have hf₀ : frontier C₀ = N.central_sphere :=
    frontier_connectedComponentIn_compl_eq_of_closure_subset N.isClosed_central_sphere
      hbelowC (fun _ hx => (hclosure hx).1)
  have hf₁ : frontier C₁ = N.central_sphere :=
    frontier_connectedComponentIn_compl_eq_of_closure_subset N.isClosed_central_sphere
      haboveC (fun _ hx => (hclosure hx).2)
  exact ⟨N.isClosed_central_sphere.isOpen_compl.connectedComponentIn,
    N.isClosed_central_sphere.isOpen_compl.connectedComponentIn, hC₀, hC₁,
    hdisjoint, hunion.symm, hf₀, hf₁,
    (closure_eq_self_union_frontier C₀).trans (congrArg (C₀ ∪ ·) hf₀),
    (closure_eq_self_union_frontier C₁).trans (congrArg (C₁ ∪ ·) hf₁), hbelowC, haboveC⟩

end PoincareConjecture.EpsilonNeck
