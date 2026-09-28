import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.NoReturn
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.GraphTransport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Collar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Segment











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem positive_half_subset_component_complement_of_tail
    (N : EpsilonNeck g) {T : Set M} (hT : IsPreconnected T)
    {c : ℝ} (hc : -N.epsilon⁻¹ < c)
    (havoid : Disjoint T (N.region (-N.epsilon⁻¹) c))
    (hquarter : N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ T)
    {p : M} (hp : p ∈ closure T) (hpout : p ∉ N.carrier) :
    N.region 0 N.epsilon⁻¹ ⊆ connectedComponentIn N.central_sphereᶜ p := by
  have hi := inv_pos.mpr N.epsilon_pos
  obtain ⟨s, hslo, hshi⟩ := exists_between (lt_min hc (neg_lt_zero.mpr hi))
  have hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨hslo, (hshi.trans_le (min_le_right _ _)).trans hi⟩
  have hsc : s < c := hshi.trans_le (min_le_left _ _)
  obtain ⟨r, hr, hrN, hbound⟩ := N.exists_graph_collar (fun _ => s)
    continuous_const (fun _ => hs)
  let e := N.graphTransport hr hrN (fun _ => s) continuous_const hbound
  have hfixed {x : M} (hx : x ∉ N.carrier) : e x = x :=
    N.graphTransport_fixed hr hrN (fun _ => s) continuous_const hbound
      (fun hk => hx (N.closedCollar_subset_carrier hrN hk))
  have hclavoid : closure T ⊆ (N.region (-N.epsilon⁻¹) c)ᶜ :=
    closure_minimal havoid.subset_compl_right (N.isOpen_region _ _).isClosed_compl
  have hgraphbelow : range (fun q : UnitTwoSphere => N.coordinate_map (q, s)) ⊆
      N.region (-N.epsilon⁻¹) c := by
    rintro x ⟨q, rfl⟩
    have hz : (q, s) ∈ N.cylinderDomain := ⟨mem_univ _, hs⟩
    refine ⟨N.coordinate_map_mem hz, ?_⟩
    rw [N.coordinate_inverse_coordinate_map hz]
    exact ⟨hslo, hsc⟩
  let U := e.symm '' closure T
  have hU : IsPreconnected U := hT.closure.image e.symm e.symm.continuous.continuousOn
  have hpU : p ∈ U := by
    refine ⟨p, hp, ?_⟩
    apply e.injective
    rw [e.apply_symm_apply, hfixed hpout]
  have hUavoid : U ⊆ N.central_sphereᶜ := by
    rintro x ⟨y, hy, heq⟩ hxS
    have hey : e x = y := by rw [← heq, e.apply_symm_apply]
    have hygraph : y ∈ range (fun q : UnitTwoSphere => N.coordinate_map (q, s)) := by
      rw [← N.graphTransport_image_central_sphere hr hrN (fun _ => s)
        continuous_const hbound]
      exact ⟨x, hxS, hey⟩
    exact hclavoid hy (hgraphbelow hygraph)
  let t := (max r (N.epsilon⁻¹ / 2) + N.epsilon⁻¹) / 2
  have htmax : max r (N.epsilon⁻¹ / 2) < N.epsilon⁻¹ :=
    max_lt hrN (by linarith)
  have htr : r < t := by dsimp [t]; linarith [le_max_left r (N.epsilon⁻¹ / 2)]
  have htquarter : N.epsilon⁻¹ / 2 < t := by
    dsimp [t]
    linarith [le_max_right r (N.epsilon⁻¹ / 2)]
  have ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    dsimp [t] at htquarter ⊢
    constructor <;> linarith
  let q := (N.coordinate_inverse N.center).1
  let z := N.coordinate_map (q, t)
  have hzdom : (q, t) ∈ N.cylinderDomain := ⟨mem_univ _, ht⟩
  have hzquarter : z ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ := by
    refine ⟨N.coordinate_map_mem hzdom, ?_⟩
    change (N.coordinate_inverse (N.coordinate_map (q, t))).2 ∈ Ioo _ _
    rw [N.coordinate_inverse_coordinate_map hzdom]
    exact ⟨htquarter, ht.2⟩
  have hzpos : z ∈ N.region 0 N.epsilon⁻¹ :=
    ⟨hzquarter.1, by linarith [hzquarter.2.1], hzquarter.2.2⟩
  have hzfixed : e z = z := by
    apply N.graphTransport_fixed hr hrN (fun _ => s) continuous_const hbound
    intro hzK
    have hcoord := ((N.mem_coordinate_slab_iff (neg_lt_neg hrN) hrN).mp hzK).2
    change (N.coordinate_inverse (N.coordinate_map (q, t))).2 ∈ Icc (-r) r at hcoord
    rw [N.coordinate_inverse_coordinate_map hzdom] at hcoord
    exact (not_le_of_gt htr) hcoord.2
  have hzU : z ∈ U := by
    refine ⟨z, subset_closure (hquarter hzquarter), ?_⟩
    apply e.injective
    rw [e.apply_symm_apply, hzfixed]
  have hpositive := N.isConnected_region (a := 0) (b := N.epsilon⁻¹)
    (by linarith) le_rfl hi
  have hpositiveavoid : N.region 0 N.epsilon⁻¹ ⊆ N.central_sphereᶜ := by
    intro x hx hxS
    exact disjoint_left.mp (N.central_sphere_disjoint_region 0 N.epsilon⁻¹ (Or.inr le_rfl)) hxS hx
  have hconnected := hU.union z hzU hzpos hpositive.isPreconnected
  exact subset_union_right.trans (hconnected.subset_connectedComponentIn (Or.inl hpU)
    (union_subset hUavoid hpositiveavoid))

end PoincareConjecture.EpsilonNeck
