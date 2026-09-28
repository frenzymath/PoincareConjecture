import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.GraphTransport
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalCapCollar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Reversal










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

def belowGraph_m28 (f : UnitTwoSphere → ℝ) : Set M :=
  {x | x ∈ N.carrier ∧ (N.coordinate_inverse x).2 < f (N.coordinate_inverse x).1}

def aboveGraph_m28 (f : UnitTwoSphere → ℝ) : Set M :=
  {x | x ∈ N.carrier ∧ f (N.coordinate_inverse x).1 < (N.coordinate_inverse x).2}

theorem isOpen_belowGraph_m28 (f : UnitTwoSphere → ℝ) (hf : Continuous f) :
    IsOpen (N.belowGraph_m28 f) := by
  have hc := N.coordinate_inverse_smooth.continuousOn.snd.sub
    (hf.comp_continuousOn N.coordinate_inverse_smooth.continuousOn.fst)
  have h := hc.isOpen_inter_preimage N.carrier_open (isOpen_Iio (a := (0 : ℝ)))
  convert h using 1
  ext x
  simp [belowGraph_m28]

theorem isOpen_aboveGraph_m28 (f : UnitTwoSphere → ℝ) (hf : Continuous f) :
    IsOpen (N.aboveGraph_m28 f) := by
  have hc := N.coordinate_inverse_smooth.continuousOn.snd.sub
    (hf.comp_continuousOn N.coordinate_inverse_smooth.continuousOn.fst)
  have h := hc.isOpen_inter_preimage N.carrier_open (isOpen_Ioi (a := (0 : ℝ)))
  convert h using 1
  ext x
  simp [aboveGraph_m28, sub_pos]

theorem mem_coordinate_graph_iff_m28 (f : UnitTwoSphere → ℝ)
    (hdom : ∀ q, f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) {x : M} :
    x ∈ range (fun q : UnitTwoSphere => N.coordinate_map (q, f q)) ↔
      x ∈ N.carrier ∧ (N.coordinate_inverse x).2 = f (N.coordinate_inverse x).1 := by
  constructor
  · rintro ⟨q, rfl⟩
    have hz : (q, f q) ∈ N.cylinderDomain := ⟨mem_univ _, hdom q⟩
    exact ⟨N.coordinate_map_mem hz, by rw [N.coordinate_inverse_coordinate_map hz]⟩
  · rintro ⟨hx, heq⟩
    refine ⟨(N.coordinate_inverse x).1, ?_⟩
    change N.coordinate_map ((N.coordinate_inverse x).1,
      f (N.coordinate_inverse x).1) = x
    rw [← heq, Prod.mk.eta, N.coordinate_map_coordinate_inverse hx]

theorem isConnected_belowGraph_m28 (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hdom : ∀ q, f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    IsConnected (N.belowGraph_m28 f) := by
  obtain ⟨r, hr, hrN, hbound⟩ := N.exists_graph_collar f hf hdom
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  let T : Set RoundCylinderSpace := univ ×ˢ Ioo (-N.epsilon⁻¹) 0
  let F : RoundCylinderSpace → M :=
    fun z => N.coordinate_map (Homeomorph.Vertical.graphMap r f z)
  have hmem (z : RoundCylinderSpace) (hz : z ∈ T) :
      Homeomorph.Vertical.graphMap r f z ∈ N.cylinderDomain := by
    refine ⟨mem_univ _, ?_⟩
    exact (Homeomorph.Vertical.move_mem_Ioo_iff hr hrN.le (hbound z.1)).mpr
      ⟨hz.2.1, hz.2.2.trans (inv_pos.mpr N.epsilon_pos)⟩
  have hF : ContinuousOn F T := N.coordinate_map_smooth.continuousOn.comp
    (Homeomorph.Vertical.continuous_graphMap hf).continuousOn hmem
  have heq : F '' T = N.belowGraph_m28 f := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨N.coordinate_map_mem (hmem z hz), ?_⟩
      change (N.coordinate_inverse
        (N.coordinate_map (Homeomorph.Vertical.graphMap r f z))).2 < _
      rw [N.coordinate_inverse_coordinate_map (hmem z hz)]
      change Homeomorph.Vertical.move r (f z.1) z.2 < f z.1
      simpa only [Homeomorph.Vertical.move_zero hr] using
        Homeomorph.Vertical.strictMono_move hr (hbound z.1) hz.2.2
    · rintro ⟨hx, hbelow⟩
      obtain ⟨t, ht⟩ := Homeomorph.Vertical.surjective_move
        (r := r) (h := f (N.coordinate_inverse x).1) (N.coordinate_inverse x).2
      have hmono := Homeomorph.Vertical.strictMono_move hr (hbound (N.coordinate_inverse x).1)
      have htdom : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
        (Homeomorph.Vertical.move_mem_Ioo_iff hr hrN.le
          (hbound (N.coordinate_inverse x).1)).mp (ht ▸ (N.coordinate_inverse_mem x hx).2)
      have htneg : t < 0 := hmono.lt_iff_lt.mp (by
        rw [ht, Homeomorph.Vertical.move_zero hr]
        exact hbelow)
      refine ⟨((N.coordinate_inverse x).1, t), ⟨mem_univ _, htdom.1, htneg⟩, ?_⟩
      change N.coordinate_map ((N.coordinate_inverse x).1,
        Homeomorph.Vertical.move r (f (N.coordinate_inverse x).1) t) = x
      rw [ht, Prod.mk.eta, N.coordinate_map_coordinate_inverse hx]
  rw [← heq]
  exact (isConnected_univ.prod (isConnected_Ioo (neg_lt_zero.mpr
    (inv_pos.mpr N.epsilon_pos)))).image _ hF

theorem isConnected_aboveGraph_m28 (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hdom : ∀ q, f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    IsConnected (N.aboveGraph_m28 f) := by
  have h := N.reversed.isConnected_belowGraph_m28 (fun q => -f q) hf.neg (by
    intro q
    simp only [reversed_epsilon, mem_Ioo]
    constructor <;> linarith [(hdom q).1, (hdom q).2])
  convert h using 1
  ext x
  simp only [aboveGraph_m28, belowGraph_m28, mem_ofPred_eq, reversed_carrier,
    reversed_coordinate_inverse, neg_lt_neg_iff]

theorem coordinate_graph_mem_closure_belowGraph_m28 (f : UnitTwoSphere → ℝ)
    (hdom : ∀ q, f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (q : UnitTwoSphere) :
    N.coordinate_map (q, f q) ∈ closure (N.belowGraph_m28 f) := by
  let F : ℝ → M := fun t => N.coordinate_map (q, t)
  have hc : ContinuousWithinAt F (Ioo (-N.epsilon⁻¹) (f q)) (f q) :=
    N.coordinate_map_smooth.continuousOn.continuousAt
      (N.cylinderDomain_open.mem_nhds ⟨mem_univ _, hdom q⟩) |>.comp_continuousWithinAt
        (continuous_const.prodMk continuous_id).continuousWithinAt
  apply closure_mono (t := N.belowGraph_m28 f) ?_ (hc.mem_closure_image ?_)
  · rintro x ⟨t, ht, rfl⟩
    have hz : (q, t) ∈ N.cylinderDomain :=
      ⟨mem_univ _, ht.1, ht.2.trans (hdom q).2⟩
    refine ⟨N.coordinate_map_mem hz, ?_⟩
    change (N.coordinate_inverse (N.coordinate_map (q, t))).2 < _
    rw [N.coordinate_inverse_coordinate_map hz]
    exact ht.2
  · rw [closure_Ioo (hdom q).1.ne]
    exact ⟨(hdom q).1.le, le_rfl⟩

theorem coordinate_graph_mem_closure_aboveGraph_m28 (f : UnitTwoSphere → ℝ)
    (hdom : ∀ q, f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (q : UnitTwoSphere) :
    N.coordinate_map (q, f q) ∈ closure (N.aboveGraph_m28 f) := by
  have h := N.reversed.coordinate_graph_mem_closure_belowGraph_m28 (fun q => -f q) (by
    intro p
    simp only [reversed_epsilon, mem_Ioo]
    constructor <;> linarith [(hdom p).1, (hdom p).2]) q
  have heq : N.reversed.belowGraph_m28 (fun q => -f q) = N.aboveGraph_m28 f := by
    ext x
    simp only [aboveGraph_m28, belowGraph_m28, mem_ofPred_eq, reversed_carrier,
      reversed_coordinate_inverse, neg_lt_neg_iff]
  simpa only [reversed_coordinate_map, neg_neg, heq] using h

theorem mem_belowGraph_or_aboveGraph_of_not_mem_graph_m28
    (f : UnitTwoSphere → ℝ)
    (hdom : ∀ q, f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    {x : M} (hx : x ∈ N.carrier)
    (hgraph : x ∉ range (fun q => N.coordinate_map (q, f q))) :
    x ∈ N.belowGraph_m28 f ∨ x ∈ N.aboveGraph_m28 f := by
  have hcoord := (N.coordinate_inverse_mem x hx).2
  have hneq : (N.coordinate_inverse x).2 ≠ f (N.coordinate_inverse x).1 := by
    intro heq
    apply hgraph
    exact (N.mem_coordinate_graph_iff_m28 f hdom).mpr ⟨hx, heq⟩
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · exact Or.inl ⟨hx, hlt⟩
  · exact Or.inr ⟨hx, hgt⟩

theorem disjoint_belowGraph_aboveGraph_m28 (f : UnitTwoSphere → ℝ) :
    Disjoint (N.belowGraph_m28 f) (N.aboveGraph_m28 f) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (not_lt_of_ge (le_of_lt hx.2)) hy.2

end PoincareConjecture.EpsilonNeck
