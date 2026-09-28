import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Regions.Smooth
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Band.GraphSlab
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.SliceProjection













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)


theorem mem_closure_region_iff_of_mem_carrier {a b : ℝ} (hab : a < b)
    {x : M} (hx : x ∈ N.carrier) :
    x ∈ closure (N.region a b) ↔
      a ≤ (N.coordinate_inverse x).2 ∧ (N.coordinate_inverse x).2 ≤ b := by
  have himage : N.coordinatePartialHomeomorph.symm.IsImage
      (N.region a b) ((univ : Set UnitTwoSphere) ×ˢ Ioo a b) := by
    intro y hy
    change (N.coordinate_inverse y).1 ∈ univ ∧
      (N.coordinate_inverse y).2 ∈ Ioo a b ↔
        y ∈ N.carrier ∧ a < (N.coordinate_inverse y).2 ∧
          (N.coordinate_inverse y).2 < b
    simp only [mem_univ, true_and, mem_Ioo, show y ∈ N.carrier from hy]
  have h := himage.closure.apply_mem_iff hx
  change N.coordinate_inverse x ∈ closure ((univ : Set UnitTwoSphere) ×ˢ Ioo a b) ↔
    x ∈ closure (N.region a b) at h
  simpa only [closure_prod_eq, closure_univ, closure_Ioo hab.ne,
    mem_prod, mem_univ, true_and, mem_Icc] using h.symm

variable [T2Space M]


theorem closure_region_eq_closedGraphSlab {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hab : a < b) (hb : b < N.epsilon⁻¹) :
    closure (N.region a b) = N.closedGraphSlab (fun _ => a) (fun _ => b) := by
  have hclosed := (N.isCompact_closedGraphSlab (fun _ => a) (fun _ => b)
    continuous_const continuous_const (fun _ => ⟨ha, hab.trans hb⟩)
    (fun _ => ⟨ha.trans hab, hb⟩) (fun _ => hab)).isClosed
  apply subset_antisymm
  · exact closure_minimal (fun _ hx => ⟨hx.1, hx.2.1.le, hx.2.2.le⟩) hclosed
  · intro x hx
    exact (N.mem_closure_region_iff_of_mem_carrier hab hx.1).mpr hx.2


theorem frontier_region_eq_slices {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hab : a < b) (hb : b < N.epsilon⁻¹) :
    frontier (N.region a b) =
      range (fun q : UnitTwoSphere => N.coordinate_map (q, a)) ∪
        range (fun q : UnitTwoSphere => N.coordinate_map (q, b)) := by
  have hopen : IsOpen (N.region a b) :=
    N.coordinate_inverse_smooth.continuousOn.snd.isOpen_inter_preimage
      N.carrier_open isOpen_Ioo
  rw [hopen.frontier_eq, N.closure_region_eq_closedGraphSlab ha hab hb]
  ext x
  rw [mem_union, N.mem_coordinate_graph_iff (fun _ => a)
    (fun _ => ⟨ha, hab.trans hb⟩), N.mem_coordinate_graph_iff (fun _ => b)
    (fun _ => ⟨ha.trans hab, hb⟩)]
  change ((x ∈ N.carrier ∧ a ≤ (N.coordinate_inverse x).2 ∧
      (N.coordinate_inverse x).2 ≤ b) ∧
      ¬ (x ∈ N.carrier ∧ a < (N.coordinate_inverse x).2 ∧
        (N.coordinate_inverse x).2 < b)) ↔ _
  constructor
  · rintro ⟨⟨hx, hlo, hhi⟩, hn⟩
    by_cases h : (N.coordinate_inverse x).2 = a
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, le_antisymm hhi (le_of_not_gt (fun hlt =>
        hn ⟨hx, lt_of_le_of_ne hlo (Ne.symm h), hlt⟩))⟩
  · rintro (⟨hx, heq⟩ | ⟨hx, heq⟩)
    · exact ⟨⟨hx, heq.symm.le, heq ▸ hab.le⟩, fun h => by
        have := h.2.1
        rw [heq] at this
        exact (lt_irrefl _ this)⟩
    · exact ⟨⟨hx, heq ▸ hab.le, heq.le⟩, fun h => by
        have := h.2.2
        rw [heq] at this
        exact (lt_irrefl _ this)⟩

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.NoncompactKappa.Positive.SoulNeckRegion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}
  {S : RiemannianMetric.PointSoulData (K.flow.metric 0)} {epsilon D R : ℝ}
  (G : SoulNeckRegion K S epsilon D R) (N : EpsilonNeck (K.flow.metric 0))


def bufferedCarrier (t : ℝ) : Set M := G.inside ∪ N.region (-N.epsilon⁻¹) t

theorem bufferedCarrier_open (t : ℝ) : IsOpen (G.bufferedCarrier N t) :=
  G.inside_open.union (N.isOpen_region _ _)

variable (hsphere : N.central_sphere = G.neck.terminal_neck.central_sphere)
  (hheight : ∀ y ∈ N.carrier, y ∈ closure G.inside ↔ (N.coordinate_inverse y).2 ≤ 0)

include hsphere hheight

theorem inside_height_iff {x : M} (hx : x ∈ N.carrier) :
    x ∈ G.inside ↔ (N.coordinate_inverse x).2 < 0 := by
  constructor
  · intro hi
    have hle := (hheight x hx).mp (subset_closure hi)
    apply lt_of_le_of_ne hle
    intro heq
    have hf : x ∈ frontier G.inside := by
      rw [G.inside_frontier, ← hsphere]
      exact (N.mem_central_sphere_iff x).mpr ⟨hx, heq⟩
    exact hf.2 (by simpa only [G.inside_open.interior_eq] using hi)
  · intro hlt
    have hc := (hheight x hx).mpr hlt.le
    by_contra hi
    have hf : x ∈ frontier G.inside := by
      rw [G.inside_open.frontier_eq]
      exact ⟨hc, hi⟩
    rw [G.inside_frontier, ← hsphere] at hf
    exact (ne_of_lt hlt) ((N.mem_central_sphere_iff x).mp hf).2

theorem bufferedCarrier_height_iff {t : ℝ} (ht : 0 < t)
    {x : M} (hx : x ∈ N.carrier) :
    x ∈ G.bufferedCarrier N t ↔ (N.coordinate_inverse x).2 < t := by
  constructor
  · rintro (hi | hn)
    · exact ((G.inside_height_iff N hsphere hheight hx).mp hi).trans ht
    · exact hn.2.2
  · intro hlt
    exact Or.inr ⟨hx, (N.coordinate_inverse_mem x hx).2.1, hlt⟩

omit hheight in
theorem closure_inside_subset_bufferedCarrier {t : ℝ} (ht : 0 < t) :
    closure G.inside ⊆ G.bufferedCarrier N t := by
  intro x hx
  by_cases hi : x ∈ G.inside
  · exact Or.inl hi
  · have hf : x ∈ frontier G.inside := by
      rw [G.inside_open.frontier_eq]
      exact ⟨hx, hi⟩
    rw [G.inside_frontier, ← hsphere] at hf
    obtain ⟨hxN, heq⟩ := (N.mem_central_sphere_iff x).mp hf
    exact Or.inr ⟨hxN, (N.coordinate_inverse_mem x hxN).2.1,
      by simpa only [heq] using ht⟩


theorem bufferedCarrier_diff_region {t : ℝ} (ht : 0 < t) :
    G.bufferedCarrier N t \ N.region 0 t = closure G.inside := by
  ext x
  constructor
  · rintro ⟨hi | hn, hout⟩
    · exact subset_closure hi
    · exact (hheight x hn.1).mpr (le_of_not_gt (fun hpos =>
        hout ⟨hn.1, hpos, hn.2.2⟩))
  · intro hc
    refine ⟨G.closure_inside_subset_bufferedCarrier N hsphere ht hc, ?_⟩
    intro hn
    exact (not_lt_of_ge ((hheight x hn.1).mp hc)) hn.2.1


theorem bufferedCarrier_inter_frontier_region {t : ℝ}
    (ht : 0 < t) (htN : t < N.epsilon⁻¹) :
    G.bufferedCarrier N t ∩ frontier (N.region 0 t) = N.central_sphere := by
  rw [N.frontier_region_eq_slices (neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos)) ht htN]
  ext x
  constructor
  · rintro ⟨hxU, hx0 | hxt⟩
    · have hx := (N.mem_coordinate_graph_iff (fun _ => (0 : ℝ))
        (fun _ => ⟨neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
          inv_pos.mpr N.epsilon_pos⟩)).mp hx0
      exact (N.mem_central_sphere_iff x).mpr hx
    · have hx := (N.mem_coordinate_graph_iff (fun _ => t)
        (fun _ => ⟨lt_trans (neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos)) ht, htN⟩)).mp hxt
      have hlt := (G.bufferedCarrier_height_iff N hsphere hheight ht hx.1).mp hxU
      exact False.elim ((ne_of_lt hlt) hx.2)
  · intro hx
    obtain ⟨hxN, heq⟩ := (N.mem_central_sphere_iff x).mp hx
    refine ⟨(G.bufferedCarrier_height_iff N hsphere hheight ht hxN).mpr
      (by simpa only [heq] using ht),
      Or.inl ?_⟩
    exact (N.mem_coordinate_graph_iff (fun _ => (0 : ℝ))
      (fun _ => ⟨neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
        inv_pos.mpr N.epsilon_pos⟩)).mpr ⟨hxN, heq⟩

omit hsphere in


theorem buffered_boundary_local_defining_function {t : ℝ} (ht : 0 < t)
    {x : M} (hx : x ∈ N.central_sphere) :
    ∃ U : Set M, ∃ f : M → ℝ,
      IsOpen U ∧ x ∈ U ∧ U ⊆ G.bufferedCarrier N t ∧
        (∀ y ∈ U, y ∈ closure G.inside ↔ f y ≤ 0) ∧ f x = 0 ∧
        ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f U ∧
        ∃ d : TangentSpace (𝓡 3) x, d ≠ 0 ∧ mvfderiv (𝓡 3) f x d ≠ 0 := by
  obtain ⟨hxN, hzero⟩ := (N.mem_central_sphere_iff x).mp hx
  let z := N.coordinate_inverse x
  let f : M → ℝ := fun y => (N.coordinate_inverse y).2
  let U := N.region (-N.epsilon⁻¹) t
  have hz : z ∈ N.cylinderDomain := N.coordinate_inverse_mem x hxN
  have hxU : x ∈ U := ⟨hxN, hz.2.1, by simpa only [hzero] using ht⟩
  have hf : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f N.carrier :=
    contMDiff_snd.comp_contMDiffOn N.coordinate_inverse_smooth
  refine ⟨U, f, N.isOpen_region _ _, hxU, fun _ hy => Or.inr hy,
    fun y hy => hheight y hy.1, hzero, hf.mono (fun _ hy => hy.1), ?_⟩
  let v : RoundCylinderTangent z := (0, 1)
  let d : TangentSpace (𝓡 3) x :=
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v
  have hi := (N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds hxN)).mdifferentiableAt (by simp)
  have hd : mvfderiv (𝓡 3) f x d = 1 := by
    change mvfderiv (𝓡 3) (Prod.snd ∘ N.coordinate_inverse) x d = 1
    rw [mvfderiv, mfderiv_comp x mdifferentiableAt_snd hi, mfderiv_snd]
    change (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x d).2 = 1
    have h := N.coordinate_inverse_mfderiv_map_prod hz v
    dsimp only [z] at h
    rw [N.coordinate_map_coordinate_inverse hxN] at h
    exact congrArg Prod.snd h
  refine ⟨d, ?_, by rw [hd]; norm_num⟩
  intro hd0
  rw [hd0, map_zero] at hd
  norm_num at hd

end PoincareConjecture.NoncompactKappa.Positive.SoulNeckRegion
