import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerOriginalAtlas
import PoincareConjecture.Proofs.M76.Mathlib.ClosedBallDeletedCellEnd

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

private theorem hasOneSimplyConnectedEnd_of_closedBall_cell
    {E F T Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace T] [T2Space T] [CompactSpace T]
    [TopologicalSpace Y] (Q : OpenPartialHomeomorph F T)
    (h0 : (0 : F) ∈ Q.source) (hdim : 2 < Module.finrank ℝ (E × F))
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (j : Y → closedBall (0 : E) 1 × T) (hj : Topology.IsEmbedding j)
    (hrange : range j = {z | ‖(z.1 : E)‖ ≤ a ∧ z.2 = Q 0}ᶜ) :
    HasOneSimplyConnectedEnd Y := by
  intro C hC
  let A := j '' C
  let Z := {z : closedBall (0 : E) 1 × T | ‖(z.1 : E)‖ ≤ a ∧ z.2 = Q 0}
  have hA : IsCompact A := hC.image hj.continuous
  have hdis : Disjoint A Z := by
    apply Set.disjoint_left.mpr
    intro z hz hzZ
    have hzR : z ∈ range j := image_subset_range j C hz
    rw [hrange] at hzR
    exact hzR hzZ
  obtain ⟨K, hK, hAK, hKZ, hsc⟩ :=
    Q.exists_compact_closedBall_deleted_cell_core hdim h0 ha ha1 hA hdis
  let D : Set Y := j ⁻¹' K
  have hKrange : K ⊆ range j := by
    rw [hrange]
    exact fun z hz hzZ => Set.disjoint_left.mp hKZ hz hzZ
  have hD : IsCompact D := hj.isInducing.isCompact_preimage' hK hKrange
  have hCD : C ⊆ interior D := by
    intro x hx
    apply (isOpen_interior.preimage hj.continuous).subset_interior_iff.mpr
      (preimage_mono interior_subset)
    exact hAK (mem_image_of_mem j hx)
  have hcomplement : j '' Dᶜ = Kᶜ \ Z := by
    change j '' (j ⁻¹' K)ᶜ = Kᶜ \ Z
    rw [← preimage_compl, image_preimage_eq_inter_range, hrange]
    rfl
  have hDsc : IsSimplyConnected Dᶜ := by
    apply hj.isSimplyConnected_image.mp
    rw [hcomplement]
    exact hsc
  refine ⟨D, hD, hCD, hDsc.isPathConnected.isConnected, ?_⟩
  intro x p hp
  obtain ⟨H, hH⟩ :=
    (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hDsc).2 x p hp
  refine ⟨H, fun z hz => ?_⟩
  exact hH z (interior_subset (hCD hz))

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "L" => hamiltonLowerPeriodLattice κ
local notation "W" => LatticeHandleAmbient ι κ L
local notation "T" => ((κ → ℝ) ⧸ (Submodule.toAddSubgroup (hamiltonLowerPeriodLattice κ)))

theorem lower_original_domain_hasOneSimplyConnectedEnd
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    {a b : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hb : 1 < b)
    (U : TopologicalSpace.Opens W)
    (hU : (U : Set W) =
      (ball (0 : ι → ℝ) b ×ˢ {hamiltonLowerLatticePuncture κ}ᶜ) ∪
        ({x : ι → ℝ | a < ‖x‖ ∧ ‖x‖ < b} ×ˢ univ)) :
    HasOneSimplyConnectedEnd
      ((Subtype.val : U → W) ⁻¹' latticeHandleDomain ι κ L) ∧
      IsCompact (frontier ((Subtype.val : U → W) ⁻¹' latticeHandleDomain ι κ L)) := by
  classical
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  let : DiscreteTopology L := inferInstance
  let : CompactSpace T := (hamiltonLowerLatticePiEquiv κ).symm.compactSpace
  let : T2Space T := (hamiltonLowerLatticePiEquiv κ).isEmbedding.t2Space
  let R : Set U := (Subtype.val : U → W) ⁻¹' latticeHandleDomain ι κ L
  let j : R → LatticeHandle ι κ L := fun z =>
    (⟨((z : U) : W).1, z.property.1⟩, ((z : U) : W).2)
  have hk : Topology.IsEmbedding (fun z : R =>
      (⟨((z : U) : W), z.property⟩ : latticeHandleDomain ι κ L)) :=
    (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).codRestrict
      (latticeHandleDomain ι κ L) (fun z => z.property)
  have hj : Topology.IsEmbedding j :=
    (latticeHandleDomainEquiv ι κ L).isEmbedding.comp hk
  have hjrange : range j =
      {z : LatticeHandle ι κ L | ‖(z.1 : ι → ℝ)‖ ≤ a ∧
        z.2 = hamiltonLowerLatticePuncture κ}ᶜ := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩ hz
      have hy := (y : U).property
      change ((y : U) : W) ∈ (U : Set W) at hy
      rw [hU] at hy
      rcases hy with hy | hy
      · exact hy.2 hz.2
      · exact (not_lt_of_ge hz.1) hy.1.1
    · intro hz
      let w : W := ((z.1 : ι → ℝ), z.2)
      have hwU : w ∈ (U : Set W) := by
        rw [hU]
        have hnorm : ‖(z.1 : ι → ℝ)‖ < b :=
          (mem_closedBall_zero_iff.mp z.1.property).trans_lt hb
        by_cases hzp : z.2 = hamiltonLowerLatticePuncture κ
        · exact Or.inr ⟨⟨lt_of_not_ge (fun hza => hz ⟨hza, hzp⟩), hnorm⟩, mem_univ _⟩
        · exact Or.inl ⟨mem_ball_zero_iff.mpr hnorm, hzp⟩
      exact ⟨⟨⟨w, hwU⟩, z.1.property, mem_univ _⟩, rfl⟩
  have hq : IsLocalHomeomorph (QuotientAddGroup.mk : (κ → ℝ) → T) :=
    ((hamiltonLowerPeriodLattice κ).toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap.isLocalHomeomorph
  obtain ⟨q, hqsource, hqval⟩ := hq (fun _ : κ => (256 : ℝ))
  let shift := (ContinuousAffineEquiv.constVAdd ℝ (κ → ℝ)
    (fun _ => (256 : ℝ))).toHomeomorph
  let Q := shift.transOpenPartialHomeomorph q
  have hQ0 : (0 : κ → ℝ) ∈ Q.source := by
    change (fun _ : κ => (256 : ℝ)) + 0 ∈ q.source
    simpa only [add_zero] using hqsource
  have hp : Q 0 = hamiltonLowerLatticePuncture κ := by
    change q ((fun _ : κ => (256 : ℝ)) + 0) =
      QuotientAddGroup.mk (fun _ : κ => (256 : ℝ))
    rw [add_zero]
    exact congrFun hqval.symm _
  have hfin : 2 < Module.finrank ℝ ((ι → ℝ) × (κ → ℝ)) := by
    simp only [Module.finrank_prod, Module.finrank_pi]
    omega
  refine ⟨hasOneSimplyConnectedEnd_of_closedBall_cell Q hQ0 hfin ha ha1 j hj
    (by simpa only [hp] using hjrange), ?_⟩
  let S : Set W := sphere (0 : ι → ℝ) 1 ×ˢ univ
  have hS : IsCompact S := (isCompact_sphere (0 : ι → ℝ) 1).prod isCompact_univ
  have hSU : S ⊆ (U : Set W) := by
    intro z hz
    have hnorm : ‖z.1‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz.1
    rw [hU]
    exact Or.inr ⟨⟨by simpa only [hnorm] using ha1, by simpa only [hnorm] using hb⟩,
      mem_univ _⟩
  have hfront : frontier R = (Subtype.val : U → W) ⁻¹' S := by
    have hopen : IsOpenMap (Subtype.val : U → W) := U.isOpen.isOpenMap_subtype_val
    have heq := hopen.preimage_frontier_eq_frontier_preimage
      (continuous_subtype_val : Continuous (Subtype.val : U → W)) (latticeHandleDomain ι κ L)
    have hHS : frontier (latticeHandleDomain ι κ L) = S := by
      simp only [latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
      rfl
    exact heq.symm.trans (congrArg (fun s => (Subtype.val : U → W) ⁻¹' s) hHS)
  rw [hfront]
  exact Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hS
    (fun z hz => ⟨⟨z, hSU hz⟩, rfl⟩)

end PoincareConjecture.M76
