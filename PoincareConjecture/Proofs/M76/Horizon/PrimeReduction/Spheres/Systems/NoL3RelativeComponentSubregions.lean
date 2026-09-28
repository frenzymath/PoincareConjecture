import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModelBoundary
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphericalSubregionModels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

private theorem relative_component_frontier_eq
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X}
    (hQ : IsCompact Q) (hPL : PLDomain e Q) {x : X} (hx : x ∈ Q) :
    frontier (connectedComponentIn Q x) = connectedComponentIn Q x ∩ frontier Q := by
  let : LocallyPathConnectedSpace Q := hPL.locallyPathConnectedSpace
  obtain ⟨U,hU,hCU⟩ := exists_open_inter_of_relative_open (connectedComponentIn_subset Q x)
    (isOpen_preimage_connectedComponentIn hx)
  exact frontier_eq_inter_of_eq_inter_open hQ.isClosed
    (isCompact_connectedComponentIn_of_mem hQ hx).isClosed hU hCU

theorem HasPuncturedSphereModel.of_original_relative_cut_component
    {X E ι ν μ : Type*} [TopologicalSpace X] [T2Space X] [Finite ν] [Finite μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {Q Q' F : Set X}
    (hQ : IsCompact Q) (hQPL : PLDomain e Q)
    (hQ' : IsCompact Q') (hQ'PL : PLDomain e Q') (hQQ' : Q ⊆ Q') (hF : IsClosed F)
    (B : ν → Set X) (sB : ∀ i, ChartwisePLSphere e (B i))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hFB : Disjoint F (⋃ i, B i)) (hfront : frontier Q = F ∪ ⋃ i, B i)
    (B' : μ → Set X) (sB' : ∀ i, ChartwisePLSphere e (B' i))
    (hFB' : Disjoint F (⋃ i, B' i)) (hfront' : frontier Q' = F ∪ ⋃ i, B' i)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ Q', f x ∈ L.space ∧ g (f x) = x)
    {x y : X} (hx : x ∈ Q') (hy : y ∈ Q)
    (hyC : y ∈ connectedComponentIn Q' x)
    (hm : HasPuncturedSphereModel e f (connectedComponentIn Q' x)) :
    HasPuncturedSphereModel e f (connectedComponentIn Q y) := by
  classical
  let D := connectedComponentIn Q y
  let C := connectedComponentIn Q' x
  have hDc : IsCompact D := isCompact_connectedComponentIn_of_mem hQ hy
  have hCc : IsCompact C := isCompact_connectedComponentIn_of_mem hQ' hx
  have hDPL : PLDomain e D := hQPL.connectedComponentIn hQ hy
  have hDconn : IsConnected D := isConnected_connectedComponentIn_iff.mpr hy
  have hDC : D ⊆ C := by
    have hh := connectedComponentIn_mono y hQQ'
    rwa [←connectedComponentIn_eq hyC] at hh
  have hDf : frontier D = D ∩ frontier Q := relative_component_frontier_eq hQ hQPL hy
  have hCf : frontier C = C ∩ frontier Q' := relative_component_frontier_eq hQ' hQ'PL hx
  have hFQ : F ⊆ Q := (subset_union_left.trans hfront.symm.subset).trans hQ.isClosed.frontier_subset
  have hBfront (j) : B j ⊆ frontier Q :=
    (subset_iUnion B j).trans (subset_union_right.trans hfront.symm.subset)
  obtain ⟨n,M,sM,hMC,hMdis,hMfront⟩ := hm.exists_boundary_spheres hCc.isClosed L g hg hgi
    (fun z hz => hreal z (connectedComponentIn_subset _ _ hz))
  have hMside (j) : M j ⊆ F ∨ M j ⊆ ⋃ i, B' i := by
    apply isPreconnected_iff_subset_of_disjoint_closed.mp (sM j).isConnected.isPreconnected
      F (⋃ i, B' i) hF (isClosed_iUnion_of_finite (fun i => (sB' i).isCompact.isClosed))
    · exact (subset_iUnion M j).trans (hMfront.symm.subset.trans
        (hCf.subset.trans (inter_subset_right.trans hfront'.subset)))
    · rw [hFB'.inter_eq,inter_empty]
  have hFM : D ∩ F = ⋃ j : {j : Fin n // M j ⊆ F ∧ M j ⊆ D}, M j.val := by
    apply Subset.antisymm
    · rintro z ⟨hzD,hzF⟩
      have hzfront : z ∈ frontier C := hCf.symm.subset
        ⟨hDC hzD,hfront'.symm.subset (Or.inl hzF)⟩
      obtain ⟨j,hj⟩ := mem_iUnion.mp (hMfront.subset hzfront)
      rcases hMside j with hMF | hMB
      · have hMD : M j ⊆ D := by
          have hh := (sM j).isConnected.isPreconnected.subset_connectedComponentIn hj
            (hMF.trans hFQ)
          rwa [←connectedComponentIn_eq hzD] at hh
        exact mem_iUnion.mpr ⟨⟨j,hMF,hMD⟩,hj⟩
      · exact (disjoint_left.mp hFB' hzF (hMB hj)).elim
    · intro z hz
      obtain ⟨j,hj⟩ := mem_iUnion.mp hz
      exact ⟨j.property.2 hj,j.property.1 hj⟩
  have hBwhole (j) : B j ⊆ D ∨ Disjoint (B j) D := by
    by_cases hh : (B j ∩ D).Nonempty
    · obtain ⟨z,hzB,hzD⟩ := hh
      left
      have hb := (sB j).isConnected.isPreconnected.subset_connectedComponentIn hzB
        ((hBfront j).trans hQ.isClosed.frontier_subset)
      rwa [←connectedComponentIn_eq hzD] at hb
    · right
      exact disjoint_left.mpr (fun _ hzB hzD => hh ⟨_,hzB,hzD⟩)
  let labels : {j : Fin n // M j ⊆ F ∧ M j ⊆ D} ⊕ {j : ν // B j ⊆ D} → Set X :=
    Sum.elim (fun j => M j.val) (fun j => B j.val)
  have slabels : ∀ j, ChartwisePLSphere e (labels j) :=
    Sum.rec (fun j => sM j.val) (fun j => sB j.val)
  have hlabelsdis : Pairwise fun j k => Disjoint (labels j) (labels k) := by
    intro j k hjk
    cases j with
    | inl j =>
      cases k with
      | inl k => exact hMdis (Subtype.val_injective.ne (by simpa using hjk))
      | inr k => exact hFB.mono j.property.1 (subset_iUnion B k.val)
    | inr j =>
      cases k with
      | inl k => exact (hFB.mono k.property.1 (subset_iUnion B j.val)).symm
      | inr k => exact hBdis (Subtype.val_injective.ne (by simpa using hjk))
  have hlabelsfront : frontier D = ⋃ j, labels j := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨hzD,hzQ⟩ := hDf.subset hz
      rcases hfront.subset hzQ with hzF | hzB
      · obtain ⟨j,hj⟩ := mem_iUnion.mp (hFM.subset ⟨hzD,hzF⟩)
        exact mem_iUnion.mpr ⟨Sum.inl j,hj⟩
      · obtain ⟨j,hj⟩ := mem_iUnion.mp hzB
        rcases hBwhole j with hh | hh
        · exact mem_iUnion.mpr ⟨Sum.inr ⟨j,hh⟩,hj⟩
        · exact (disjoint_left.mp hh hj hzD).elim
    · intro z hz
      obtain ⟨j,hj⟩ := mem_iUnion.mp hz
      apply hDf.symm.subset
      cases j with
      | inl j =>
        have hh := hFM.symm.subset (mem_iUnion.mpr ⟨j,hj⟩)
        exact ⟨hh.1,hfront.symm.subset (Or.inl hh.2)⟩
      | inr j => exact ⟨j.property hj,hBfront j.val hj⟩
  exact hm.of_connected_spherical_subregion hDc hDPL hDconn hDC labels slabels hlabelsdis hlabelsfront

theorem HasNoPuncturedSphereComponents.union_relative_connected_attachment
    {X E ι ν μ : Type*} [TopologicalSpace X] [T2Space X] [Finite ν] [Finite μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {Q D F : Set X}
    (hQ : IsCompact Q) (hQPL : PLDomain e Q)
    (hQD : IsCompact (Q ∪ D)) (hQDPL : PLDomain e (Q ∪ D)) (hF : IsClosed F)
    (B : ν → Set X) (sB : ∀ i, ChartwisePLSphere e (B i))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hFB : Disjoint F (⋃ i, B i)) (hfront : frontier Q = F ∪ ⋃ i, B i)
    (B' : μ → Set X) (sB' : ∀ i, ChartwisePLSphere e (B' i))
    (hFB' : Disjoint F (⋃ i, B' i)) (hfront' : frontier (Q ∪ D) = F ∪ ⋃ i, B' i)
    (hD : IsPreconnected D) (hcontact : (Q ∩ D).Nonempty)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ Q ∪ D, f x ∈ L.space ∧ g (f x) = x)
    (hno : HasNoPuncturedSphereComponents e f Q) :
    HasNoPuncturedSphereComponents e f (Q ∪ D) := by
  intro x hx hm
  obtain ⟨y,hy,hynew⟩ : ∃ y ∈ Q, y ∈ connectedComponentIn (Q ∪ D) x := by
    rcases hx with hxQ | hxD
    · exact ⟨x,hxQ,mem_connectedComponentIn (Or.inl hxQ)⟩
    · obtain ⟨y,hyQ,hyD⟩ := hcontact
      exact ⟨y,hyQ,hD.subset_connectedComponentIn hxD subset_union_right hyD⟩
  exact hno y hy (hm.of_original_relative_cut_component hQ hQPL hQD hQDPL subset_union_left hF
    B sB hBdis hFB hfront B' sB' hFB' hfront' L g hg hgi hreal hx hy hynew)

end PoincareConjecture.M76
