import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RawSphereCutComponents
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphericalSubregionModels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModelBoundary
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

private theorem component_frontier_eq
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X}
    (hQ : IsCompact Q) (hPL : PLDomain e Q) {x : X} (hx : x ∈ Q) :
    frontier (connectedComponentIn Q x) = connectedComponentIn Q x ∩ frontier Q := by
  let : LocallyPathConnectedSpace Q := hPL.locallyPathConnectedSpace
  obtain ⟨U,hU,hCU⟩ := exists_open_inter_of_relative_open (connectedComponentIn_subset Q x)
    (isOpen_preimage_connectedComponentIn hx)
  exact frontier_eq_inter_of_eq_inter_open hQ.isClosed
    (isCompact_connectedComponentIn_of_mem hQ hx).isClosed hU hCU

theorem HasNoPuncturedSphereComponents.mono_original_collar_cut_relative_boundary
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    (R : Set X) (hR : IsClosed R)
    (Q : Bool → Set X) (O : Bool → κ → Set X) (S : κ → Set X)
    (W : ∀ b i, (S i × unitInterval) ≃ₜ closure (O b i))
    (hQ : ∀ b, Q b = R \ ⋃ i, O b i)
    (hcQ : ∀ b, IsCompact (Q b)) (hPL : ∀ b, PLDomain e (Q b))
    (hinside : ∀ b i, closure (O b i) ⊆ interior R)
    (hdis : ∀ b, Pairwise fun i j => Disjoint (closure (O b i)) (closure (O b j)))
    (hO : ∀ b i z, (W b i z : X) ∈ O b i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hS : ∀ b i z, (W b i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hSC : ∀ b i, S i ⊆ closure (O b i))
    (B : Bool → κ × Bool → Set X) (sB : ∀ b i, ChartwisePLSphere e (B b i))
    (hBdis : ∀ b, Pairwise fun i j => Disjoint (B b i) (B b j))
    (hBsub : ∀ b i, B b i ⊆ closure (O b i.1))
    (hfront : ∀ b, frontier (Q b) = frontier R ∪ ⋃ i, B b i)
    (hnest : Q false ⊆ Q true)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x)
    (hno : HasNoPuncturedSphereComponents e f (Q false)) :
    HasNoPuncturedSphereComponents e f (Q true) := by
  classical
  have hCR (b i) : closure (O b i) ⊆ R := (hinside b i).trans interior_subset
  have hfrontQ (b) : frontier R ⊆ Q b := by
    intro x hx
    apply (hQ b).symm.subset
    refine ⟨hR.frontier_subset hx,?_⟩
    intro ho
    obtain ⟨i,hi⟩ := mem_iUnion.mp ho
    exact hx.2 (hinside b i (subset_closure hi))
  have hBfront (b i) : B b i ⊆ frontier (Q b) :=
    (subset_iUnion (B b) i).trans (subset_union_right.trans (hfront b).symm.subset)
  have hBF (b) : Disjoint (frontier R) (⋃ i, B b i) := by
    apply disjoint_left.mpr
    intro x hx hb
    obtain ⟨i,hi⟩ := mem_iUnion.mp hb
    exact hx.2 (hinside b i.1 (hBsub b i hi))
  obtain ⟨r,_,hrQ,_,hrcc,hcomp0,_⟩ := exists_raw_sphere_cut_component_map
    R (Q false) (O false) S (W false) (hQ false) (hcQ false).isClosed
    (hCR false) (hdis false) (hO false) (hS false) (hSC false)
  obtain ⟨_,_,_,_,_,hcomp1,_⟩ := exists_raw_sphere_cut_component_map
    R (Q true) (O true) S (W true) (hQ true) (hcQ true).isClosed
    (hCR true) (hdis true) (hO true) (hS true) (hSC true)
  intro x hx hm
  have hxraw : x ∈ R \ ⋃ i, S i := by
    have hh := mem_connectedComponentIn hx
    rw [hcomp1 x hx] at hh
    exact connectedComponentIn_subset _ _ hh.1
  have hy := hrQ hxraw
  let D := connectedComponentIn (Q false) (r x)
  let C := connectedComponentIn (Q true) x
  have hDcompact : IsCompact D := isCompact_connectedComponentIn_of_mem (hcQ false) hy
  have hCcompact : IsCompact C := isCompact_connectedComponentIn_of_mem (hcQ true) hx
  have hDPL : PLDomain e D := (hPL false).connectedComponentIn (hcQ false) hy
  have hDconn : IsConnected D := isConnected_connectedComponentIn_iff.mpr hy
  have hynew : r x ∈ C := by
    change r x ∈ connectedComponentIn (Q true) x
    rw [hcomp1 x hx]
    exact ⟨hrcc x hxraw,hnest hy⟩
  have hDC : D ⊆ C := by
    have hh := connectedComponentIn_mono (r x) hnest
    rwa [←connectedComponentIn_eq hynew] at hh
  have hDF : frontier D = D ∩ frontier (Q false) :=
    component_frontier_eq (hcQ false) (hPL false) hy
  have hCF : frontier C = C ∩ frontier (Q true) :=
    component_frontier_eq (hcQ true) (hPL true) hx
  have hsame : D ∩ frontier R = C ∩ frontier R := by
    ext z
    constructor
    · exact fun hz => ⟨hDC hz.1,hz.2⟩
    · rintro ⟨hzC,hzF⟩
      refine ⟨?_,hzF⟩
      change z ∈ connectedComponentIn (Q false) (r x)
      rw [hcomp0 (r x) hy,←connectedComponentIn_eq (hrcc x hxraw)]
      exact ⟨((hcomp1 x hx).subset hzC).1,hfrontQ false hzF⟩
  obtain ⟨n,M,sM,hMC,hMdis,hMfront⟩ := hm.exists_boundary_spheres hCcompact.isClosed L g hg hgi
    (fun z hz => hreal z ((hQ true).subset (connectedComponentIn_subset _ _ hz)).1)
  have hMside (j) : M j ⊆ frontier R ∨ M j ⊆ ⋃ i, B true i := by
    apply isPreconnected_iff_subset_of_disjoint_closed.mp (sM j).isConnected.isPreconnected
      (frontier R) (⋃ i, B true i) isClosed_frontier
      (isClosed_iUnion_of_finite (fun i => (sB true i).isCompact.isClosed))
    · exact (subset_iUnion M j).trans (hMfront.symm.subset.trans
        (hCF.subset.trans (inter_subset_right.trans (hfront true).subset)))
    · rw [(hBF true).inter_eq,inter_empty]
  have hFM : D ∩ frontier R = ⋃ j : {j : Fin n // M j ⊆ frontier R}, M j.val := by
    rw [hsame]
    apply Subset.antisymm
    · rintro z ⟨hzC,hzF⟩
      have hzfront : z ∈ frontier C := hCF.symm.subset
        ⟨hzC,(hfront true).symm.subset (Or.inl hzF)⟩
      obtain ⟨j,hj⟩ := mem_iUnion.mp (hMfront.subset hzfront)
      rcases hMside j with h | h
      · exact mem_iUnion.mpr ⟨⟨j,h⟩,hj⟩
      · exact (disjoint_left.mp (hBF true) hzF (h hj)).elim
    · intro z hz
      obtain ⟨j,hj⟩ := mem_iUnion.mp hz
      exact ⟨hMC j.val hj,j.property hj⟩
  have hBwhole (j) : B false j ⊆ D ∨ Disjoint (B false j) D := by
    by_cases hh : (B false j ∩ D).Nonempty
    · obtain ⟨z,hzB,hzD⟩ := hh
      left
      have hb := (sB false j).isConnected.isPreconnected.subset_connectedComponentIn hzB
        ((hBfront false j).trans (hPL false).closed.frontier_subset)
      rwa [←connectedComponentIn_eq hzD] at hb
    · right
      exact disjoint_left.mpr (fun _ hzB hzD => hh ⟨_,hzB,hzD⟩)
  let labels : {j : Fin n // M j ⊆ frontier R} ⊕
      {j : κ × Bool // B false j ⊆ D} → Set X :=
    Sum.elim (fun j => M j.val) (fun j => B false j.val)
  have slabels : ∀ j, ChartwisePLSphere e (labels j) :=
    Sum.rec (fun j => sM j.val) (fun j => sB false j.val)
  have hlabelsdis : Pairwise fun j k => Disjoint (labels j) (labels k) := by
    intro j k hjk
    cases j with
    | inl j =>
      cases k with
      | inl k => exact hMdis (Subtype.val_injective.ne (by simpa using hjk))
      | inr k => exact (hBF false).mono j.property (subset_iUnion (B false) k.val)
    | inr j =>
      cases k with
      | inl k => exact ((hBF false).mono k.property (subset_iUnion (B false) j.val)).symm
      | inr k => exact hBdis false (Subtype.val_injective.ne (by simpa using hjk))
  have hlabelsfront : frontier D = ⋃ j, labels j := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨hzD,hzQ⟩ := hDF.subset hz
      rcases (hfront false).subset hzQ with hzF | hzB
      · obtain ⟨j,hj⟩ := mem_iUnion.mp (hFM.subset ⟨hzD,hzF⟩)
        exact mem_iUnion.mpr ⟨Sum.inl j,hj⟩
      · obtain ⟨j,hj⟩ := mem_iUnion.mp hzB
        rcases hBwhole j with hh | hh
        · exact mem_iUnion.mpr ⟨Sum.inr ⟨j,hh⟩,hj⟩
        · exact (disjoint_left.mp hh hj hzD).elim
    · intro z hz
      obtain ⟨j,hj⟩ := mem_iUnion.mp hz
      apply hDF.symm.subset
      cases j with
      | inl j =>
        have hh := hFM.symm.subset (mem_iUnion.mpr ⟨j,hj⟩)
        exact ⟨hh.1,(hfront false).symm.subset (Or.inl hh.2)⟩
      | inr j => exact ⟨j.property hj,hBfront false j.val hj⟩
  exact hno (r x) hy (hm.of_connected_spherical_subregion hDcompact hDPL hDconn hDC
    labels slabels hlabelsdis hlabelsfront)

end PoincareConjecture.M76
