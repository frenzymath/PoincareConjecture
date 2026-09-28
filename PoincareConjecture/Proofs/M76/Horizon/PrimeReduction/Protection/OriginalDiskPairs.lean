import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalDiskRimModels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.ProductSurfaceLinks
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.FiniteSimplyConnectedDisk
import PoincareConjecture.Proofs.M76.Mathlib.SinglePolygonPresentation
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.RefinementEdgeStars

set_option autoImplicit false
noncomputable section
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

open Classical in
theorem HamiltonMarkedProtectedBall.exists_original_disk_pairs
    {ι κ α E : Type*} [Fintype ι] [Unique ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hdim : Fintype.card κ = 2)
    (F : LatticeHandleAmbient ι κ L → E) (hF : Continuous F)
    (hfi : InjOn F (latticeHandleDomain ι κ L))
    (J B : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hBJ : B ≤ J)
    (hBdim : ∀ t ∈ B.faces, t.card ≤ 2)
    (hpure : ∀ t ∈ J.faces, ∃ u ∈ J.faces, u.card = 3 ∧ t ⊆ u)
    (hcofaces : ∀ t ∈ J.faces, t.card = 2 →
      {u : Finset E | u ∈ J.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard =
        if t ∈ B.faces then 1 else 2)
    (hJmark : J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2))
    (hBmark : B.space = F '' (hamiltonMarkedProjection ι κ L ''
      (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2)))) :
    ∃ d r : Bool → Set E,
      (∀ side, IsFinitePLBallPair (ℝ × ℝ) (d side) (r side) ∧
        d side = F '' (hamiltonMarkedProjection ι κ L ''
          ({fun _ : ι => if side then (1 : ℝ) else -1} ×ˢ
            closedBall (0 : κ → ℝ) (3 / 2))) ∧
        r side = F '' (hamiltonMarkedProjection ι κ L ''
          ({fun _ : ι => if side then (1 : ℝ) else -1} ×ˢ
            sphere (0 : κ → ℝ) (3 / 2)))) ∧
      Disjoint (d false) (d true) ∧ d false ∪ d true = J.space := by
  classical
  obtain ⟨P, hP⟩ := b.exists_marked_image_homeomorph (by simp) F hF hfi
    (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2))
    ((isCompact_sphere _ _).prod (isCompact_closedBall _ _)) subset_rfl J.space hJmark
  obtain ⟨A, H, hA, hH, hdis, hcover, hretain, _⟩ :=
    exists_marked_disk_component_models J hJ P
  obtain ⟨C, gamma, hC, hfaces⟩ := b.exists_original_disk_rim_models hdim F hF hfi
    J B (hJ.subset hBJ) hBdim hJmark hBmark
  have hval (side) (x : closedBall (0 : κ → ℝ) (3 / 2)) :
      (H side x : E) = F (hamiltonMarkedProjection ι κ L
        ((markedDiskSignCoordinates (ι := ι) side : ι → ℝ), (x : κ → ℝ))) :=
    (hH side x).trans (hP _)
  have hAm (side) : (A side).space = F '' (hamiltonMarkedProjection ι κ L ''
      ({fun _ : ι => if side then (1 : ℝ) else -1} ×ˢ
        closedBall (0 : κ → ℝ) (3 / 2))) := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨x, hx⟩ := (H side).surjective ⟨z, hz⟩
      refine ⟨_, ⟨((markedDiskSignCoordinates (ι := ι) side : ι → ℝ), (x : κ → ℝ)),
        ⟨markedDiskSignCoordinates_apply side, x.property⟩, rfl⟩, ?_⟩
      exact (hval side x).symm.trans (congrArg Subtype.val hx)
    · rintro z ⟨_, ⟨x, ⟨hx, hxball⟩, rfl⟩, rfl⟩
      have hh : (H side ⟨x.2, hxball⟩ : E) = F (hamiltonMarkedProjection ι κ L x) := by
        rw [hval]
        apply congrArg (F ∘ hamiltonMarkedProjection ι κ L)
        exact Prod.ext ((markedDiskSignCoordinates_apply (ι := ι) side).trans hx.symm) rfl
      exact hh ▸ (H side ⟨x.2, hxball⟩).property
  have hCA (side) : C side ≤ A side := by
    apply J.le_of_common_subcomplex_space_subset _ _ ((hC side).1.trans hBJ) (hA side).2.1
    rw [(hC side).2.2.2, hAm side]
    exact image_mono (image_mono (prod_mono subset_rfl sphere_subset_closedBall))
  have hdisAll : Pairwise fun i j => Disjoint (A i).space (A j).space := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hdis
    · exact hdis.symm
    · exact (hij rfl).elim
  have hboundary (side) (t : Finset E) (ht : t ∈ (A side).faces) :
      t ∈ B.faces ↔ t ∈ (C side).faces := by
    constructor
    · intro htB
      obtain ⟨other, ho⟩ := (hfaces t).mp htB
      by_cases heq : other = side
      · exact heq ▸ ho
      · obtain ⟨v, hv⟩ := (A side).nonempty_of_mem_faces ht
        exact (disjoint_left.mp (hdisAll heq)
          (SimplicialComplex.subset_space (hCA other ho) hv)
          (SimplicialComplex.subset_space ht hv)).elim
    · exact fun htC => (hC side).1 htC
  have hcounts (side) (t : Finset E) (ht : t ∈ (A side).faces) (htc : t.card = 2) :
      {u : Finset E | u ∈ (A side).faces ∧ u.card = 3 ∧ t ⊆ u}.ncard =
        if t ∈ (C side).faces then 1 else 2 := by
    have heq : {u : Finset E | u ∈ (A side).faces ∧ u.card = 3 ∧ t ⊆ u} =
        {u : Finset E | u ∈ J.faces ∧ u.card = 3 ∧ t ⊆ u} := by
      ext u
      exact ⟨fun h => ⟨(hA side).2.1 h.1, h.2⟩,
        fun h => ⟨hretain side t u ht h.1 h.2.2, h.2⟩⟩
    rw [heq, hcofaces t ((hA side).2.1 ht) htc, hboundary side t ht]
  refine ⟨fun side => (A side).space, fun side => (C side).space, ?_, hdis, hcover⟩
  intro side
  refine ⟨?_, hAm side, (hC side).2.2.2⟩
  let : ContractibleSpace (A side).space := (hA side).2.2
  have hlinks := connected_links_of_closed_ball_two (A side) (hA side).1
    hdim (by norm_num : (0 : ℝ) < 3 / 2) (H side)
  obtain ⟨g⟩ := exists_unit_sphere_circle_homeomorph (by simp : Fintype.card (Fin 2) = 2)
  obtain ⟨n, Q, hQi, hQ, hQs⟩ := (C side).exists_polygon_of_homeomorph_circle
    (hC side).2.1 (fun t ht => hBdim t ((hC side).1 ht)) ((gamma side).symm.trans g)
  have hpoly : HasDisjointPolygonPresentation (C side).space :=
    hQs ▸ Q.hasDisjointPolygonPresentation hQi hQ
  have hinc := Dehn.Annuli.circle_incidence (C side) (hC side).2.1
    (gamma side) (hC side).2.2.1
  apply isFinitePLBallPair_of_simplyConnected_marked_surface (A side) (C side)
    (hA side).1 (hCA side) _ hlinks (hcounts side) hpoly hinc.2.2.1.nonempty
  intro t ht
  obtain ⟨u, hu, huc, htu⟩ := hpure t ((hA side).2.1 ht)
  exact ⟨u, hretain side t u ht hu htu, huc, htu⟩

end PoincareConjecture.M76
