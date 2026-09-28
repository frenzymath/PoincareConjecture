import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.OriginalContactEndpoint
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.PlanePairSignTransport
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier










set_option autoImplicit false

open Set Geometry Filter
open scoped Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)




theorem exists_original_subedge_of_mem_triangle_intrinsicFrontier
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {w : V3} (hw : w ∈ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))) :
    ∃ a : Finset E, a ∈ K.faces ∧ a ⊆ s ∧ a.card = 2 ∧
      w ∈ (Q ∘ g) '' convexHull ℝ (a : Set E) ∧ w ∈ Q.target ∧
      Q.symm w ∈ g '' convexHull ℝ (a : Set E) := by
  classical
  have hclosed : IsClosed (convexHull ℝ (A '' (s : Set E))) :=
    ((s.finite_toSet.image A).isCompact_convexHull ℝ).isClosed
  rw [← closure_sdiff_intrinsicInterior, hclosed.closure_eq] at hw
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro x hx y hy hxy
    exact hgi (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hy)
      (Q.injOn (hmap hx) (hmap hy) ((hA hx).trans (hxy.trans (hA hy).symm)))
  have hAsp := A.toAffineMap.injOn_affineSpan_of_injOn_convex
    (convex_convexHull ℝ _) (K.nonempty_of_mem_faces hs).to_set.convexHull hAi
  have himage : A '' convexHull ℝ (s : Set E) = convexHull ℝ (A '' (s : Set E)) :=
    A.toAffineMap.image_convexHull _
  obtain ⟨u, hu, huw⟩ := himage.symm.subset hw.1
  have huint : u ∉ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
    intro hui
    apply hw.2
    have hh : w ∈ A.toAffineMap '' intrinsicInterior ℝ (convexHull ℝ (s : Set E)) :=
      ⟨u, hui, huw⟩
    rw [← A.toAffineMap.intrinsicInterior_image_of_injOn_span _ hAsp] at hh
    change w ∈ intrinsicInterior ℝ (A '' convexHull ℝ (s : Set E)) at hh
    rwa [himage] at hh
  have hufront : u ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
    rw [← closure_sdiff_intrinsicInterior]
    exact ⟨subset_closure hu, huint⟩
  obtain ⟨i, hi, hui⟩ := (AffineIndependent.mem_intrinsicFrontier_convexHull_finset
    (K.nonempty_of_mem_faces hs) (K.indep hs) u).mp hufront
  have hi2 : (s.erase i).card = 2 := by rw [Finset.card_erase_of_mem hi, hs3]
  have hiK : s.erase i ∈ K.faces := K.down_closed hs (Finset.erase_subset _ _)
    (Finset.card_pos.mp (by omega))
  have hQgu : Q (g u) = w := (hA hu).trans huw
  have hgu : g u = Q.symm w := (Q.left_inv (hmap hu)).symm.trans (congrArg Q.symm hQgu)
  exact ⟨s.erase i, hiK, Finset.erase_subset _ _, hi2, ⟨u, hui, hQgu⟩,
    hQgu ▸ Q.map_source (hmap hu), u, hui, hgu⟩





theorem ChartwisePLSphere.ncard_triangle_boundary_neighborSet_eq_one
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (sS : ChartwisePLSphere e S) (K : SimplicialComplex ℝ E) (g : E → X)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (hcofaces : ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      HasOriginalEdgeCofaceCharts e S K g a)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite)
    (hGQ : G.space ⊆ Q.target)
    (hGt : G.space ⊆ convexHull ℝ (A '' (s : Set E)))
    (Phi : X ≃ₜ X) {W : Set X} (hW : IsOpen W)
    (hedgeW : ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      g '' convexHull ℝ (a : Set E) ⊆ W)
    (hagree : Phi '' S ∩ W = S ∩ W)
    (hphysical : Q.symm '' G.space = Phi '' S ∩ (g '' convexHull ℝ (s : Set E))) :
    ∀ w : G.vertices,
      (w : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet w).ncard = 1 := by
  classical
  have himage : A '' convexHull ℝ (s : Set E) = convexHull ℝ (A '' (s : Set E)) :=
    A.toAffineMap.image_convexHull _
  intro w hw
  have hwG : (w : V3) ∈ G.space := G.vertices_subset_space w.property
  have hwQ : (w : V3) ∈ Q.target := hGQ hwG
  have hwfront : (w : V3) ∈ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) := by
    rw [← closure_sdiff_intrinsicInterior]
    exact ⟨subset_closure (hGt hwG), hw⟩
  obtain ⟨a, ha, has, ha2, _, _, hyedge⟩ :=
    exists_original_subedge_of_mem_triangle_intrinsicFrontier K g hgi hs hs3 Q A hmap hA hwfront
  have hyW : Q.symm w ∈ W := hedgeW a ha has ha2 hyedge
  have hyPhi : Q.symm w ∈ Phi '' S := (hphysical.subset ⟨w, hwG, rfl⟩).1
  have hyS : Q.symm w ∈ S := (hagree.subset ⟨hyPhi, hyW⟩).1
  have hlocal : ∀ᶠ x in 𝓝 (w : V3), x ∈ G.space ↔
      x ∈ Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' (s : Set E)) := by
    have hU : IsOpen (Q.target ∩ Q.symm ⁻¹' W) := Q.symm.isOpen_inter_preimage hW
    filter_upwards [hU.mem_nhds ⟨hwQ, hyW⟩] with x hxU
    constructor
    · intro hxG
      have hxPhi : Q.symm x ∈ Phi '' S := (hphysical.subset ⟨x, hxG, rfl⟩).1
      have hxS : Q.symm x ∈ S := (hagree.subset ⟨hxPhi, hxU.2⟩).1
      exact ⟨⟨Q.symm x, ⟨hxS, Q.map_target hxU.1⟩, Q.right_inv hxU.1⟩, hGt hxG⟩
    · rintro ⟨⟨y, ⟨hyS, hyQ⟩, hyx⟩, hxt⟩
      have hxS : Q.symm x ∈ S := by rw [← hyx, Q.left_inv hyQ]; exact hyS
      have hxPhi : Q.symm x ∈ Phi '' S := (hagree.symm.subset ⟨hxS, hxU.2⟩).1
      obtain ⟨v, hv, hvx⟩ := himage.symm.subset hxt
      have hQgv : Q (g v) = x := (hA hv).trans hvx
      have hgv : g v = Q.symm x := (Q.left_inv (hmap hv)).symm.trans (congrArg Q.symm hQgv)
      obtain ⟨z, hzG, hzx⟩ := hphysical.symm.subset ⟨hxPhi, v, hv, hgv⟩
      exact Q.symm.injOn (hGQ hzG) hxU.1 hzx ▸ hzG
  have hmarked : Q (Q.symm w) ∈ G.vertices := by rw [Q.right_inv hwQ]; exact w.property
  have hdegree := (hcofaces a ha has ha2).ncard_contact_neighborSet_eq_one_of_affine_chart
      sS hs hs3 has ha2
      hgi hSV ⟨hyS, hyedge⟩ Q hQ A hmap hA G hG hmarked
      (by simpa only [Q.right_inv hwQ] using hlocal)
  simpa only [Q.right_inv hwQ] using hdegree




theorem finite_original_triangle_graph_boundary
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3) (S : Set X)
    (hedges : ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      (S ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V3) (Phi : X ≃ₜ X) {W : Set X}
    (hedgeW : ∀ a ∈ K.faces, a ⊆ s → a.card = 2 →
      g '' convexHull ℝ (a : Set E) ⊆ W)
    (hagree : Phi '' S ∩ W = S ∩ W)
    (hphysical : Q.symm '' G.space = Phi '' S ∩ (g '' convexHull ℝ (s : Set E))) :
    (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite := by
  classical
  let F := s.powerset.filter (fun a => a ∈ K.faces ∧ a.card = 2)
  have hfinite : (⋃ a ∈ F, Q '' (S ∩ (g '' convexHull ℝ (a : Set E)))).Finite := by
    apply F.finite_toSet.biUnion
    intro a ha
    obtain ⟨haF, haK, ha2⟩ := Finset.mem_filter.mp ha
    exact (hedges a haK (Finset.mem_powerset.mp haF) ha2).image Q
  apply hfinite.subset
  rintro x ⟨hxG, hxfront⟩
  obtain ⟨a, ha, has, ha2, _, hxQ, hyedge⟩ :=
    exists_original_subedge_of_mem_triangle_intrinsicFrontier K g hgi hs hs3 Q A hmap hA hxfront
  have hyW : Q.symm x ∈ W := hedgeW a ha has ha2 hyedge
  have hyPhi : Q.symm x ∈ Phi '' S := (hphysical.subset ⟨x, hxG, rfl⟩).1
  have hyS : Q.symm x ∈ S := (hagree.subset ⟨hyPhi, hyW⟩).1
  exact mem_iUnion₂.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr has, ha, ha2⟩,
    Q.symm x, ⟨hyS, hyedge⟩, Q.right_inv hxQ⟩

end PoincareConjecture.M76
