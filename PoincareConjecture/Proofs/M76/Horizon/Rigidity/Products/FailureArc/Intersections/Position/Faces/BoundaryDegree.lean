import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalTriangleBoundaryDegree
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Contacts.Endpoints

set_option autoImplicit false
open Set Geometry Filter
open scoped Topology

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem ncard_surface_triangle_boundary_neighborSet_eq_one
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (hAtlas : ∀ y ∈ S, ∃ i, y ∈ (e i).source) (K : SimplicialComplex ℝ E) (g : E → X)
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
  have hdegree := (hcofaces a ha has ha2).ncard_surface_contact_neighborSet_eq_one_of_affine_chart
      hAtlas hs hs3 has ha2
      hgi hSV ⟨hyS, hyedge⟩ Q hQ A hmap hA G hG hmarked
      (by simpa only [Q.right_inv hwQ] using hlocal)
  simpa only [Q.right_inv hwQ] using hdegree

end PoincareConjecture.M76
