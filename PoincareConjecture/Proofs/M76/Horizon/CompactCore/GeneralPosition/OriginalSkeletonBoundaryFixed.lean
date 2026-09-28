import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.OriginalSkeletonFrontierCrossings
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.PlanarBoundaryEdges
import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceMaps









set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex unitInterval

namespace PoincareConjecture.M76

theorem original_skeleton_fixes_boundary
    {E X V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hdim : Module.finrank ℝ E = 2)
    (hcv : Convex ℝ K.space) (hne : (interior K.space).Nonempty)
    (a b : {s : K.faces // s.val.card = 2} → K.vertices)
    (hpair : ∀ k, ({(a k : E), (b k : E)} : Finset E) = k.val.val)
    (T : SimplicialComplex ℝ E) (hTS : T.space = ⋃ k, segment ℝ (a k : E) (b k : E))
    (G : C(I × T.space, X)) (f : E → X) (p : K.vertices → C(I, X))
    (F : Set X) (hboundary : ∀ x ∈ frontier K.space, f x ∉ F)
    (hpfix : ∀ w : K.vertices, f w ∉ F → ∀ t, p w t = f w)
    (B : K.vertices → OpenPartialHomeomorph X V)
    (hsource : ∀ w : K.vertices, MapsTo f (K.closedStar w).space (B w).source)
    (hcoord : ∀ w : K.vertices, (K.closedStar w).AffineOnFaces (B w ∘ f))
    (hformula : ∀ k (t r : I)
      (hx : AffineMap.lineMap (a k : E) (b k : E) (r : ℝ) ∈ T.space),
      G (t, ⟨AffineMap.lineMap (a k : E) (b k : E) (r : ℝ), hx⟩) ∈ (B (a k)).source ∧
      B (a k) (G (t, ⟨AffineMap.lineMap (a k : E) (b k : E) (r : ℝ), hx⟩)) =
        AffineMap.lineMap (B (a k) (p (a k) t)) (B (a k) (p (b k) t)) (r : ℝ))
    (hend : ∀ k (t : I) (ha : (a k : E) ∈ T.space) (hb : (b k : E) ∈ T.space),
      G (t, ⟨a k, ha⟩) = p (a k) t ∧ G (t, ⟨b k, hb⟩) = p (b k) t) :
    ∀ (t : I) (x : T.space), (x : E) ∈ frontier K.space → G (t, x) = f x := by
  classical
  have hedgeT (k : {s : K.faces // s.val.card = 2}) :
      segment ℝ (a k : E) (b k : E) ⊆ T.space :=
    fun _ hx => hTS.symm.subset (mem_iUnion.mpr ⟨k, hx⟩)
  have hvertex (t : I) (x : T.space) (hxv : (x : E) ∈ K.vertices) (hxF : f x ∉ F) :
      G (t, x) = f x := by
    obtain ⟨s, hs, hxs, hc⟩ := K.exists_full_coface_of_convex_space hK hcv hne hxv
    have hx : (x : E) ∈ s := hxs (Finset.mem_singleton_self _)
    have herase : (s.erase (x : E)).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hx, hc, hdim]
      decide
    obtain ⟨w, hw⟩ := herase
    have he : {(x : E), w} ∈ K.faces := K.down_closed hs
      (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hx, (Finset.mem_erase.mp hw).2⟩)
      (by simp)
    let k : {s : K.faces // s.val.card = 2} :=
      ⟨⟨{(x : E), w}, he⟩, Finset.card_pair (Finset.mem_erase.mp hw).1.symm⟩
    have hxm : (x : E) ∈ ({(a k : E), (b k : E)} : Finset E) :=
      (hpair k).symm ▸ Finset.mem_insert_self (x : E) {w}
    have hh := hend k t (hedgeT k (left_mem_segment ℝ _ _)) (hedgeT k (right_mem_segment ℝ _ _))
    rcases Finset.mem_insert.mp hxm with hxa | hxb
    · have heqx : x = ⟨a k, hedgeT k (left_mem_segment ℝ _ _)⟩ := Subtype.ext hxa
      rw [heqx, hh.1, hpfix (a k) (by simpa only [hxa] using hxF)]
    · have hxb := Finset.mem_singleton.mp hxb
      have heqx : x = ⟨b k, hedgeT k (right_mem_segment ℝ _ _)⟩ := Subtype.ext hxb
      rw [heqx, hh.2, hpfix (b k) (by simpa only [hxb] using hxF)]
  intro t x hx
  rcases K.frontier_point_vertex_or_boundary_edge hK hdim hcv hne hx with hxv | ⟨u, v, huv, he, hu, hv, hxseg⟩
  · exact hvertex t x hxv (hboundary x hx)
  let k : {s : K.faces // s.val.card = 2} := ⟨⟨{u, v}, he⟩, Finset.card_pair huv⟩
  have hends (w : E) (hw : w ∈ k.val.val) : w ∈ frontier K.space := by
    change w ∈ ({u, v} : Finset E) at hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hu
    · exact Finset.mem_singleton.mp hw ▸ hv
  have ha : (a k : E) ∈ k.val.val := hpair k ▸ Finset.mem_insert_self _ _
  have hb : (b k : E) ∈ k.val.val := hpair k ▸ (by simp)
  have hstar : k.val.val ∈ (K.closedStar (a k)).faces := by
    exact ⟨k.val.property, by simpa only [Finset.insert_eq_of_mem ha] using k.val.property⟩
  obtain ⟨A, hA⟩ := hcoord (a k) k.val.val hstar
  have hseg : convexHull ℝ (k.val.val : Set E) = segment ℝ (a k : E) (b k : E) := by
    rw [← hpair k, Finset.coe_pair, convexHull_pair]
  have hxedge : (x : E) ∈ segment ℝ (a k : E) (b k : E) := by
    rw [← hseg]
    simpa only [k, Finset.coe_pair, convexHull_pair] using openSegment_subset_segment ℝ u v hxseg
  obtain ⟨r, hr, hxr⟩ := (segment_eq_image_lineMap ℝ (a k : E) (b k : E)).subset hxedge
  let rI : I := ⟨r, hr⟩
  have hxT : AffineMap.lineMap (a k : E) (b k : E) r ∈ T.space := hxr.symm ▸ x.property
  have hG := hformula k t rI hxT
  have heqx : (⟨AffineMap.lineMap (a k : E) (b k : E) r, hxT⟩ : T.space) = x := Subtype.ext hxr
  rw [heqx] at hG
  apply (B (a k)).injOn hG.1 (hsource (a k) (convexHull_subset_space hstar (hseg.symm.subset hxedge)))
  rw [hG.2, hpfix (a k) (hboundary _ (hends _ ha)), hpfix (b k) (hboundary _ (hends _ hb))]
  have hAa := hA (subset_convexHull ℝ (k.val.val : Set E) ha)
  have hAb := hA (subset_convexHull ℝ (k.val.val : Set E) hb)
  have hAx := hA (hseg.symm.subset hxedge)
  change B (a k) (f x) = A x at hAx
  change B (a k) (f (a k)) = A (a k) at hAa
  change B (a k) (f (b k)) = A (b k) at hAb
  rw [hAa, hAb, hAx]
  exact (A.toAffineMap.apply_lineMap (a k : E) (b k : E) r).symm.trans (congrArg A hxr)

end PoincareConjecture.M76
