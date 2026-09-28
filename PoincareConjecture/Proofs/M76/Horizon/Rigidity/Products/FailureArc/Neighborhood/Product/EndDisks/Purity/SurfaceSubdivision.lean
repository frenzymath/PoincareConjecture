import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.Purity.Subdivision
import PoincareConjecture.Proofs.M76.Mathlib.CenteredDerivedSurface
import PoincareConjecture.Proofs.M76.Mathlib.SurfaceLinkPolygon
import PoincareConjecture.Proofs.M76.Mathlib.PolygonClosedStarDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.LocalDiskEdgeCofaces
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.LocalDiskConnectedLink
import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates

set_option autoImplicit false
open Set Geometry Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [FiniteDimensional ℝ E] in
theorem isOpen_closedStar_sdiff_link_preimage
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (p : E) :
    IsOpen ((Subtype.val : K.space → E) ⁻¹'
      ((K.closedStar p).space \ (K.link p).space)) := by
  classical
  let T := hK.toFinset.filter (fun s => p ∉ s)
  let D := ⋃ s ∈ T, convexHull ℝ (s : Set E)
  have hD : IsClosed D :=
    (T.finite_toSet.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)).isClosed
  have heq : (Subtype.val : K.space → E) ⁻¹'
      ((K.closedStar p).space \ (K.link p).space) = Subtype.val ⁻¹' Dᶜ := by
    ext x
    constructor
    · intro hx hxD
      obtain ⟨s,hs,hxs⟩ := K.exists_face_intrinsicInterior_of_finite hK x.property
      obtain ⟨u,hu,hxu⟩ := mem_space_iff.mp hx.1
      have hsu := K.subset_of_mem_intrinsicInterior_face hs hu.1 hxs hxu
      have hps : p ∈ s := by
        by_contra hps
        apply hx.2
        exact (K.link p).convexHull_subset_space
          ⟨hs,hps,K.down_closed hu.2 (Finset.insert_subset_insert p hsu)
            (Finset.insert_nonempty p s)⟩ (intrinsicInterior_subset hxs)
      obtain ⟨v,hv,hxv⟩ := mem_iUnion₂.mp hxD
      obtain ⟨hvK,hpv⟩ := Finset.mem_filter.mp hv
      exact hpv (K.subset_of_mem_intrinsicInterior_face hs
        (hK.mem_toFinset.mp hvK) hxs hxv hps)
    · intro hx
      obtain ⟨s,hs,hxs⟩ := mem_space_iff.mp x.property
      have hps : p ∈ s := by
        by_contra hps
        exact hx (mem_iUnion₂.mpr ⟨s,Finset.mem_filter.mpr
          ⟨hK.mem_toFinset.mpr hs,hps⟩,hxs⟩)
      refine ⟨(K.closedStar p).convexHull_subset_space
        ⟨hs,by simpa only [Finset.insert_eq_of_mem hps] using hs⟩ hxs,?_⟩
      intro hlink
      obtain ⟨u,hu,hxu⟩ := mem_space_iff.mp hlink
      exact hx (mem_iUnion₂.mpr ⟨u,Finset.mem_filter.mpr
        ⟨hK.mem_toFinset.mpr hu.1,hu.2.1⟩,hxu⟩)
  rw [heq]
  exact hD.isOpen_compl.preimage continuous_subtype_val

theorem exists_local_disk_of_closed_surface_incidence
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    {p : E} (hp : p ∈ K.space) :
    ∃ d q : Set E, IsFinitePLBallPair (Fin 2 → ℝ) d q ∧ d ⊆ K.space ∧
      p ∈ d \ q ∧ IsOpen ((Subtype.val : K.space → E) ⁻¹' (d \ q)) := by
  classical
  obtain ⟨M,hM,hMK,hpM,hpureM,hcofacesM,hlinkM⟩ :=
    K.exists_centered_derived_surface_at_carrier_point hK hpure hcofaces hlinks hp
  obtain ⟨n,P,hPi,hP,hPlink⟩ :=
    M.exists_surface_link_polygon hM hpureM hcofacesM p hlinkM
  have hd := (M.isFinitePLBallPair_closedStar_of_polygon_link hM hpM P hP hPi hPlink).model_equiv
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  have hpstar : p ∈ (M.closedStar p).space :=
    (M.closedStar p).vertices_subset_space ⟨hpM,by
      simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self p)] using
        (show {p} ∈ M.faces from hpM)⟩
  have hpnot : p ∉ (M.link p).space := by
    intro h
    obtain ⟨s,hs,hps⟩ := mem_space_iff.mp h
    exact hs.2.1 ((M.vertex_mem_convexHull_iff hpM hs.1).mp hps)
  refine ⟨(M.closedStar p).space,(M.link p).space,hd,?_,⟨hpstar,hpnot⟩,?_⟩
  · intro x hx
    obtain ⟨s,hs,hxs⟩ := mem_space_iff.mp hx
    exact hMK.subset (M.convexHull_subset_space hs.1 hxs)
  · exact (M.isOpen_closedStar_sdiff_link_preimage hM p).preimage
      (Homeomorph.setCongr hMK.symm).continuous

theorem closed_surface_incidence_of_finite_same_carrier
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hL : L.faces.Finite)
    (hspace : L.space = K.space)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space) :
    (∀ s ∈ L.faces, ∃ t ∈ L.faces, t.card = 3 ∧ s ⊆ t) ∧
    (∀ s ∈ L.faces, s.card = 2 →
      {t : Finset E | t ∈ L.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2) ∧
    (∀ p ∈ L.vertices, IsConnected (L.link p).space) := by
  classical
  have hpureL := K.pure_of_finite_same_carrier L hK hL hspace hpure
  have hboundL (s : Finset E) (hs : s ∈ L.faces) : s.card ≤ 3 := by
    obtain ⟨t,_,ht,hst⟩ := hpureL s hs
    exact (Finset.card_le_card hst).trans_eq ht
  have hlocal (p : E) (hp : p ∈ L.space) :
      ∃ d q : Set E, IsFinitePLBallPair (Fin 2 → ℝ) d q ∧ d ⊆ L.space ∧
        p ∈ d \ q ∧ IsOpen ((Subtype.val : L.space → E) ⁻¹' (d \ q)) := by
    obtain ⟨d,q,hd,hdK,hpd,hopen⟩ := K.exists_local_disk_of_closed_surface_incidence
      hK hpure hcofaces hlinks (hspace.subset hp)
    exact ⟨d,q,hd,hdK.trans hspace.symm.subset,hpd,
      hopen.preimage (Homeomorph.setCongr hspace).continuous⟩
  refine ⟨hpureL,?_,?_⟩
  · intro s hs hs2
    obtain ⟨p,hps⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (s : Set E))
      (Finset.coe_nonempty.mpr (L.nonempty_of_mem_faces hs)).convexHull
    obtain ⟨d,q,hd,hdL,hpd,hopen⟩ := hlocal p
      (L.convexHull_subset_space hs (intrinsicInterior_subset hps))
    exact L.ncard_triangle_cofaces_eq_two_of_local_disk hL hboundL hs hs2 hps hd hdL hpd hopen
  · intro p hp
    obtain ⟨d,q,hd,hdL,hpd,hopen⟩ := hlocal p (L.vertices_subset_space hp)
    exact L.isConnected_link_of_local_finitePLBallPair (by simp) hL hp hd hdL hpd hopen

theorem IsSubdivision.closed_surface_incidence
    {K L : SimplicialComplex ℝ E} (hLK : L.IsSubdivision K)
    (hK : K.faces.Finite) (hL : L.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space) :
    (∀ s ∈ L.faces, ∃ t ∈ L.faces, t.card = 3 ∧ s ⊆ t) ∧
    (∀ s ∈ L.faces, s.card = 2 →
      {t : Finset E | t ∈ L.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2) ∧
    (∀ p ∈ L.vertices, IsConnected (L.link p).space) :=
  K.closed_surface_incidence_of_finite_same_carrier L hK hL hLK.space_eq hpure hcofaces hlinks

end Geometry.SimplicialComplex
