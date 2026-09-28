import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskFrontierStars









set_option autoImplicit false

open Set Metric Geometry Filter
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => ((ℝ × ℝ) × ℝ)
local notation "P2" => (ℝ × ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}




theorem HamiltonProperDiskTriangulation.frontier_vertex_ballPair
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices)
    (hpfront : (p : E) ∈ frontier R) :
    IsFinitePLBallPair P2 ((T.vertexBlock p).space ∩ frontier R)
      (((T.vertexBlock p).space ∩ frontier R) ∩
        ((T.vertexBlock p).link p).space) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype T.boundary.faces := (T.finite.subset T.boundary_le).fintype
  let N := T.boundary.barycentricDualBlock {(p : E)}
  let H := (T.pairChart p).chart
  have hN : N.faces.Finite := T.boundary.barycentricDualBlock_finite {(p : E)}
  have hNK : N ≤ T.vertexBlock p :=
    T.ambient.barycentricDualBlock_mono_of_subcomplex T.boundary T.boundary_le _
  have hNs : N.space = (T.vertexBlock p).space ∩ frontier R := by
    simpa only [HamiltonProperDiskTriangulation.vertexBlock, T.boundary_space] using
      (T.ambient.barycentricDualBlock_space_inter_subcomplex
        T.boundary T.boundary_le {(p : E)}).symm
  have hpK : (p : E) ∈ T.ambient.vertices := T.disk_le p.property
  have hpF : (p : E) ∈ T.boundary.vertices := by
    obtain ⟨s, hs, hps⟩ := SimplicialComplex.mem_space_iff.mp
      (T.boundary_space.symm.subset hpfront)
    exact T.boundary.face_subset_vertices hs
      ((T.ambient.vertex_mem_convexHull_iff hpK (T.boundary_le hs)).mp hps)
  have hpN : (p : E) ∈ N.vertices := by
    simpa only [N, Finset.centroid_singleton, id_eq] using
      T.boundary.faceCentroid_mem_barycentricDualBlock_vertices hpF
  have hstar : N.closedStar p = N := by
    simpa only [N, Finset.centroid_singleton, id_eq] using
      T.boundary.barycentricDualBlock_closedStar_faceCentroid hpF
  have hlink : (N.link p).space = N.space ∩ ((T.vertexBlock p).link p).space :=
    (T.vertexBlock p).link_space_eq_inter_of_closedStar_eq N hNK p hstar
  obtain ⟨_, _, _, hsource, f0, hf0, _, _, _, hvalue⟩ :=
    T.vertexBlock_centered_chart p
  have hNS : N.space ⊆ H.source :=
    (SimplicialComplex.space_subset_of_le hNK).trans hsource
  have hNF : N.space ⊆ frontier R := hNs.subset.trans inter_subset_right
  have hpH : (p : E) ∈ H.source := hNS (N.vertices_subset_space hpN)
  have hhalf : ∀ x ∈ H.source, x ∈ R ↔ 0 ≤ (H x).1.1 := by
    rcases (T.pairChart p).model with ⟨hinside, _⟩ | ⟨hhalf, _⟩
    · exact False.elim (hpfront.2 (hinside hpH))
    · exact hhalf
  let ell : V →L[ℝ] ℝ :=
    { toFun := fun z => z.1.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := by fun_prop }
  let rho : V →L[ℝ] P2 :=
    { toFun := fun z => (z.1.2, z.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := by fun_prop }
  let a : P2 →L[ℝ] V :=
    { toFun := fun z => ((0, z.1), z.2)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp
      cont := by fun_prop }
  have hell : ell.toContinuousAffineMap.toAffineMap.linear ≠ 0 := by
    intro he
    have h := congrArg (fun m : V →ₗ[ℝ] ℝ => m ((1, 0), 0)) he
    change (1 : ℝ) = 0 at h
    exact one_ne_zero h
  have hfront := H.isImage_frontier_of_affine_nonneg ell.toContinuousAffineMap hell hhalf
  obtain ⟨q, hqs, _, hqval, _⟩ := H.exists_affine_hypersurface_chart
    ell.toContinuousAffineMap hfront a.toContinuousAffineMap rho.toContinuousAffineMap
    (fun z => rfl) (by
      intro z hz
      change ((0, z.1.2), z.2) = z
      exact Prod.ext (Prod.ext hz.symm rfl) rfl)
    (fun _ => rfl) ⟨p, hpfront⟩
  let f : E → P2 := fun x => rho (H x)
  have hHaffine : N.AffineOnFaces H := by
    let add : V →ᴬ[ℝ] V :=
      ContinuousAffineMap.id ℝ V + ContinuousAffineMap.const ℝ V (H p)
    have hfN : N.AffineOnFaces f0 := fun s hs => hf0 s (hNK hs)
    apply (hfN.postcomp add).congr
    intro x _
    change f0 x + H p = H x
    rw [hvalue x, sub_add_cancel]
  have hf : N.AffineOnFaces f := hHaffine.postcomp rho.toContinuousAffineMap
  have hi : InjOn f N.space := by
    intro x hx y hy hxy
    change ((H x).1.2, (H x).2) = ((H y).1.2, (H y).2) at hxy
    have hxzero := (hfront.apply_mem_iff (hNS hx)).mpr (hNF hx)
    have hyzero := (hfront.apply_mem_iff (hNS hy)).mpr (hNF hy)
    exact H.injOn (hNS hx) (hNS hy)
      (Prod.ext (Prod.ext (hxzero.trans hyzero.symm)
        (congrArg (fun z : P2 => z.1) hxy)) (congrArg (fun z : P2 => z.2) hxy))
  let K := T.boundary.barycentricSubdivision
  have hpK' : (p : E) ∈ K.vertices :=
    (T.boundary.barycentricDualBlock_le {(p : E)}) hpN
  obtain ⟨r, hr, hrN⟩ := K.exists_ball_inter_space_subset_closedStar
    T.boundary.barycentricSubdivision_finite hpK'
  have hKspace : K.space = frontier R :=
    T.boundary.barycentricSubdivision_isSubdivision.space_eq.trans T.boundary_space
  have hNstar : K.closedStar p = N :=
    (T.boundary.barycentricDualBlock_singleton_eq_closedStar hpF).symm
  have hcont : ContinuousAt (Subtype.val : frontier R → E) ⟨p, hpfront⟩ :=
    continuous_subtype_val.continuousAt
  have hnhds : (Subtype.val ⁻¹' N.space : Set (frontier R)) ∈ 𝓝 ⟨p, hpfront⟩ := by
    apply Filter.mem_of_superset (hcont.preimage_mem_nhds (ball_mem_nhds (p : E) hr))
    intro x hx
    exact hNstar ▸ hrN ⟨hKspace.symm.subset x.property, hx⟩
  have hpq : (⟨p, hpfront⟩ : frontier R) ∈ q.source := by
    rw [hqs]
    exact hpH
  have hqint : q ⟨p, hpfront⟩ ∈ interior (q '' (Subtype.val ⁻¹' N.space)) :=
    mem_interior_iff_mem_nhds.mpr (q.image_mem_nhds hpq hnhds)
  have himage : q '' (Subtype.val ⁻¹' N.space) ⊆ f '' N.space := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hqval x).symm⟩
  have hint : f p ∈ interior (f '' N.space) := by
    have h := interior_mono himage hqint
    rwa [hqval ⟨p, hpfront⟩] at h
  let J := hf.embeddedImage hi
  have hJ : J.faces.Finite := hf.embeddedImage_finite hi hN
  have hpJ : f p ∈ J.vertices := by
    rw [hf.embeddedImage_vertices hi]
    exact ⟨p, hpN, rfl⟩
  have hJint : f p ∈ interior J.space := by
    rw [hf.embeddedImage_space hi]
    exact hint
  have hJstar : (J.closedStar (f p)).space = f '' N.space := by
    simpa only [hstar] using hf.embeddedImage_closedStar_space hi hpN
  have hJlink : (J.link (f p)).space = f '' (N.link p).space :=
    hf.embeddedImage_link_space hi hpN
  have hball := J.isFinitePLBallPair_closedStar_of_interior hJ hpJ hJint
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  rw [hJstar, hJlink] at hball
  obtain ⟨e, he, heval⟩ := (hf.finitePiecewiseAffineOn hN).exists_homeomorph_image hi
  have hlinks : (N.link p).space ⊆ N.space :=
    SimplicialComplex.space_subset_of_le (fun _ hs => hs.1)
  have hballN : IsFinitePLBallPair P2 N.space (N.link p).space := by
    apply hball.of_homeomorph hlinks e he
    intro x
    rw [heval x]
    constructor
    · exact fun hx => mem_image_of_mem f hx
    · rintro ⟨y, hy, hyx⟩
      exact hi (hlinks hy) x.property hyx ▸ hy
  simpa only [hlink, hNs] using hballN

end PoincareConjecture.M76.HamiltonIndexOne
