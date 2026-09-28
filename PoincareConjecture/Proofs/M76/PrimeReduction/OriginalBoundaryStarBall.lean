import PoincareConjecture.Proofs.M76.PrimeReduction.EmbeddedHalfspaceStarBall
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalStarChartImages









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]



theorem exists_original_boundary_star_half_ball
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {p : E} (hp : p ∈ K.vertices) (hpb : (g p : X) ∈ frontier R)
    (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z)))
    (hregion : B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
      ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ∃ (C : Set V3) (A : V3 →ₗ[ℝ] ℝ) (v : V3)
      (G : (K.closedStar p).space ≃ₜ (C ∩ {x | 0 ≤ A x} : Set V3)),
      A v = 1 ∧ IsCompact C ∧ Convex ℝ C ∧ (0 : V3) ∈ interior C ∧
      (∃ J : SimplicialComplex ℝ V3, J.faces.Finite ∧ J.space = C) ∧
      IsFinitePLBallPair V3 (K.closedStar p).space
        (((K.closedStar p).link p).space ∪
          ((K.closedStar p).space ∩ {z | (g z : X) ∈ frontier R})) ∧
      G.IsFinitePL ∧
      (∀ x : (K.closedStar p).space,
        (x : E) ∈ ((K.closedStar p).link p).space ↔ (G x : V3) ∈ frontier C) ∧
      ∀ x : (K.closedStar p).space, A (G x : V3) = 0 ↔ (g x : X) ∈ frontier R := by
  classical
  let N := K.closedStar p
  have hpN : p ∈ N.vertices := by
    change {p} ∈ K.faces ∧ insert p {p} ∈ K.faces
    exact ⟨hp, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self p)]
      using (show {p} ∈ K.faces from hp)⟩
  have hpsource := hsource (N.vertices_subset_space hpN)
  rcases hregion with hinterior | ⟨ell, v, hv, hhalf⟩
  · exact False.elim (hpb.2 (interior_maximal hinterior B.open_source hpsource))
  have hlin : ell.toAffineMap.linear ≠ 0 := by
    intro he
    have hv' : ell.toAffineMap.linear v = 1 := hv
    rw [he] at hv'
    exact zero_ne_one hv'
  have hboundary (z : E) (hz : z ∈ N.space) :
      (g z : X) ∈ frontier R ↔ ell (B (g z)) = 0 :=
    ((B.isImage_frontier_of_affine_nonneg ell hlin hhalf).apply_mem_iff
      (hsource hz)).symm
  have hzeroell : ell (B (g p)) = 0 :=
    (hboundary p (N.vertices_subset_space hpN)).mp hpb
  obtain ⟨hinj, O, hO, hgpO, hOB, hOR⟩ :=
    K.exists_original_open_neighborhood_of_closedStar hK H g hg hp B hsource
  let q : V3 := B (g p)
  let t : V3 ≃ᴬ[ℝ] V3 := ContinuousAffineEquiv.constVAdd ℝ V3 (-q)
  let f : E → V3 := fun z => t (B (g z))
  let A : V3 →ₗ[ℝ] ℝ := ell.contLinear.toLinearMap
  have hcenter (y : V3) : A (t y) = ell y := by
    have he := ell.contLinear_map_vsub y q
    change ell.contLinear (y - q) = ell y - ell q at he
    have hq : ell q = 0 := hzeroell
    rw [hq, sub_zero] at he
    change ell.contLinear (-q + y) = ell y
    simpa only [sub_eq_add_neg, add_comm y (-q)] using he
  have hf : N.AffineOnFaces f := hface.postcomp t.toContinuousAffineMap
  have hfi : InjOn f N.space := by
    intro x hx y hy he
    exact hinj hx hy (t.injective he)
  have hfp : f p = 0 := by change -q + q = 0; exact neg_add_cancel q
  have hself : (N.closedStar p).space = N.space := by
    have he : N.closedStar p = N := by
      ext s
      change ((s ∈ K.faces ∧ insert p s ∈ K.faces) ∧
        insert p s ∈ K.faces ∧ insert p (insert p s) ∈ K.faces) ↔
        s ∈ K.faces ∧ insert p s ∈ K.faces
      simp only [Finset.insert_idem]
      tauto
    rw [he]
  have hside : f '' N.space ⊆ {x | 0 ≤ A x} := by
    rintro _ ⟨z, hz, rfl⟩
    change 0 ≤ A (f z)
    rw [show f z = t (B (g z)) from rfl, hcenter]
    exact (hhalf (g z) (hsource hz)).mp (g z).property
  let U : Set V3 := t '' (B '' O)
  have hU : IsOpen U :=
    t.toHomeomorph.isOpenMap _ (B.isOpen_image_of_subset_source hO hOB)
  have h0U : (0 : V3) ∈ U := by
    have htq : t q = 0 := by change -q + q = 0; exact neg_add_cancel q
    exact ⟨q, mem_image_of_mem B hgpO, htq⟩
  have hUhalf : U ∩ {x | 0 ≤ A x} ⊆ f '' N.space := by
    rintro y ⟨⟨z, ⟨x, hxO, hxz⟩, hzy⟩, hyA⟩
    subst z
    subst y
    change 0 ≤ A (t (B x)) at hyA
    rw [hcenter] at hyA
    obtain ⟨w, hwN, hwx⟩ := hOR ⟨hxO, (hhalf x (hOB hxO)).mpr hyA⟩
    exact ⟨w, hwN, congrArg (fun y => t (B y)) hwx⟩
  obtain ⟨C, G, hC, hcv, hC0, hpoly, hpair, hG, hGb, hGzero⟩ :=
    hf.exists_halfspace_star_ball (SimplicialComplex.finite_closedStar_faces hK p)
      hfi hpN hfp hself A v (by change 0 < ell.contLinear v; rw [hv]; norm_num)
      hside hU h0U hUhalf (ContinuousLinearEquiv.refl ℝ V3)
  have hzero (z : E) : A (f z) = 0 ↔ ell (B (g z)) = 0 := by rw [hcenter]
  have hmarks : N.space ∩ {z | A (f z) = 0} =
      N.space ∩ {z | (g z : X) ∈ frontier R} := by
    ext z
    constructor
    · rintro ⟨hz, hz0⟩
      exact ⟨hz, (hboundary z hz).mpr ((hzero z).mp hz0)⟩
    · rintro ⟨hz, hzb⟩
      exact ⟨hz, (hzero z).mpr ((hboundary z hz).mp hzb)⟩
  rw [hmarks] at hpair
  exact ⟨C, A, v, G, hv, hC, hcv, hC0, hpoly, hpair, hG, hGb,
    fun z => (hGzero z).trans ((hzero z).trans (hboundary z z.property).symm)⟩

end PoincareConjecture.M76
