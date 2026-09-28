import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneSurfaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarInteriorBall
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityOrdinaryDiskBoundary
import PoincareConjecture.Proofs.M76.Mathlib.PrescribedSubdivisionVertices

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "Cube" => closedBall (0 : V2) 1

theorem exists_proper_disk_interior_pair_chart {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3) {R D : Set E}
    (b : Cube ≃ₜ D) (hb : b.IsFinitePL)
    (hproper : ∀ x : Cube,
      (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere (0 : V2) 1)
    {p : E} (hpD : p ∈ D) (hpR : p ∈ interior R) :
    ∃ H : OpenPartialHomeomorph E ((ℝ × ℝ) × ℝ),
      p ∈ H.source ∧ H.source ⊆ interior R ∧
      H.target = interior (CoordinateHalfBoxes.box 1) ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧ H p = 0 ∧
      ∀ x ∈ H.source, x ∈ D ↔ (H x).2 = 0 := by
  classical
  let z : Cube := b.symm ⟨p, hpD⟩
  have hbz : (b z : E) = p := congrArg Subtype.val (b.apply_symm_apply ⟨p, hpD⟩)
  have hznot : (z : V2) ∉ sphere (0 : V2) 1 := by
    intro hz
    have hfront : p ∈ frontier R := hbz ▸ (hproper z).mpr hz
    exact hfront.2 hpR
  have hzint : (z : V2) ∈ interior Cube := by
    by_contra hn
    apply hznot
    rw [← frontier_closedBall (0 : V2) one_ne_zero]
    exact ⟨subset_closure z.property, hn⟩
  let a : V2 ≃ᴬ[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toContinuousAffineEquiv
  let Q := a '' Cube
  let z0 : ℝ × ℝ := a z
  have hzQ : z0 ∈ Q := mem_image_of_mem a z.property
  have hzQint : z0 ∈ interior Q := by
    change a.toHomeomorph z ∈ interior (a.toHomeomorph '' Cube)
    rw [← a.toHomeomorph.image_interior]
    exact mem_image_of_mem a hzint
  let τ : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-p)
  have hτp : τ p = 0 := by change -p + p = 0; exact neg_add_cancel p
  obtain ⟨u, hu, hbu⟩ := hb
  let f : (ℝ × ℝ) → E := τ ∘ (u ∘ a.symm)
  have hf : FinitePiecewiseAffineOn f Q :=
    (hu.precomp_affineEquiv a.symm).postcomp τ.toContinuousAffineMap
  have hfu (x : Cube) : f (a x) = τ (b x) := by
    change τ (u (a.symm (a x))) = τ (b x)
    rw [a.symm_apply_apply, ← hbu x]
  have hfz : f z0 = 0 := by rw [hfu z, hbz, hτp]
  have hinj : InjOn f Q := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    have hval : (b ⟨x, hx⟩ : E) = b ⟨y, hy⟩ := τ.injective
      ((hfu ⟨x, hx⟩).symm.trans (hxy.trans (hfu ⟨y, hy⟩)))
    exact congrArg a (congrArg Subtype.val (b.injective (Subtype.ext hval)))
  obtain ⟨K, hK, hKQ, hfK⟩ := hf
  obtain ⟨L, hL, hLK, hzL⟩ := K.exists_finite_subdivision_with_vertices hK {z0}
    (by simpa only [Finset.coe_singleton, singleton_subset_iff, hKQ] using hzQ)
  have hLQ : L.space = Q := hLK.space_eq.trans hKQ
  have hzL' : z0 ∈ L.vertices := hzL (by simp)
  have hfL : L.AffineOnFaces f := hLK.affineOnFaces hfK
  have hinjL : InjOn f L.space := hinj.mono hLQ.subset
  have hsource := L.isFinitePLBallPair_closedStar_of_interior hL hzL'
    (hLQ.symm ▸ hzQint) (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  obtain ⟨n, P, hPi, hPe, hPb⟩ := hsource.exists_polygon_boundary
  have hlinksub : (L.link z0).space ⊆ L.space :=
    SimplicialComplex.space_subset_of_le (fun _ hs => hs.1)
  have hPQ : P.boundary ℝ ⊆ Q := hPb.subset.trans (hlinksub.trans hLQ.subset)
  obtain ⟨m, P0, hP0i, hP0e, hP0b⟩ :=
    P.exists_polygon_finitePL_image hPe hPi
      ⟨L, hL, hLQ, hfL⟩ hPQ (hinj.mono hPQ)
  let M := hfL.embeddedImage hinjL
  have hM : M.faces.Finite := hfL.embeddedImage_finite hinjL hL
  have h0M : (0 : E) ∈ M.vertices := by
    rw [hfL.embeddedImage_vertices]
    exact ⟨z0, hzL', hfz⟩
  have hMlink : (M.link 0).space = f '' (L.link z0).space := by
    simpa only [hfz] using hfL.embeddedImage_link_space hinjL hzL'
  have hP0M : P0.boundary ℝ = (M.link 0).space := by
    rw [hP0b, hPb, ← hMlink]
  have hMs : M.space = τ '' D := by
    rw [hfL.embeddedImage_space, hLQ]
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨b ⟨x, hx⟩, (b ⟨x, hx⟩).property, (hfu ⟨x, hx⟩).symm⟩
    · rintro ⟨x, hx, rfl⟩
      let t : Cube := b.symm ⟨x, hx⟩
      refine ⟨a t, mem_image_of_mem a t.property, ?_⟩
      rw [hfu t]
      exact congrArg τ (congrArg Subtype.val (b.apply_symm_apply ⟨x, hx⟩))
  let U : Set E := τ.symm ⁻¹' interior R
  have hU : IsOpen U := isOpen_interior.preimage τ.symm.continuous
  have h0U : (0 : E) ∈ U := by
    change τ.symm 0 ∈ interior R
    rw [← hτp, τ.symm_apply_apply]
    exact hpR
  let coords : E ≃L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)
  obtain ⟨C, forms, J, hC, hcv, h0C, hCU, hdisj, hstar,
    hforms, hrep, hJ, hJC⟩ :=
    M.exists_small_closedStar_halfspace_neighborhood hM h0M hU h0U coords
  obtain ⟨k, P1, hP1i, hP1e, hP1b⟩ :=
    M.exists_polygon_closedStar_convex_frontier hM P0 hP0e hP0i hP0M
      hC hcv h0C hdisj forms hforms hrep
  have hP1ne : ((M.closedStar 0).space ∩ frontier C).Nonempty := by
    rw [← hP1b]
    exact ⟨P1 0, P1.vertex_mem_boundary 0⟩
  have hcone : M.space ∩ C = convexJoin ℝ {0} (P1.boundary ℝ) := by
    rw [hP1b, M.convexJoin_closedStar_frontier_eq_inter hC hcv h0C hdisj hP1ne]
    exact hstar
  have hMint : interior M.space = ∅ := by
    apply M.interior_space_eq_empty_of_card_le hM
    intro s hs
    rw [hfL.embeddedImage_faces hinjL] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have htcard := (L.indep ht).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    have ht3 : t.card ≤ 3 := by simpa [Module.finrank_prod] using htcard
    rw [hdim]
    exact Finset.card_image_le.trans ht3
  obtain ⟨q, hq⟩ := M.exists_frontier_notMem_closedStar hMint
    (M.vertices_subset_space h0M) hC hcv h0C
  have hP1C : P1.boundary ℝ ⊆ frontier C := hP1b.subset.trans inter_subset_right
  have hqP : (q : E) ∉ P1.boundary ℝ := fun hx => hq (hP1b.subset hx).1
  obtain ⟨d0, d1, hd0, hd1, hcover, hinter, _⟩ :=
    J.exists_convex_sphere_polygon_cut hJ hC hcv ⟨0, h0C⟩ hJC hdim
      P1 hP1e hP1i hP1C q hqP
  obtain ⟨H, hHs, hHt, hH, hHi, hH0, hHD⟩ :=
    exists_conical_surface_chart hdim hC hcv h0C hd0 hd1 hcover hinter hcone
  let F := τ.toHomeomorph.toOpenPartialHomeomorph.trans H
  have hpF : p ∈ F.source := by
    change p ∈ (univ : Set E) ∧ τ p ∈ H.source
    exact ⟨mem_univ p, by rw [hτp, hHs]; exact h0C⟩
  have hFt : F.target = interior (CoordinateHalfBoxes.box 1) := by
    change H.target ∩ H.symm ⁻¹' (univ : Set E) = _
    simp only [preimage_univ, inter_univ, hHt]
  have hF : LocallyPiecewiseAffineOn F F.source :=
    hH.comp (locallyPiecewiseAffineOn_affine τ.toContinuousAffineMap isOpen_univ)
  have hFi : LocallyPiecewiseAffineOn F.symm F.target :=
    (locallyPiecewiseAffineOn_affine τ.symm.toContinuousAffineMap isOpen_univ).comp hHi
  refine ⟨F, hpF, ?_, hFt, hF, hFi, ?_, ?_⟩
  · intro x hx
    have hxU := hCU (interior_subset (hHs.subset hx.2))
    change τ.symm (τ x) ∈ interior R at hxU
    simpa only [τ.symm_apply_apply] using hxU
  · change H (τ p) = 0
    rw [hτp, hH0]
  · intro x hx
    have hτx : τ x ∈ M.space ↔ x ∈ D := by
      rw [hMs]
      constructor
      · rintro ⟨y, hy, heq⟩
        exact τ.injective heq ▸ hy
      · exact mem_image_of_mem τ
    exact hτx.symm.trans (hHD (τ x) hx.2)

end PoincareConjecture.M76.HamiltonIndexOne
