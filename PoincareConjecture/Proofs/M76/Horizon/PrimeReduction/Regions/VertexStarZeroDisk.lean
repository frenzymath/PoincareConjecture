import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.VertexStarHalfBalls
import PoincareConjecture.Proofs.M76.PrimeReduction.ConvexZeroSectionDisk
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarMarkedCutCharts

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

private theorem geometric_closedStar_zero_disk
    (K : SimplicialComplex ℝ (Fin 3 → ℝ)) (hK : K.faces.Finite)
    (hz : (0 : Fin 3 → ℝ) ∈ K.vertices)
    (hint : (0 : Fin 3 → ℝ) ∈ interior K.space) :
    IsFinitePLBallPair (ℝ × ℝ)
      ((K.closedStar 0).space ∩ {x | x 0 = 0})
      ((K.link 0).space ∩ {x | x 0 = 0}) := by
  classical
  let A : (Fin 3 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
  obtain ⟨C, _, H, hC, hcv, hC0, _, _, hH, hboundary, hmarks⟩ :=
    K.exists_finitePL_closedStar_chart_preserving_cut_family hK hz hint
      (ContinuousLinearEquiv.refl ℝ _) (fun _ : Unit => A)
  obtain ⟨g, ⟨J, hJ, hJC, hg⟩, hginv⟩ := hH.symm
  have hgfull : FinitePiecewiseAffineOn g C := ⟨J, hJ, hJC, hg⟩
  have hgin (x : Fin 3 → ℝ) (hx : x ∈ C) : g x ∈ (K.closedStar 0).space := by
    rw [← hginv ⟨x, hx⟩]
    exact (H.symm ⟨x, hx⟩).property
  have hforward (x : Fin 3 → ℝ) (hx : x ∈ C) :
      (H ⟨g x, hgin x hx⟩ : Fin 3 → ℝ) = x := by
    have he : (⟨g x, hgin x hx⟩ : (K.closedStar 0).space) = H.symm ⟨x, hx⟩ :=
      Subtype.ext (hginv ⟨x, hx⟩).symm
    rw [he, H.apply_symm_apply]
  have hback (x : (K.closedStar 0).space) : g (H x) = x := by
    rw [← hginv (H x), H.symm_apply_apply]
  have hginj : InjOn g C := by
    intro x hx y hy hxy
    have he : H.symm ⟨x, hx⟩ = H.symm ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hginv] using hxy
    exact congrArg Subtype.val (H.symm.injective he)
  have hzero (x : Fin 3 → ℝ) (hx : x ∈ C) : x 0 = 0 ↔ g x 0 = 0 := by
    have h := (hmarks () ⟨g x, hgin x hx⟩).1
    change ((H ⟨g x, hgin x hx⟩ : Fin 3 → ℝ) 0 = 0 ↔ g x 0 = 0) at h
    rwa [hforward x hx] at h
  have himage : g '' (C ∩ {x | x 0 = 0}) =
      (K.closedStar 0).space ∩ {x | x 0 = 0} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hgin x hx.1, (hzero x hx.1).mp hx.2⟩
    · intro hy
      let z : (K.closedStar 0).space := ⟨y, hy.1⟩
      refine ⟨H z, ⟨(H z).property, ?_⟩, hback z⟩
      apply (hzero (H z) (H z).property).mpr
      rw [hback z]
      exact hy.2
  have hlinksub : (K.link 0).space ⊆ (K.closedStar 0).space :=
    space_subset_of_le (K.link_le_closedStar 0)
  have hrim : g '' (frontier C ∩ {x | x 0 = 0}) =
      (K.link 0).space ∩ {x | x 0 = 0} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxC := hC.isClosed.frontier_subset hx.1
      refine ⟨(hboundary ⟨g x, hgin x hxC⟩).mpr ?_, (hzero x hxC).mp hx.2⟩
      rw [hforward x hxC]
      exact hx.1
    · intro hy
      let z : (K.closedStar 0).space := ⟨y, hlinksub hy.1⟩
      refine ⟨H z, ⟨(hboundary z).mp hy.1, ?_⟩, hback z⟩
      apply (hzero (H z) (H z).property).mpr
      rw [hback z]
      exact hy.2
  have hA : A.toAffineMap.linear ≠ 0 := by
    intro h
    have he := LinearMap.congr_fun h (fun _ => (1 : ℝ))
    norm_num [A] at he
  have hball := J.isFinitePLBallPair_convex_zero_section hJ hC hcv hJC
    A.toAffineMap hA ⟨0, hC0, A.map_zero⟩
    (show Module.finrank ℝ (Fin 3 → ℝ) = Module.finrank ℝ (ℝ × ℝ) + 1 by
      simp [Module.finrank_prod])
  have hresult := hball.image_of_subset hgfull inter_subset_left hginj
  change IsFinitePLBallPair (ℝ × ℝ)
    (g '' (C ∩ {x | x 0 = 0})) (g '' (frontier C ∩ {x | x 0 = 0})) at hresult
  simpa only [himage, hrim] using hresult

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem isFinitePLBallPair_closedStar_chart_zero_section
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p : E} (hp : p ∈ K.vertices) {f : E → (Fin 3 → ℝ)}
    (hf : (K.closedStar p).AffineOnFaces f)
    (hinj : InjOn f (K.closedStar p).space)
    (hzero : f p 0 = 0)
    (hint : f p ∈ interior (f '' (K.closedStar p).space)) :
    IsFinitePLBallPair (ℝ × ℝ)
      ((K.closedStar p).space ∩ {x | f x 0 = 0})
      ((K.link p).space ∩ {x | f x 0 = 0}) := by
  classical
  let a : (Fin 3 → ℝ) ≃ᴬ[ℝ] (Fin 3 → ℝ) :=
    ContinuousAffineEquiv.constVAdd ℝ (Fin 3 → ℝ) (-f p)
  let g : E → (Fin 3 → ℝ) := fun x => a (f x)
  have hg : (K.closedStar p).AffineOnFaces g := hf.postcomp a.toContinuousAffineMap
  have hginj : InjOn g (K.closedStar p).space := fun _ hx _ hy h =>
    hinj hx hy (a.injective h)
  have hgp : g p = 0 := by
    change -f p + f p = 0
    exact neg_add_cancel _
  have hgheight (x : E) : g x 0 = f x 0 := by
    change -(f p 0) + f x 0 = f x 0
    rw [hzero, neg_zero, zero_add]
  have hpstar : p ∈ (K.closedStar p).vertices := by
    change {p} ∈ K.faces ∧ insert p {p} ∈ K.faces
    exact ⟨hp, by
      rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self p)]
      exact hp⟩
  have hstar : (K.closedStar p).closedStar p = K.closedStar p := by
    ext s
    change ((s ∈ K.faces ∧ insert p s ∈ K.faces) ∧
      insert p s ∈ K.faces ∧ insert p (insert p s) ∈ K.faces) ↔
      s ∈ K.faces ∧ insert p s ∈ K.faces
    simp only [Finset.insert_idem, and_self, and_assoc]
  have hlink : (K.closedStar p).link p = K.link p := by
    ext s
    change ((s ∈ K.faces ∧ insert p s ∈ K.faces) ∧ p ∉ s ∧
      insert p s ∈ K.faces ∧ insert p (insert p s) ∈ K.faces) ↔
      s ∈ K.faces ∧ p ∉ s ∧ insert p s ∈ K.faces
    simp only [Finset.insert_idem]
    tauto
  let J := hg.embeddedImage hginj
  have hJ : J.faces.Finite := hg.embeddedImage_finite hginj (finite_closedStar_faces hK p)
  have hJs : J.space = g '' (K.closedStar p).space := hg.embeddedImage_space hginj
  have hJstar : (J.closedStar 0).space = J.space := by
    have h := hg.embeddedImage_closedStar_space hginj hpstar
    change (J.closedStar (g p)).space = g '' ((K.closedStar p).closedStar p).space at h
    simpa only [hgp, hstar, ← hJs] using h
  have hJlink : (J.link 0).space = g '' (K.link p).space := by
    have h := hg.embeddedImage_link_space hginj hpstar
    change (J.link (g p)).space = g '' ((K.closedStar p).link p).space at h
    simpa only [hgp, hlink] using h
  have hzJ : (0 : Fin 3 → ℝ) ∈ J.vertices := by
    rw [hg.embeddedImage_vertices hginj]
    exact ⟨p, hpstar, hgp⟩
  have hJint : (0 : Fin 3 → ℝ) ∈ interior J.space := by
    rw [hJs]
    change (0 : Fin 3 → ℝ) ∈ interior ((a ∘ f) '' (K.closedStar p).space)
    rw [image_comp]
    change (0 : Fin 3 → ℝ) ∈ interior (a.toHomeomorph '' (f '' (K.closedStar p).space))
    rw [← a.toHomeomorph.image_interior]
    exact ⟨f p, hint, hgp⟩
  have hball := geometric_closedStar_zero_disk J hJ hzJ hJint
  rw [hJstar] at hball
  let b : (Fin 3 → ℝ) → E := Function.invFunOn g (K.closedStar p).space
  have hleft : LeftInvOn b g (K.closedStar p).space := hginj.leftInvOn_invFunOn
  have hback (x : Fin 3 → ℝ) (hx : x ∈ J.space) :
      b x ∈ (K.closedStar p).space ∧ g (b x) = x := by
    obtain ⟨y, hy, rfl⟩ := hJs.subset hx
    rw [hleft hy]
    exact ⟨hy, rfl⟩
  have hb : FinitePiecewiseAffineOn b J.space :=
    (hg.invFunOn_embeddedImage hginj).finitePiecewiseAffineOn hJ
  have hbinj : InjOn b J.space := by
    intro x hx y hy hxy
    exact (hback x hx).2.symm.trans ((congrArg g hxy).trans (hback y hy).2)
  have hlinksub : (K.link p).space ⊆ (K.closedStar p).space :=
    space_subset_of_le (K.link_le_closedStar p)
  have himage (T : Set E) (hT : T ⊆ (K.closedStar p).space) :
      b '' ((g '' T) ∩ {x | x 0 = 0}) = T ∩ {x | f x 0 = 0} := by
    ext x
    constructor
    · rintro ⟨y, ⟨⟨z, hz, rfl⟩, he⟩, rfl⟩
      rw [hleft (hT hz)]
      exact ⟨hz, (hgheight z).symm.trans he⟩
    · intro hx
      exact ⟨g x, ⟨mem_image_of_mem g hx.1, (hgheight x).trans hx.2⟩, hleft (hT hx.1)⟩
  have hresult := hball.image_of_subset hb inter_subset_left hbinj
  simpa only [hJs, hJlink, himage _ Subset.rfl, himage _ hlinksub] using hresult

end Geometry.SimplicialComplex
