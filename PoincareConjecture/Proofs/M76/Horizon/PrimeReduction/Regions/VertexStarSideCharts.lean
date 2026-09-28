import PoincareConjecture.Proofs.M76.PrimeReduction.EmbeddedHalfspaceStarBall

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_closedStar_side_chart
    (K P : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hPK : P ≤ K)
    {p : E} (hp : p ∈ K.vertices) {f : E → (Fin 3 → ℝ)}
    (hf : (K.closedStar p).AffineOnFaces f)
    (hinj : InjOn f (K.closedStar p).space)
    (hzero : f p 0 = 0)
    (hint : f p ∈ interior (f '' (K.closedStar p).space))
    (hside : (P.closedStar p).space = (K.closedStar p).space ∩ {x | 0 ≤ f x 0}) :
    ∃ (C : Set (Fin 3 → ℝ)) (v : Fin 3 → ℝ)
      (H : (P.closedStar p).space ≃ₜ (C ∩ {x | 0 ≤ x 0} : Set (Fin 3 → ℝ))),
      v 0 = 1 ∧ IsCompact C ∧ Convex ℝ C ∧ (0 : Fin 3 → ℝ) ∈ interior C ∧
      (∃ J : SimplicialComplex ℝ (Fin 3 → ℝ), J.faces.Finite ∧ J.space = C) ∧
      IsFinitePLBallPair (Fin 3 → ℝ) (P.closedStar p).space
        ((P.link p).space ∪ ((P.closedStar p).space ∩ {x | f x 0 = 0})) ∧
      H.IsFinitePL ∧
      (∀ x : (P.closedStar p).space,
        (x : E) ∈ (P.link p).space ↔ (H x : Fin 3 → ℝ) ∈ frontier C) ∧
      ∀ x : (P.closedStar p).space, (H x : Fin 3 → ℝ) 0 = 0 ↔ f x 0 = 0 := by
  classical
  have hP : P.faces.Finite := hK.subset hPK
  have hstarle : P.closedStar p ≤ K.closedStar p := fun _ hs =>
    ⟨hPK hs.1, hPK hs.2⟩
  have hstarsub : (P.closedStar p).space ⊆ (K.closedStar p).space :=
    space_subset_of_le hstarle
  have hpKstar : p ∈ (K.closedStar p).vertices := by
    change {p} ∈ K.faces ∧ insert p {p} ∈ K.faces
    exact ⟨hp, by
      rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self p)]
      exact hp⟩
  have hpPspace : p ∈ (P.closedStar p).space := hside.symm.subset
    ⟨(K.closedStar p).vertices_subset_space hpKstar, by
      change 0 ≤ f p 0
      rw [hzero]⟩
  have hpPstar : p ∈ (P.closedStar p).vertices := by
    obtain ⟨s, hs, hps⟩ := mem_space_iff.mp hpPspace
    have hpins := (K.vertex_mem_convexHull_iff hp (hPK hs.1)).mp hps
    exact (P.closedStar p).down_closed hs (Finset.singleton_subset_iff.mpr hpins)
      (Finset.singleton_nonempty p)
  have hself : ((P.closedStar p).closedStar p).space = (P.closedStar p).space := by
    congr 1
    ext s
    change ((s ∈ P.faces ∧ insert p s ∈ P.faces) ∧
      insert p s ∈ P.faces ∧ insert p (insert p s) ∈ P.faces) ↔
      s ∈ P.faces ∧ insert p s ∈ P.faces
    simp only [Finset.insert_idem, and_self, and_assoc]
  have hlink : (P.closedStar p).link p = P.link p := by
    ext s
    change ((s ∈ P.faces ∧ insert p s ∈ P.faces) ∧ p ∉ s ∧
      insert p s ∈ P.faces ∧ insert p (insert p s) ∈ P.faces) ↔
      s ∈ P.faces ∧ p ∉ s ∧ insert p s ∈ P.faces
    simp only [Finset.insert_idem]
    tauto
  let a : (Fin 3 → ℝ) ≃ᴬ[ℝ] (Fin 3 → ℝ) :=
    ContinuousAffineEquiv.constVAdd ℝ (Fin 3 → ℝ) (-f p)
  let g : E → (Fin 3 → ℝ) := fun x => a (f x)
  have hg : (P.closedStar p).AffineOnFaces g :=
    (show (P.closedStar p).AffineOnFaces f from fun s hs => hf s (hstarle hs)).postcomp
      a.toContinuousAffineMap
  have hginj : InjOn g (P.closedStar p).space := fun _ hx _ hy he =>
    hinj (hstarsub hx) (hstarsub hy) (a.injective he)
  have hgp : g p = 0 := by
    change -f p + f p = 0
    exact neg_add_cancel _
  have hgheight (x : E) : g x 0 = f x 0 := by
    change -(f p 0) + f x 0 = f x 0
    rw [hzero, neg_zero, zero_add]
  let U := interior (g '' (K.closedStar p).space)
  have h0U : (0 : Fin 3 → ℝ) ∈ U := by
    change (0 : Fin 3 → ℝ) ∈ interior ((a ∘ f) '' (K.closedStar p).space)
    rw [image_comp]
    change (0 : Fin 3 → ℝ) ∈ interior (a.toHomeomorph '' (f '' (K.closedStar p).space))
    rw [← a.toHomeomorph.image_interior]
    exact ⟨f p, hint, hgp⟩
  let A : (Fin 3 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
  have hsideg : g '' (P.closedStar p).space ⊆ {x | 0 ≤ A x} := by
    rintro y ⟨x, hx, rfl⟩
    change 0 ≤ g x 0
    rw [hgheight]
    exact (hside.subset hx).2
  have hhalf : U ∩ {x | 0 ≤ A x} ⊆ g '' (P.closedStar p).space := by
    rintro y ⟨hyU, hypos⟩
    obtain ⟨x, hx, rfl⟩ := interior_subset hyU
    refine ⟨x, hside.symm.subset ⟨hx, ?_⟩, rfl⟩
    change 0 ≤ g x 0 at hypos
    rwa [hgheight] at hypos
  obtain ⟨C, H, hC, hcv, hC0, hpoly, hball, hH, hboundary, hmarks⟩ :=
    hg.exists_halfspace_star_ball (finite_closedStar_faces hP p) hginj hpPstar hgp
      hself A (fun _ => 1) (by norm_num [A]) hsideg
      (show IsOpen U from isOpen_interior) h0U hhalf (ContinuousLinearEquiv.refl ℝ _)
  refine ⟨C, fun _ => 1, H, rfl, hC, hcv, hC0, hpoly, ?_, hH, ?_, ?_⟩
  · simpa only [hlink, A, LinearMap.proj_apply, hgheight] using hball
  · intro x
    change (x : E) ∈ (P.link p).space ↔ (H x : Fin 3 → ℝ) ∈ frontier C
    rw [← hlink]
    exact hboundary x
  · intro x
    change (H x : Fin 3 → ℝ) 0 = 0 ↔ f x 0 = 0
    rw [← hgheight]
    exact hmarks x

end Geometry.SimplicialComplex
