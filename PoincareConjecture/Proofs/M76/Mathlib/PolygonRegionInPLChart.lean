import PoincareConjecture.Proofs.M76.Mathlib.PolygonPLSubdisk
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.of_polygon_region {d q A U : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hAc : IsCompact A) (hA : A ⊆ d \ q) (hcl : closure U = A)
    (hint : interior ((Subtype.val : d → E) ⁻¹' A) = (Subtype.val : d → E) ⁻¹' U)
    (hbound : A \ U = P.boundary ℝ) (hne : U.Nonempty) :
    IsFinitePLBallPair (ℝ × ℝ) A (P.boundary ℝ) := by
  have hUA : U ⊆ A := hcl ▸ subset_closure
  have hAd : A ⊆ d := hA.trans sdiff_subset
  have hUd : U ⊆ d := hUA.trans hAd
  have hBA : P.boundary ℝ ⊆ A := by rw [← hbound]; exact sdiff_subset
  have hBd : P.boundary ℝ ⊆ d := hBA.trans hAd
  obtain ⟨_, C, _, _, _, e, he, heb⟩ := hd
  have hecopy := he
  obtain ⟨f, hf, heval⟩ := hecopy
  obtain ⟨g, hg, hgval⟩ := he.symm
  have hgf : LeftInvOn g f d := by
    intro x hx
    rw [← heval ⟨x, hx⟩, ← hgval, e.symm_apply_apply]
  have hfg : LeftInvOn f g C := by
    intro y hy
    rw [← hgval ⟨y, hy⟩, ← heval, e.apply_symm_apply]
  have hfmap (x : E) (hx : x ∈ d) : f x ∈ C := by
    rw [← heval ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  have hpre {b : Set E} (hb : b ⊆ d) :
      (Subtype.val : C → (ℝ × ℝ)) ⁻¹' (f '' b) =
        e.symm ⁻¹' ((Subtype.val : d → E) ⁻¹' b) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      change (e.symm y : E) ∈ b
      rw [hgval, ← hxy, hgf (hb hx)]
      exact hx
    · intro hy
      refine ⟨e.symm y, hy, ?_⟩
      rw [← heval (e.symm y), e.apply_symm_apply]
  have hYint : f '' A ⊆ interior C := by
    rintro _ ⟨x, hx, rfl⟩
    by_contra hnot
    have hfront : f x ∈ frontier C := ⟨subset_closure (hfmap x (hAd hx)), hnot⟩
    have hq := (heb ⟨x, hAd hx⟩).mpr (by rwa [heval])
    exact (hA hx).2 hq
  have hYC : f '' A ⊆ C := hYint.trans interior_subset
  have hVC : f '' U ⊆ C := (image_mono hUA).trans hYC
  have hYinterior : interior (f '' A) = f '' U := by
    have hrel : interior ((Subtype.val : C → (ℝ × ℝ)) ⁻¹' (f '' A)) =
        (Subtype.val : C → (ℝ × ℝ)) ⁻¹' (f '' U) := by
      rw [hpre hAd, ← e.symm.preimage_interior, hint, ← hpre hUd]
    rw [interior_preimage_val_of_subset_interior hYint] at hrel
    have heq := congrArg (fun b : Set C => (Subtype.val : C → (ℝ × ℝ)) '' b) hrel
    rwa [image_preimage_eq_of_subset (by
      simpa using (interior_subset.trans hYC : interior (f '' A) ⊆ C)),
      image_preimage_eq_of_subset (by simpa using hVC)] at heq
  have hYc : IsCompact (f '' A) := hAc.image_of_continuousOn (hf.continuousOn.mono hAd)
  have hVcl : closure (f '' U) = f '' A := by
    apply Subset.antisymm (closure_minimal (image_mono hUA) hYc.isClosed)
    have hc : ContinuousOn f (closure U) := by
      rw [hcl]
      exact hf.continuousOn.mono hAd
    simpa only [hcl] using hc.image_closure
  obtain ⟨N, R, hRi, hRs, hRb⟩ :=
    P.exists_polygon_finitePL_image hP hinj hf hBd (hgf.injOn.mono hBd)
  have hVo : IsOpen (f '' U) := hYinterior ▸ isOpen_interior
  have hfront : frontier (f '' U) = R.boundary ℝ := by
    rw [frontier, hVcl, hVo.interior_eq,
      ← (hgf.injOn.mono hAd).image_sdiff_subset hUA, hbound, ← hRb]
  have hinside : R.inside = f '' U := R.inside_eq_of_open_bounded_frontier hRs hRi
    hVo (hYc.isBounded.subset (image_mono hUA)) (hne.image f) hfront
  have hfill : closure R.inside = f '' A := by rw [hinside, hVcl]
  obtain ⟨J, hJ⟩ := R.exists_triangulation hRs hRi
  have hgD : FinitePiecewiseAffineOn g (closure R.inside) := by
    rw [← hJ.space_eq]
    apply hg.restrict J hJ.finite_faces
    rw [hJ.space_eq, hfill]
    exact hYC
  have hDC : closure R.inside ⊆ C := by rwa [hfill]
  have hback {b : Set E} (hb : b ⊆ d) : g '' (f '' b) = b := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩
      rw [hgf (hb hy)] at hxy
      exact hxy ▸ hy
    · intro hx
      exact ⟨f x, mem_image_of_mem f hx, hgf (hb hx)⟩
  have hpair := (R.isFinitePLBallPair_closed_inside hRs hRi).image hgD (hfg.injOn.mono hDC)
  rwa [hfill, hRb, hback hAd, hback hBd] at hpair

end Set
