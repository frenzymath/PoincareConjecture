import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage
import PoincareConjecture.Proofs.M76.Mathlib.PolygonConvexContainment
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLDisk
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.RelativeSetInteriors

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_polygon_subdisk_with_interior {d q : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hsub : P.boundary ℝ ⊆ d \ q) :
    ∃ D : Set E, IsFinitePLBallPair (ℝ × ℝ) D (P.boundary ℝ) ∧ D ⊆ d \ q ∧
      interior ((Subtype.val : d → E) ⁻¹' D) =
        (Subtype.val : d → E) ⁻¹' (D \ P.boundary ℝ) := by
  obtain ⟨_, C, _, hCcv, _, e, he, heb⟩ := hd
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
  have hgmap (y : ℝ × ℝ) (hy : y ∈ C) : g y ∈ d := by
    rw [← hgval ⟨y, hy⟩]
    exact (e.symm ⟨y, hy⟩).property
  have hPsub : P.boundary ℝ ⊆ d := hsub.trans sdiff_subset
  obtain ⟨N, R, hRi, hRs, hRb⟩ := P.exists_polygon_finitePL_image hP hinj hf hPsub
    (hgf.injOn.mono hPsub)
  have hRint : R.boundary ℝ ⊆ interior C := by
    rw [hRb]
    rintro _ ⟨x, hx, rfl⟩
    by_contra hnot
    have hfront : f x ∈ frontier C := ⟨subset_closure (hfmap x (hPsub hx)), hnot⟩
    have hq := (heb ⟨x, hPsub hx⟩).mpr (by rwa [heval])
    exact (hsub hx).2 hq
  have hDint : closure R.inside ⊆ interior C := R.closure_inside_subset_convex hRs hRi
    hCcv.interior (by
      rintro _ ⟨i, rfl⟩
      exact hRint (mem_iUnion.mpr ⟨i, left_mem_affineSegment ℝ _ _⟩))
  have hDC : closure R.inside ⊆ C := hDint.trans interior_subset
  obtain ⟨J, hJ⟩ := R.exists_triangulation hRs hRi
  have hgD : FinitePiecewiseAffineOn g (closure R.inside) := by
    rw [← hJ.space_eq]
    exact hg.restrict J hJ.finite_faces (hJ.space_eq.subset.trans hDC)
  have hboundary : g '' R.boundary ℝ = P.boundary ℝ := by
    rw [hRb]
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩
      rw [hgf (hPsub hy)] at hxy
      exact hxy ▸ hy
    · intro hx
      exact ⟨f x, mem_image_of_mem f hx, hgf (hPsub hx)⟩
  have hpair := (R.isFinitePLBallPair_closed_inside hRs hRi).image hgD (hfg.injOn.mono hDC)
  rw [hboundary] at hpair
  refine ⟨g '' closure R.inside, hpair, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨hgmap y (hDC hy), ?_⟩
    intro hq
    have hfront := (heb ⟨g y, hgmap y (hDC hy)⟩).mp hq
    rw [heval, hfg (hDC hy)] at hfront
    exact hfront.2 (hDint hy)
  · have himage {b : Set (ℝ × ℝ)} (hb : b ⊆ C) :
        (Subtype.val : d → E) ⁻¹' (g '' b) = e ⁻¹' ((Subtype.val : C → (ℝ × ℝ)) ⁻¹' b) := by
      ext x
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hexy : (e x : ℝ × ℝ) = y := by
          rw [heval, ← hyx, hfg (hb hy)]
        change (e x : ℝ × ℝ) ∈ b
        rwa [hexy]
      · intro hx
        refine ⟨e x, hx, ?_⟩
        rw [← hgval (e x), e.symm_apply_apply]
    have hBC : R.boundary ℝ ⊆ C :=
      (R.isFinitePLBallPair_closed_inside hRs hRi).1.trans hDC
    have hregion : closure R.inside \ R.boundary ℝ = R.inside := by
      rw [← R.frontier_closure_inside hRs hRi, self_sdiff_frontier,
        R.interior_closure_inside hRs hRi]
    calc
      interior ((Subtype.val : d → E) ⁻¹' (g '' closure R.inside)) =
          e ⁻¹' ((Subtype.val : C → (ℝ × ℝ)) ⁻¹' R.inside) := by
        rw [himage hDC, ← e.preimage_interior,
          interior_preimage_val_of_subset_interior hDint, R.interior_closure_inside hRs hRi]
      _ = (Subtype.val : d → E) ⁻¹' (g '' closure R.inside \ P.boundary ℝ) := by
        rw [preimage_sdiff, ← hboundary, himage hDC, himage hBC,
          ← preimage_sdiff, ← preimage_sdiff, hregion]

theorem IsFinitePLBallPair.exists_polygon_subdisk {d q : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hsub : P.boundary ℝ ⊆ d \ q) :
    ∃ D : Set E, IsFinitePLBallPair (ℝ × ℝ) D (P.boundary ℝ) ∧ D ⊆ d \ q := by
  obtain ⟨D, hD, hDd, _⟩ := hd.exists_polygon_subdisk_with_interior P hP hinj hsub
  exact ⟨D, hD, hDd⟩

end Set
