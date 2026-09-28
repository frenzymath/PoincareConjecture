import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.BoundaryConeCaps
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryPieceGluing
import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

open Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem exists_disk_rim_circle_chart {d q : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) :
    ∃ b : sphere (0 : Fin 2 → ℝ) 1 ≃ₜ q, b.IsFinitePL := by
  obtain ⟨e, he, heb⟩ := hd.exists_cube_chart (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  let C := closedBall (0 : Fin 2 → ℝ) 1
  have hmem (x : C) : (x : Fin 2 → ℝ) ∈ sphere (0 : Fin 2 → ℝ) 1 ↔
      (e.symm x : E) ∈ q := by
    have h := heb (e.symm x)
    rw [e.apply_symm_apply, frontier_closedBall _ one_ne_zero] at h
    exact h.symm
  let b := e.symm.restrictSubsets sphere_subset_closedBall hd.1 hmem
  have htri := he.symm
  obtain ⟨_, ⟨J, hJ, hJs, _⟩, _⟩ := htri
  have hfront : (J.frontierSubcomplex C).space = sphere (0 : Fin 2 → ℝ) 1 := by
    rw [J.frontierSubcomplex_space (isCompact_closedBall _ _).isClosed
      (convex_closedBall _ _) ⟨0, ball_subset_interior_closedBall
        (mem_ball_self zero_lt_one)⟩ hJs, frontier_closedBall _ one_ne_zero]
  exact ⟨b, he.symm.restrictSubsets sphere_subset_closedBall hd.1 hmem
    (J.frontierSubcomplex C) (J.frontierSubcomplex_finite C hJ) hfront⟩


theorem exists_disk_cap_homeomorph {d q : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) :
    ∃ H : d ≃ₜ boundaryCircleCap true q, H.IsFinitePL ∧
      (∀ x : q, (H ⟨x, hd.1 x.property⟩ : E × ℝ) = ((x : E), 0)) ∧
      (∀ x : d, (x : E) ∈ q ↔ (H x : E × ℝ) ∈ q ×ˢ {(0 : ℝ)}) := by
  obtain ⟨b, hb⟩ := exists_disk_rim_circle_chart hd
  have hcap := (isFinitePLBallPair_boundaryCircleCap true b hb).model_equiv
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have hbcopy := hb.symm
  obtain ⟨_, ⟨Q, hQ, hQq, _⟩, _⟩ := hbcopy
  let I : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have hI : FinitePiecewiseAffineOn I q := ⟨Q, hQ, hQq, Q.affineOnFaces_affine I⟩
  obtain ⟨e, he, heval⟩ := hI.exists_homeomorph_image
    (fun x _ y _ h ↦ congrArg Prod.fst h)
  have him : I '' q = q ×ˢ {(0 : ℝ)} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, rfl⟩
    · rintro ⟨hz, hz0⟩
      exact ⟨z.1, hz, Prod.ext rfl hz0.symm⟩
  let eb := e.trans (Homeomorph.setCongr him)
  have heb : eb.IsFinitePL := he.setCongr rfl him
  obtain ⟨H, hH, hHb, hHmem⟩ := hd.exists_extension hcap eb heb
  refine ⟨H, hH, ?_, hHmem⟩
  intro x
  exact (congrArg Subtype.val (hHb x)).trans (heval x)


theorem exists_primal_disk_replacement {d q c : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (hinter : d ∩ c = q)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJc : J.space = c) :
    ∃ H : (d ∪ c : Set E) ≃ₜ (boundaryCircleCap true q ∪ (c ×ˢ {(0 : ℝ)}) : Set (E × ℝ)),
      H.IsFinitePL ∧
      (∀ x : c, (H ⟨x, Or.inr x.property⟩ : E × ℝ) = ((x : E), 0)) ∧
      (∀ x : (d ∪ c : Set E), (x : E) ∈ d ↔
        (H x : E × ℝ) ∈ boundaryCircleCap true q) ∧
      (∀ x : (d ∪ c : Set E), (x : E) ∈ c ↔
        (H x : E × ℝ) ∈ c ×ˢ {(0 : ℝ)}) := by
  obtain ⟨b, hb⟩ := exists_disk_rim_circle_chart hd
  have hcap := (isFinitePLBallPair_boundaryCircleCap true b hb).model_equiv
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have hqc : q ⊆ c := by rw [← hinter]; exact inter_subset_right
  have hInter : boundaryCircleCap true q ∩ (c ×ˢ {(0 : ℝ)}) = q ×ˢ {(0 : ℝ)} := by
    apply Subset.antisymm
    · intro x hx
      exact (boundaryCircleCap_plane true q).subset ⟨hx.1, mem_univ _, hx.2.2⟩
    · intro x hx
      exact ⟨((boundaryCircleCap_plane true q).symm.subset hx).1, hqc hx.1, hx.2⟩
  let I : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have hI : FinitePiecewiseAffineOn I c := ⟨J, hJ, hJc, J.affineOnFaces_affine I⟩
  obtain ⟨e, he, heval⟩ := hI.exists_homeomorph_image
    (fun x _ y _ h ↦ congrArg Prod.fst h)
  have him : I '' c = c ×ˢ {(0 : ℝ)} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, rfl⟩
    · rintro ⟨hz, hz0⟩
      exact ⟨z.1, hz, Prod.ext rfl hz0.symm⟩
  let ec := e.trans (Homeomorph.setCongr him)
  have hec : ec.IsFinitePL := he.setCongr rfl him
  have hmem (x : c) : (x : E) ∈ q ↔ (ec x : E × ℝ) ∈ q ×ˢ {(0 : ℝ)} := by
    change (x : E) ∈ q ↔ (e x : E × ℝ) ∈ q ×ˢ {(0 : ℝ)}
    rw [heval x]
    exact ⟨fun h ↦ ⟨h, rfl⟩, fun h ↦ h.1⟩
  obtain ⟨H, hH, hkeep, hHd, hHc⟩ :=
    hd.exists_union_homeomorph_of_boundary_piece hcap hinter hInter ec hec hmem
  refine ⟨H, hH, ?_, hHd, hHc⟩
  intro x
  exact (congrArg Subtype.val (hkeep x)).trans (heval x)

end PoincareConjecture.M76.OriginalTriangleCopies
