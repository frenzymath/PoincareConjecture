import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierPLNormalization
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.CubeSectorSubdivision










set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in


theorem signedCubeCoordinate_ne_zero (i : ι ⊕ ι) : signedCubeCoordinate i ≠ 0 := by
  intro h
  have hv := congrArg (fun L : (ι → ℝ) →ₗ[ℝ] ℝ => L (fun _ => 1)) h
  cases i <;> simp [signedCubeCoordinate] at hv




theorem closedBall_eq_signedCube_halfspaces :
    Metric.closedBall (0 : ι → ℝ) 1 = {x | ∀ i, signedCubeCoordinate i x ≤ 1} := by
  ext x
  rw [Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro hx i
    exact (signedCubeCoordinate_le_norm i x).trans hx
  · intro hx
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    rw [Real.norm_eq_abs]
    have hp : x i ≤ 1 := hx (.inl i)
    have hn : -x i ≤ 1 := hx (.inr i)
    exact abs_le.mpr ⟨by linarith, hp⟩

end Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem IsCompact.exists_finitePL_cube_homeomorph {s : Set E} (hs : IsCompact s)
    (hcv : Convex ℝ s) (hne : (interior s).Nonempty)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hspace : K.space = s)
    {ι : Type*} [Fintype ι] [Nonempty ι] (c : E ≃L[ℝ] (ι → ℝ)) :
    ∃ e : s ≃ₜ Metric.closedBall (0 : ι → ℝ) 1, e.IsFinitePL ∧
      ∀ x : s, (x : E) ∈ frontier s ↔
        (e x : ι → ℝ) ∈ frontier (Metric.closedBall (0 : ι → ℝ) 1) := by
  classical
  obtain ⟨p, hp⟩ := hne
  let a : E ≃ᴬ[ℝ] (ι → ℝ) :=
    (ContinuousAffineEquiv.constVAdd ℝ E (-p)).trans c.toContinuousAffineEquiv
  have hap : a p = 0 := by change c (-p + p) = 0; simp
  let C := a '' s
  have hC : IsCompact C := hs.image a.continuous
  have hCcv : Convex ℝ C := hcv.affine_image a.toAffineEquiv.toAffineMap
  have hC0 : (0 : ι → ℝ) ∈ interior C := by
    change (0 : ι → ℝ) ∈ interior (a.toHomeomorph '' s)
    rw [← a.toHomeomorph.image_interior]
    exact ⟨p, hp, hap⟩
  have haff : K.AffineOnFaces a := K.affineOnFaces_affine a.toContinuousAffineMap
  let J := haff.embeddedImage a.injective.injOn
  have hJ : J.faces.Finite := haff.embeddedImage_finite _ hK
  have hJC : J.space = C := by rw [haff.embeddedImage_space, hspace]
  have hb := J.frontierSubcomplex_space hC.isClosed hCcv ⟨0, hC0⟩ hJC
  let T := Metric.closedBall (0 : ι → ℝ) 1
  have hT : IsCompact T := isCompact_closedBall _ _
  have hTcv : Convex ℝ T := convex_closedBall _ _
  have hT0 : (0 : ι → ℝ) ∈ interior T :=
    Metric.ball_subset_interior_closedBall (Metric.mem_ball_self zero_lt_one)
  obtain ⟨eb, heb⟩ := (J.frontierSubcomplex C).exists_finitePL_convex_frontier_halfspaces
    (J.frontierSubcomplex_finite C hJ) hC hT hCcv hTcv hC0 hT0 hb
    signedCubeCoordinate signedCubeCoordinate_ne_zero closedBall_eq_signedCube_halfspaces
  obtain ⟨H, hH, _, hHb⟩ := heb.exists_convex_extension hC hT hCcv hTcv
    ⟨0, hC0⟩ ⟨0, hT0⟩
  let ea := a.toHomeomorph.image s
  have hea : ea.IsFinitePL := ⟨a, ⟨K, hK, hspace, haff⟩, fun _ => rfl⟩
  refine ⟨ea.trans H, hea.trans hH, fun x => ?_⟩
  have hx : (x : E) ∈ frontier s ↔ (ea x : ι → ℝ) ∈ frontier C := by
    change (x : E) ∈ frontier s ↔ a x ∈ frontier (a.toHomeomorph '' s)
    rw [← a.toHomeomorph.image_frontier]
    exact a.injective.mem_set_image.symm
  exact hx.trans (hHb (ea x))

end Set
