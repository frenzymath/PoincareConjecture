import PoincareConjecture.Proofs.M76.Mathlib.ConvexCubeNormalization
import PoincareConjecture.Proofs.M76.Mathlib.LinearPoleCoordinates

set_option autoImplicit false

open Set Geometry
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_finitePL_convex_frontier_cube_pole (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {s : Set E} (hs : IsCompact s) (hcv : Convex ℝ s)
    (hne : (interior s).Nonempty) (hspace : K.space = frontier s)
    {ι : Type*} [Fintype ι] [Nonempty ι] (c : E ≃L[ℝ] (ι → ℝ))
    (p : frontier s) :
    ∃ e : frontier s ≃ₜ frontier (Metric.closedBall (0 : ι → ℝ) 1),
      e.IsFinitePL ∧ (e p : ι → ℝ) = fun _ => 1 := by
  classical
  obtain ⟨q, hq⟩ := hne
  let b : E ≃ᴬ[ℝ] (ι → ℝ) :=
    (ContinuousAffineEquiv.constVAdd ℝ E (-q)).trans c.toContinuousAffineEquiv
  have hbq : b q = 0 := by change c (-q + q) = 0; simp
  have hbp : b p ≠ 0 := by
    intro he
    have hpq : (p : E) = q := b.injective (he.trans hbq.symm)
    exact p.property.2 (hpq.symm ▸ hq)
  obtain ⟨u, hu⟩ := ContinuousLinearEquiv.exists_apply_eq_one hbp
  let a : E ≃ᴬ[ℝ] (ι → ℝ) := b.trans u.toContinuousAffineEquiv
  have hap : a p = fun _ => 1 := hu
  have haq : a q = 0 := by change u (b q) = 0; rw [hbq, map_zero]
  let C := a '' s
  have hC : IsCompact C := hs.image a.continuous
  have hCcv : Convex ℝ C := hcv.affine_image a.toAffineEquiv.toAffineMap
  have hC0 : (0 : ι → ℝ) ∈ interior C := by
    change (0 : ι → ℝ) ∈ interior (a.toHomeomorph '' s)
    rw [← a.toHomeomorph.image_interior]
    exact ⟨q, hq, haq⟩
  have hfa : a '' frontier s = frontier C := a.toHomeomorph.image_frontier s
  have haff : K.AffineOnFaces a := K.affineOnFaces_affine a.toContinuousAffineMap
  let J := haff.embeddedImage a.injective.injOn
  have hJ : J.faces.Finite := haff.embeddedImage_finite _ hK
  have hJC : J.space = frontier C := by
    rw [haff.embeddedImage_space, hspace, hfa]
  let T := Metric.closedBall (0 : ι → ℝ) 1
  have hT : IsCompact T := isCompact_closedBall _ _
  have hTcv : Convex ℝ T := convex_closedBall _ _
  have hT0 : (0 : ι → ℝ) ∈ interior T :=
    Metric.ball_subset_interior_closedBall (Metric.mem_ball_self zero_lt_one)
  have honeC : (fun _ : ι => (1 : ℝ)) ∈ frontier C := by
    rw [← hfa]
    exact ⟨p, p.property, hap⟩
  obtain ⟨e, he, hem⟩ := J.exists_finitePL_convex_frontier_halfspaces_marked hJ hC hT
    hCcv hTcv hC0 hT0 hJC signedCubeCoordinate signedCubeCoordinate_ne_zero
    closedBall_eq_signedCube_halfspaces {fun _ => 1} (by simpa using honeC)
  have honeT : (fun _ : ι => (1 : ℝ)) ∈ frontier T := by
    change (fun _ : ι => (1 : ℝ)) ∈ frontier (Metric.closedBall (0 : ι → ℝ) 1)
    rw [closedBall_eq_signedCube_halfspaces,
      frontier_finite_linear_unit_halfspaces (signedCubeCoordinate (ι := ι))
        (signedCubeCoordinate_ne_zero (ι := ι))]
    refine ⟨?_, .inl (Classical.arbitrary ι), rfl⟩
    intro i
    cases i <;> norm_num [signedCubeCoordinate]
  have hgauge : gauge T (fun _ : ι => (1 : ℝ)) = 1 :=
    (gauge_eq_one_iff_mem_frontier hTcv (mem_interior_iff_mem_nhds.mp hT0)).mpr honeT
  let ea := (a.toHomeomorph.image (frontier s)).trans (Homeomorph.setCongr hfa)
  have hea : ea.IsFinitePL := by
    have h : (a.toHomeomorph.image (frontier s)).IsFinitePL :=
      ⟨a, ⟨K, hK, hspace, haff⟩, fun _ => rfl⟩
    exact h.setCongr rfl hfa
  refine ⟨ea.trans e, hea.trans he, ?_⟩
  have heamp : (ea p : ι → ℝ) = fun _ => 1 := hap
  have hepm := hem (ea p) (by simp only [heamp, Finset.mem_singleton])
  change (e (ea p) : ι → ℝ) = fun _ => 1
  rw [hepm, heamp, hgauge, inv_one, one_smul]

end Geometry.SimplicialComplex
