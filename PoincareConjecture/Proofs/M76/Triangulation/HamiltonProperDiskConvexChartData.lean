import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskParameterPieces
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.CompactLocallyPLComposition
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "Cube" => closedBall (0 : V2) 1

noncomputable def diskChartCoordinates : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] V :=
  ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.prodCongr
    (ContinuousLinearEquiv.refl ℝ ℝ)).toContinuousAffineEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : Cube ≃ₜ D}

theorem HamiltonProperDiskTriangulation.exists_convex_chart_restrictions
    (T : HamiltonProperDiskTriangulation R D b) (hb : b.IsFinitePL)
    (p : T.disk.vertices) (c : E ≃ᴬ[ℝ] V) :
    ∃ (F : V2 → E) (K : SimplicialComplex ℝ V)
      (Q L : SimplicialComplex ℝ V2),
      (∀ x : Cube, F x = (b x : E)) ∧
      K.faces.Finite ∧ Convex ℝ K.space ∧ c p ∈ interior K.space ∧
      (∀ x ∈ K.space, c.symm x ∈ (T.pairChart p).chart.source) ∧
      K.AffineOnFaces (fun x => diskChartCoordinates ((T.pairChart p).chart (c.symm x))) ∧
      InjOn (fun x => diskChartCoordinates ((T.pairChart p).chart (c.symm x))) K.space ∧
      Q.faces.Finite ∧ Convex ℝ Q.space ∧ T.inverse p ∈ interior Q.space ∧
      L.faces.Finite ∧ L.space = Q.space ∩ Cube ∧ Convex ℝ L.space ∧
      (interior L.space).Nonempty ∧
      (∀ x ∈ L.space, F x ∈ (T.pairChart p).chart.source) ∧
      L.AffineOnFaces (fun x => (diskChartCoordinates ((T.pairChart p).chart (F x))).1) ∧
      InjOn (fun x => (diskChartCoordinates ((T.pairChart p).chart (F x))).1) L.space := by
  classical
  let H := (T.pairChart p).chart
  have hpK : (p : E) ∈ T.ambient.vertices := T.disk_le p.property
  change {(p : E)} ∈ T.ambient.faces at hpK
  have hpstar : {(p : E)} ∈ (T.ambient.closedStar p).faces := by
    exact ⟨hpK, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]
      using hpK⟩
  have hpH : (p : E) ∈ H.source := T.star_source p
    ((T.ambient.closedStar p).subset_space hpstar (by simp))
  have hpD : (p : E) ∈ D := T.disk_space.subset
    (T.disk.vertices_subset_space p.property)
  obtain ⟨F, hF, hbF⟩ := hb
  have hFb (x : Cube) : F x = (b x : E) := (hbF x).symm
  let z : Cube := b.symm ⟨p, hpD⟩
  have hz : T.inverse p = (z : V2) := T.inverse_eq ⟨p, hpD⟩
  have hFz : F z = p := (hFb z).trans
    (congrArg Subtype.val (b.apply_symm_apply ⟨p, hpD⟩))
  let U : Set V := c.symm ⁻¹' H.source
  have hU : IsOpen U := H.open_source.preimage c.symm.continuous
  have hpU : c p ∈ U := by
    change c.symm (c p) ∈ H.source
    rwa [c.symm_apply_apply]
  obtain ⟨K0, hK0, hKcv, hpK0, hK0U⟩ := hU.exists_finite_convex_neighborhood hpU
  have hc : FinitePiecewiseAffineOn c.symm K0.space :=
    (K0.affineOnFaces_affine c.symm.toContinuousAffineMap).finitePiecewiseAffineOn hK0
  have hambient : FinitePiecewiseAffineOn
      (fun x => diskChartCoordinates (H (c.symm x))) K0.space :=
    ((T.pairChart p).piecewiseAffine.comp_finitePiecewiseAffineOn hc hK0U).postcomp
      diskChartCoordinates.toContinuousAffineMap
  obtain ⟨K, hK, hKK0, hKaff⟩ := hambient
  have hKi : InjOn (fun x => diskChartCoordinates (H (c.symm x))) K.space := by
    intro x hx y hy hxy
    exact c.symm.injective (H.injOn (hK0U (hKK0.subset hx))
      (hK0U (hKK0.subset hy)) (diskChartCoordinates.injective hxy))
  obtain ⟨W, hW, hWset⟩ := continuousOn_iff'.mp hF.continuousOn H.source H.open_source
  have hzW : (z : V2) ∈ W := (hWset.subset ⟨by
    change F z ∈ H.source
    rwa [hFz], z.property⟩).1
  obtain ⟨Q, hQ, hQcv, hzQ, hQW⟩ := hW.exists_finite_convex_neighborhood hzW
  have hFcopy := hF
  obtain ⟨J, hJ, hJspace, _⟩ := hFcopy
  obtain ⟨L0, hL0, hL0s⟩ := Q.exists_finite_triangulation_inter J hQ hJ
  have hL0space : L0.space = Q.space ∩ Cube := by rwa [hJspace] at hL0s
  have hL0Cube : L0.space ⊆ Cube := hL0space.subset.trans inter_subset_right
  have hFL0 : FinitePiecewiseAffineOn F L0.space := hF.restrict L0 hL0 hL0Cube
  have hmap : MapsTo F L0.space H.source := by
    intro x hx
    have hx' := hL0space.subset hx
    exact (hWset.symm.subset ⟨hQW hx'.1, hx'.2⟩).1
  let a : ((ℝ × ℝ) × ℝ) →ᴬ[ℝ] V2 :=
    (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.comp
      diskChartCoordinates.toContinuousAffineMap
  have htangent : FinitePiecewiseAffineOn
      (fun x => (diskChartCoordinates (H (F x))).1) L0.space :=
    ((T.pairChart p).piecewiseAffine.comp_finitePiecewiseAffineOn hFL0 hmap).postcomp a
  obtain ⟨L, hL, hLL0, hLaff⟩ := htangent
  have hLs : L.space = Q.space ∩ Cube := hLL0.trans hL0space
  have hLcv : Convex ℝ L.space := by
    rw [hLs]
    exact hQcv.inter (convex_closedBall (0 : V2) 1)
  have hCubeint : (interior Cube).Nonempty := by
    rw [interior_closedBall (0 : V2) one_ne_zero]
    exact ⟨0, mem_ball_self zero_lt_one⟩
  have hzcl : (z : V2) ∈ closure (interior Cube) := by
    rw [(convex_closedBall (0 : V2) 1).closure_interior_eq_closure_of_nonempty_interior
      hCubeint, isClosed_closedBall.closure_eq]
    exact z.property
  obtain ⟨y, hyQ, hyCube⟩ := mem_closure_iff.mp hzcl (interior Q.space) isOpen_interior hzQ
  have hLint : (interior L.space).Nonempty := by
    rw [hLs, interior_inter]
    exact ⟨y, hyQ, hyCube⟩
  have hFdisk (x : V2) (hx : x ∈ L.space) : F x ∈ D := by
    rw [hFb ⟨x, (hLs.subset hx).2⟩]
    exact (b ⟨x, (hLs.subset hx).2⟩).property
  have hzero (x : V2) (hx : x ∈ L.space) : (H (F x)).2 = 0 := by
    have hxH := hmap (hLL0.subset hx)
    rcases (T.pairChart p).model with ⟨_, hplane⟩ | ⟨_, hplane⟩
    · exact (hplane (F x) hxH).mp (hFdisk x hx)
    · exact ((hplane (F x) hxH).mp (hFdisk x hx)).2
  have hLi : InjOn (fun x => (diskChartCoordinates (H (F x))).1) L.space := by
    intro x hx y hy hxy
    have hcoords : diskChartCoordinates (H (F x)) = diskChartCoordinates (H (F y)) := by
      apply Prod.ext hxy
      change (H (F x)).2 = (H (F y)).2
      rw [hzero x hx, hzero y hy]
    have hFx : F x = F y := H.injOn (hmap (hLL0.subset hx))
      (hmap (hLL0.subset hy)) (diskChartCoordinates.injective hcoords)
    have hbxy : b ⟨x, (hLs.subset hx).2⟩ = b ⟨y, (hLs.subset hy).2⟩ := by
      apply Subtype.ext
      exact (hFb ⟨x, (hLs.subset hx).2⟩).symm.trans
        (hFx.trans (hFb ⟨y, (hLs.subset hy).2⟩))
    exact congrArg Subtype.val (b.injective hbxy)
  refine ⟨F, K, Q, L, hFb, hK, ?_, ?_, ?_, hKaff, hKi,
    hQ, hQcv, ?_, hL, hLs, hLcv, hLint, ?_, hLaff, hLi⟩
  · rwa [hKK0]
  · rwa [hKK0]
  · exact fun x hx => hK0U (hKK0.subset hx)
  · rwa [hz]
  · exact fun x hx => hmap (hLL0.subset hx)

end PoincareConjecture.M76.HamiltonIndexOne
