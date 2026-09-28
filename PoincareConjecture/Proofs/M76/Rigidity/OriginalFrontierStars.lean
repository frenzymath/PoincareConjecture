import PoincareConjecture.Proofs.M76.Rigidity.OriginalBoundaryMembership
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarInteriorBall

set_option autoImplicit false

open Set Metric Geometry Filter
open scoped Topology

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "P2" => (ℝ × ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in

theorem exists_frontier_star_plane_chart (p : (T.marked 2).vertices)
    (hpfront : (T.inverse p : X) ∈ frontier R) :
    ∃ f : (T.index → ℝ × V3) → P2,
      ((T.marked 1).closedStar p).AffineOnFaces f ∧
      InjOn f ((T.marked 1).closedStar p).space ∧
      f p ∈ interior (f '' ((T.marked 1).closedStar p).space) ∧
      ∀ x, f x = ((T.chart (T.chart_index p) (T.inverse x)).1.2,
        (T.chart (T.chart_index p) (T.inverse x)).2) := by
  classical
  let H := T.chart (T.chart_index p)
  let S := (T.marked 1).closedStar p
  have hpK : (p : T.index → ℝ × V3) ∈ T.ambient.vertices := T.marked_le 2 p.property
  have hpKs := T.ambient.vertices_subset_space hpK
  have hpH : (T.inverse p : X) ∈ H.source := T.star_source p
    ((T.ambient.closedStar p).vertices_subset_space
      ⟨hpK, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]
        using (show {p.val} ∈ T.ambient.faces from hpK)⟩)
  have hhalf : ∀ x ∈ H.source, x ∈ R ↔ 0 ≤ (H x).1.1 := by
    rcases T.chart_model (T.chart_index p) with ⟨hinside, _⟩ | ⟨hhalf, _⟩
    · exact False.elim (hpfront.2 (hinside hpH))
    · exact hhalf
  let ell : C3 →L[ℝ] ℝ :=
    { toFun := fun z => z.1.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := by fun_prop }
  let rho : C3 →L[ℝ] P2 :=
    { toFun := fun z => (z.1.2, z.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := by fun_prop }
  let a : P2 →L[ℝ] C3 :=
    { toFun := fun z => ((0, z.1), z.2)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp
      cont := by fun_prop }
  have hell : ell.toContinuousAffineMap.toAffineMap.linear ≠ 0 := by
    intro he
    have h := congrArg (fun m : C3 →ₗ[ℝ] ℝ => m ((1, 0), 0)) he
    change (1 : ℝ) = 0 at h
    exact one_ne_zero h
  have hfront := H.isImage_frontier_of_affine_nonneg ell.toContinuousAffineMap hell hhalf
  let x0 : frontier R := ⟨T.inverse p, hpfront⟩
  obtain ⟨q, hqs, _, hqval, _⟩ := H.exists_affine_hypersurface_chart
    ell.toContinuousAffineMap hfront a.toContinuousAffineMap rho.toContinuousAffineMap
    (fun _ => rfl) (by
      intro z hz
      change ((0, z.1.2), z.2) = z
      exact Prod.ext (Prod.ext hz.symm rfl) rfl)
    (fun _ => rfl) x0
  have hSstar : S ≤ T.ambient.closedStar p :=
    fun _ hs => ⟨T.marked_le 1 hs.1, T.marked_le 1 hs.2⟩
  have hSbound : S ≤ T.marked 1 := fun _ hs => hs.1
  have hSK : S.space ⊆ T.ambient.space :=
    SimplicialComplex.space_subset_of_le (hSbound.trans (T.marked_le 1))
  have hSS : MapsTo (fun x => (T.inverse x : X)) S.space H.source :=
    fun _ hx => T.star_source p (SimplicialComplex.space_subset_of_le hSstar hx)
  have hSF : MapsTo (fun x => (T.inverse x : X)) S.space (frontier R) :=
    fun _ hx => (T.inverse_mem_boundary_iff (hSK hx)).mpr
      (SimplicialComplex.space_subset_of_le hSbound hx)
  let f : (T.index → ℝ × V3) → P2 := fun x => rho (H (T.inverse x))
  have hf : S.AffineOnFaces f :=
    (show S.AffineOnFaces (fun x => H (T.inverse x)) from
      fun t ht => T.star_affine p t (hSstar ht)).postcomp rho.toContinuousAffineMap
  have hfi : InjOn f S.space := by
    intro x hx y hy hxy
    change ((H (T.inverse x)).1.2, (H (T.inverse x)).2) =
      ((H (T.inverse y)).1.2, (H (T.inverse y)).2) at hxy
    have hxzero := (hfront.apply_mem_iff (hSS hx)).mpr (hSF hx)
    have hyzero := (hfront.apply_mem_iff (hSS hy)).mpr (hSF hy)
    apply T.star_injective p (SimplicialComplex.space_subset_of_le hSstar hx)
      (SimplicialComplex.space_subset_of_le hSstar hy)
    exact Prod.ext (Prod.ext (hxzero.trans hyzero.symm)
      (congrArg (fun z : P2 => z.1) hxy)) (congrArg (fun z : P2 => z.2) hxy)
  have hpB : (p : T.index → ℝ × V3) ∈ (T.marked 1).vertices :=
    (SimplicialComplex.vertex_mem_subcomplex_space_iff (T.marked_le 1) hpK).mp
      ((T.inverse_mem_boundary_iff hpKs).mp hpfront)
  obtain ⟨r, hr, hrS⟩ := (T.marked 1).exists_ball_inter_space_subset_closedStar
    (T.marked_finite 1) hpB
  have hFp : T.graph x0 = (p : T.index → ℝ × V3) := by
    change T.graph (T.inverse p) = _
    rw [T.inverse_eq ⟨p, hpKs⟩, ← T.model_eq (T.model.symm ⟨p, hpKs⟩),
      T.model.apply_symm_apply]
  have hF : Continuous (fun x : frontier R => T.graph x) :=
    T.graph_continuous.comp continuous_subtype_val
  have hN : (fun x : frontier R => T.graph x) ⁻¹' S.space ∈ 𝓝 x0 := by
    have hb : ball (p : T.index → ℝ × V3) r ∈ 𝓝 (T.graph x0) := by
      rw [hFp]
      exact ball_mem_nhds _ hr
    apply Filter.mem_of_superset (hF.continuousAt.preimage_mem_nhds hb)
    intro x hx
    exact hrS ⟨T.boundary_space.symm.subset ⟨x, x.property, rfl⟩, hx⟩
  have hpq : x0 ∈ q.source := by
    rw [hqs]
    exact hpH
  have hqint : q x0 ∈ interior (q '' ((fun x : frontier R => T.graph x) ⁻¹' S.space)) :=
    mem_interior_iff_mem_nhds.mpr (q.image_mem_nhds hpq hN)
  have himage : q '' ((fun x : frontier R => T.graph x) ⁻¹' S.space) ⊆ f '' S.space := by
    rintro _ ⟨x, hx, rfl⟩
    have hxC : (x : X) ∈ T.neighborhood := T.frontier_subset_neighborhood x.property
    have hFx : (T.model ⟨x, hxC⟩ : T.index → ℝ × V3) = T.graph x :=
      T.model_eq ⟨x, hxC⟩
    have hInv : (T.inverse (T.graph x) : X) = (x : X) := by
      rw [← hFx, T.inverse_eq (T.model ⟨x, hxC⟩), T.model.symm_apply_apply]
    refine ⟨T.graph x, hx, ?_⟩
    change rho (H (T.inverse (T.graph x))) = q x
    rw [hInv, hqval]
    rfl
  refine ⟨f, hf, hfi, ?_, fun _ => rfl⟩
  have hint := interior_mono himage hqint
  simpa only [hqval, ContinuousLinearMap.coe_toContinuousAffineMap, x0, f, S] using hint

end PoincareConjecture.M76.OriginalProperDiskTriangulation
