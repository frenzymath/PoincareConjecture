import PoincareConjecture.Proofs.M76.Mathlib.NonnegativeDirectionalIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPLTransport
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralRefinement

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76

theorem convex_inward_translation_of_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hC : Convex ℝ C) {y w x : E} {r t : ℝ}
    (hw : ball w r ⊆ interior C) (hx : x ∈ C) (hxy : x ∈ ball y r)
    (ht : t ∈ Ioo (0 : ℝ) 1) : x + t • (w - y) ∈ interior C := by
  have hnear : w + (x - y) ∈ ball w r := by
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left] using hxy
  have hsegment := hC.openSegment_self_interior_subset_interior hx (hw hnear)
  have hpoint : x + t • (w - y) = AffineMap.lineMap x (w + (x-y)) t := by
    rw [AffineMap.lineMap_apply_module]
    module
  rw [hpoint]
  exact hsegment (by rw [openSegment_eq_image_lineMap]; exact mem_image_of_mem _ ht)

theorem exists_supported_convex_plane_push
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C U : Set E} (hC : Convex ℝ C) (hU : IsOpen U) {y w : E}
    (hy : y ∈ C) (hyU : y ∈ U) (hw : w ∈ interior C)
    (A : E →ᵃ[ℝ] ℝ) (hAw : A w = A y) :
    ∃ H : E ≃ₜ E,
      (∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
        FinitePiecewiseAffineOn (H : E → E) K.space) ∧
      (∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
        FinitePiecewiseAffineOn (H.symm : E → E) K.space) ∧
      EqOn H id Uᶜ ∧ (∀ x, A (H x) = A x) ∧
      (∀ x ∈ C, H x ∈ interior C ∨ H x = x) ∧ H y ∈ interior C := by
  classical
  obtain ⟨r,hr,hrC⟩ := Metric.isOpen_iff.mp isOpen_interior w hw
  let V := U ∩ ball y r
  have hV : IsOpen V := hU.inter isOpen_ball
  have hyV : y ∈ V := ⟨hyU,mem_ball_self hr⟩
  obtain ⟨L,hL,hyL,hLV⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed isCompact_singleton
      hV (singleton_subset_iff.mpr hyV)
  have hf : FinitePiecewiseAffineOn (fun _ : E => (1 : ℝ)) L.space :=
    ⟨L,hL,rfl,L.affineOnFaces_affine (ContinuousAffineMap.const ℝ E 1)⟩
  have hzero : ∀ x ∈ L.space ∩ (⊥ : SimplicialComplex ℝ E).space, (1 : ℝ) = 0 := by
    simp [SimplicialComplex.space_bot]
  obtain ⟨g,hgn,hgf,_,hgV,ε,hε,F,_,_,hF,K,hK,_,_,hg,hgK,_,hPL⟩ :=
    hf.exists_nonnegative_directional_isotopy_with_global_finitePL
      (fun _ _ => zero_le_one) (w-y) ⊥ Set.finite_empty hzero hV hLV isCompact_empty
  obtain ⟨M,hM⟩ := (K.isCompact_space_of_finite hK).exists_bound_of_continuousOn hg.continuousOn
  have hgBound (x : E) : g x ≤ |M| + 1 := by
    by_cases hx : x ∈ K.space
    · exact (le_abs_self _).trans ((hM x hx).trans ((le_abs_self M).trans (le_add_of_nonneg_right zero_le_one)))
    · rw [hgK x hx]
      positivity
  let τ := min ε (1 / (|M| + 1)) / 2
  have hτ : 0 < τ := half_pos (lt_min hε (by positivity))
  have hτε : τ ≤ ε := by dsimp [τ]; linarith [min_le_left ε (1/(|M|+1))]
  have hτbound : τ * (|M| + 1) ≤ 1 / 2 := by
    have hmin : min ε (1/(|M|+1)) ≤ 1/(|M|+1) := min_le_right _ _
    have hprod := (le_div_iff₀ (by positivity : (0 : ℝ) < |M|+1)).mp hmin
    dsimp [τ]
    nlinarith
  let t : Icc (-ε) ε := ⟨τ,by constructor <;> linarith⟩
  let H := F t
  have hformula (x : E) : H x = x + (τ * g x) • (w-y) := hF t x
  have hheight (x : E) : A (H x) = A x := by
    rw [hformula,add_comm]
    change A ((τ*g x) • (w-y) +ᵥ x) = A x
    rw [A.map_vadd,map_smul]
    have hdir : A.linear (w-y) = 0 := by
      simpa only [vsub_eq_sub,hAw,sub_self] using A.linearMap_vsub w y
    rw [hdir,smul_zero,zero_vadd]
  have hinside (x : E) (hx : x ∈ C) (hpos : 0 < g x) : H x ∈ interior C := by
    have hxV : x ∈ V := by
      by_contra hnot
      exact hpos.ne' (hgV x hnot)
    rw [hformula]
    apply convex_inward_translation_of_ball hC hrC hx hxV.2
    refine ⟨mul_pos hτ hpos,?_⟩
    have hmul := mul_le_mul_of_nonneg_left (hgBound x) hτ.le
    linarith
  have hPLH := hPL t
  refine ⟨H,hPLH,H.finitePiecewiseAffineOn_symm_of_forall_finite_polyhedron hPLH,
    ?_,hheight,?_,?_⟩
  · intro x hx
    rw [hformula,hgV x (fun h => hx h.1),mul_zero,zero_smul,add_zero]
    rfl
  · intro x hx
    rcases (hgn x).eq_or_lt with hz | hp
    · right
      rw [hformula,← hz,mul_zero,zero_smul,add_zero]
    · exact Or.inl (hinside x hx hp)
  · apply hinside y hy
    rw [hgf (interior_subset (hyL (mem_singleton y)))]
    exact zero_lt_one

end PoincareConjecture.M76
