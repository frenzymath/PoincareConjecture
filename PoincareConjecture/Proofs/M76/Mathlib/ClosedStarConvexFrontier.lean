import PoincareConjecture.Proofs.M76.Mathlib.RadialComplexFrontierChart
import PoincareConjecture.Proofs.M76.Mathlib.TruncatedStarConeCarrier
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage












set_option autoImplicit false

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]





theorem radial_frontier_section_eq_closedStar_inter
    (K : SimplicialComplex ℝ E) {C : Set E}
    (hC : IsClosed C) (hcv : Convex ℝ C) (hzero : (0 : E) ∈ interior C)
    (hdisj : Disjoint C (K.link 0).space) :
    (frontier C ∩ (NormedSpace.normalize ⁻¹'
      (NormedSpace.normalize '' (K.link 0).space)) : Set E) =
        (K.closedStar 0).space ∩ frontier C := by
  ext z
  constructor
  · rintro ⟨hzC, y, hy, hdir⟩
    have hz0 : z ≠ 0 := fun he => hzC.2 (he ▸ hzero)
    have hy0 : y ≠ 0 := fun he => K.zero_notMem_link_space (he ▸ hy)
    let r := ‖z‖ / ‖y‖
    have hr : 0 < r := div_pos (norm_pos_iff.mpr hz0) (norm_pos_iff.mpr hy0)
    have hzy : z = r • y := by
      calc
        z = ‖z‖ • NormedSpace.normalize z := (norm_smul_normalize z).symm
        _ = ‖z‖ • NormedSpace.normalize y := by rw [hdir]
        _ = r • y := by rw [NormedSpace.normalize, smul_smul]; rfl
    have hrlt : r < 1 := by
      by_contra hn
      have hrinv : r⁻¹ ∈ Icc (0 : ℝ) 1 :=
        ⟨inv_nonneg.mpr hr.le, (inv_le_one₀ hr).mpr (le_of_not_gt hn)⟩
      have hyC := hcv.smul_mem_of_zero_mem (interior_subset hzero)
        (hC.frontier_subset hzC) hrinv
      rw [hzy, inv_smul_smul₀ hr.ne'] at hyC
      exact disjoint_left.mp hdisj hyC hy
    have hys : y ∈ (K.closedStar 0).space :=
      space_subset_of_le (K.link_le_closedStar 0) hy
    exact ⟨hzy.symm ▸ K.smul_mem_closedStar_zero hys ⟨hr.le, hrlt.le⟩, hzC⟩
  · rintro ⟨hzstar, hzC⟩
    have hz0 : z ≠ 0 := fun he => hzC.2 (he ▸ hzero)
    obtain ⟨y, hy, r, hr, hzy⟩ := exists_linkPoint_smul hzstar hz0
    refine ⟨hzC, y, hy, ?_⟩
    rw [hzy, normalize_smul_of_pos hr.1]

variable [FiniteDimensional ℝ E]




theorem exists_finitePL_link_convex_frontier_chart
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C) (hdisj : Disjoint C (K.link 0).space)
    {ι : Type*} [Finite ι] [Nonempty ι] (L : ι → E →ₗ[ℝ] ℝ)
    (hL : ∀ i, L i ≠ 0) (hrep : C = {x | ∀ i, L i x ≤ 1}) :
    ∃ e : (K.link 0).space ≃ₜ ((K.closedStar 0).space ∩ frontier C : Set E),
      e.IsFinitePL := by
  obtain ⟨e, he⟩ := (K.link 0).exists_finitePL_radial_frontier_section
    (finite_link_faces hK 0) (fun _ hs => linearIndependent_of_mem_link_zero hs)
    (K.injOn_normalize_link) hC hcv hzero L hL hrep
  have heq := K.radial_frontier_section_eq_closedStar_inter hC.isClosed hcv hzero hdisj
  exact ⟨e.trans (Homeomorph.setCongr heq), he.setCongr rfl heq⟩





theorem exists_polygon_closedStar_convex_frontier
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (hPspace : P.boundary ℝ = (K.link 0).space)
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hzero : (0 : E) ∈ interior C) (hdisj : Disjoint C (K.link 0).space)
    {ι : Type*} [Finite ι] [Nonempty ι] (L : ι → E →ₗ[ℝ] ℝ)
    (hL : ∀ i, L i ≠ 0) (hrep : C = {x | ∀ i, L i x ≤ 1}) :
    ∃ (N : ℕ) (Q : Polygon E (N + 3)), Function.Injective Q ∧ Q.HasSimplicialEdges ∧
      Q.boundary ℝ = (K.closedStar 0).space ∩ frontier C := by
  obtain ⟨e, ⟨f, hf, hef⟩⟩ :=
    K.exists_finitePL_link_convex_frontier_chart hK hC hcv hzero hdisj L hL hrep
  have hfi : InjOn f (K.link 0).space := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext
      ((hef ⟨x, hx⟩).trans (hxy.trans (hef ⟨y, hy⟩).symm))))
  obtain ⟨N, Q, hQi, hQe, hQb⟩ :=
    P.exists_polygon_finitePL_image hP hinj hf hPspace.subset (hfi.mono hPspace.subset)
  refine ⟨N, Q, hQi, hQe, hQb.trans ?_⟩
  rw [hPspace]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← hef ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  · intro hy
    refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
    rw [← hef, e.apply_symm_apply]

end Geometry.SimplicialComplex
