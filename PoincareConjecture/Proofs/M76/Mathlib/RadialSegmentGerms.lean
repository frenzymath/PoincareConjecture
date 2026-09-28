import PoincareConjecture.Proofs.M76.Mathlib.PolygonLocalSegments
import PoincareConjecture.Proofs.M76.Mathlib.RadialStar
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveBirthStar
import Mathlib.Data.Set.Card

set_option autoImplicit false

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Set.exists_pos_smul_mem_of_mem_nhds {U : Set E}
    (hU : U ∈ 𝓝 (0 : E)) (x : E) :
    ∃ r : ℝ, r ∈ Ioc 0 1 ∧ r • x ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  let r : ℝ := min (1 / 2) (ε / (2 * (‖x‖ + 1)))
  have hden : 0 < 2 * (‖x‖ + 1) := by positivity
  have hr : 0 < r := lt_min (by norm_num) (div_pos hε hden)
  have hbound : r * (2 * (‖x‖ + 1)) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  refine ⟨r, ⟨hr, (min_le_left _ _).trans (by norm_num)⟩, hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le]
  nlinarith [norm_nonneg x]

namespace NormedSpace

theorem normalize_eq_of_mem_segment_zero {x u : E}
    (hx : x ∈ segment ℝ 0 u) (hx0 : x ≠ 0) : normalize x = normalize u := by
  obtain ⟨a, b, _, hb, _, heq⟩ := hx
  simp only [smul_zero, zero_add] at heq
  have hb0 : b ≠ 0 := by
    intro h
    exact hx0 (by simpa only [h, zero_smul] using heq.symm)
  rw [← heq]
  exact normalize_smul_of_pos (lt_of_le_of_ne hb hb0.symm) u

theorem normalize_ne_of_segment_inter {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (hinter : segment ℝ 0 u ∩ segment ℝ 0 v ⊆ {0}) :
    normalize u ≠ normalize v := by
  have hcase (x y : E) (hx : x ≠ 0) (hy : y ≠ 0)
      (hxy : normalize x = normalize y) (hle : ‖x‖ ≤ ‖y‖) :
      x ∈ segment ℝ 0 y := by
    have hr : ‖x‖ / ‖y‖ ∈ Icc (0 : ℝ) 1 :=
      ⟨(div_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).le,
        (div_le_one (norm_pos_iff.mpr hy)).mpr hle⟩
    have heq : (‖x‖ / ‖y‖) • y = x := by
      calc
        (‖x‖ / ‖y‖) • y = ‖x‖ • normalize y := by
          rw [NormedSpace.normalize, smul_smul, div_eq_mul_inv]
        _ = ‖x‖ • normalize x := by rw [hxy]
        _ = x := norm_smul_normalize x
    exact heq ▸ (convex_segment (0 : E) y).smul_mem_of_zero_mem
      (left_mem_segment ℝ 0 y) (right_mem_segment ℝ 0 y) hr
  intro h
  rcases le_total ‖u‖ ‖v‖ with hle | hle
  · exact hu (hinter ⟨right_mem_segment ℝ 0 u, hcase u v hu hv h hle⟩)
  · exact hv (hinter ⟨hcase v u hv hu h.symm hle, right_mem_segment ℝ 0 v⟩)

end NormedSpace

namespace Geometry.SimplicialComplex

variable [DecidableEq E]

theorem normalize_image_link_zero_of_local_segments
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) (L : E →ₗ[ℝ] ℝ)
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (hlocal : ∀ᶠ x in 𝓝 (0 : E),
      x ∈ K.space ∩ {y | L y = 0} ↔ x ∈ segment ℝ 0 u ∪ segment ℝ 0 v) :
    NormedSpace.normalize '' ((K.link 0).space ∩ {x | L x = 0}) =
      {NormedSpace.normalize u, NormedSpace.normalize v} := by
  obtain ⟨ε, hε, hball⟩ := K.exists_ball_inter_space_subset_closedStar hK hzero
  have hN : {x | x ∈ K.space ∩ {y | L y = 0} ↔
      x ∈ segment ℝ 0 u ∪ segment ℝ 0 v} ∩ Metric.ball 0 ε ∈ 𝓝 (0 : E) :=
    inter_mem hlocal (Metric.ball_mem_nhds 0 hε)
  have hsmul (y : E) (hy : y ∈ (K.link 0).space) {r : ℝ} (hr : r ∈ Icc 0 1) :
      r • y ∈ K.space := by
    obtain ⟨s, hs, hys⟩ := mem_space_iff.mp hy
    apply K.convexHull_subset_space hs.2.2
    exact (convex_convexHull ℝ _).smul_mem_of_zero_mem
      (subset_convexHull ℝ _ (Finset.mem_insert_self _ _))
      (convexHull_mono (Finset.subset_insert _ _) hys) hr
  apply Subset.antisymm
  · rintro z ⟨y, hy, rfl⟩
    obtain ⟨r, hr, hNry⟩ := Set.exists_pos_smul_mem_of_mem_nhds hN y
    have hy0 : y ≠ 0 := fun h => K.zero_notMem_link_space (h ▸ hy.1)
    have hry : r • y ∈ K.space ∩ {x | L x = 0} :=
      ⟨hsmul y hy.1 ⟨hr.1.le, hr.2⟩, by
        change L (r • y) = 0
        rw [map_smul, hy.2, smul_zero]⟩
    rcases hNry.1.mp hry with hru | hrv
    · exact Or.inl ((NormedSpace.normalize_smul_of_pos hr.1 y).symm.trans
        (NormedSpace.normalize_eq_of_mem_segment_zero hru (smul_ne_zero hr.1.ne' hy0)))
    · exact Or.inr ((NormedSpace.normalize_smul_of_pos hr.1 y).symm.trans
        (NormedSpace.normalize_eq_of_mem_segment_zero hrv (smul_ne_zero hr.1.ne' hy0)))
  · have hdir (w : E) (hw : w ≠ 0)
        (hseg : segment ℝ 0 w ⊆ segment ℝ 0 u ∪ segment ℝ 0 v) :
        NormedSpace.normalize w ∈
          NormedSpace.normalize '' ((K.link 0).space ∩ {x | L x = 0}) := by
      obtain ⟨r, hr, hNrw⟩ := Set.exists_pos_smul_mem_of_mem_nhds hN w
      have hrseg : r • w ∈ segment ℝ 0 w :=
        (convex_segment (0 : E) w).smul_mem_of_zero_mem
          (left_mem_segment ℝ 0 w) (right_mem_segment ℝ 0 w) ⟨hr.1.le, hr.2⟩
      have hrw := hNrw.1.mpr (hseg hrseg)
      obtain ⟨y, hy, a, ha, hya⟩ := exists_linkPoint_smul
        (hball ⟨hrw.1, hNrw.2⟩) (smul_ne_zero hr.1.ne' hw)
      have hLy : L y = 0 := by
        have hLrw : L (r • w) = 0 := hrw.2
        rw [hya, map_smul, smul_eq_mul] at hLrw
        exact (mul_eq_zero.mp hLrw).resolve_left ha.1.ne'
      refine ⟨y, ⟨hy, hLy⟩, ?_⟩
      calc
        NormedSpace.normalize y = NormedSpace.normalize (a • y) :=
          (NormedSpace.normalize_smul_of_pos ha.1 y).symm
        _ = NormedSpace.normalize (r • w) := congrArg NormedSpace.normalize hya.symm
        _ = NormedSpace.normalize w := NormedSpace.normalize_smul_of_pos hr.1 w
    intro z hz
    rcases hz with rfl | rfl
    · exact hdir u hu subset_union_left
    · exact hdir v hv subset_union_right

theorem ncard_link_zero_of_local_segments
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hzero : (0 : E) ∈ K.vertices) (L : E →ₗ[ℝ] ℝ)
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (hinter : segment ℝ 0 u ∩ segment ℝ 0 v ⊆ {0})
    (hlocal : ∀ᶠ x in 𝓝 (0 : E),
      x ∈ K.space ∩ {y | L y = 0} ↔ x ∈ segment ℝ 0 u ∪ segment ℝ 0 v) :
    ((K.link 0).space ∩ {x | L x = 0}).ncard = 2 := by
  have hinj : InjOn (NormedSpace.normalize : E → E)
      ((K.link 0).space ∩ {x | L x = 0}) := K.injOn_normalize_link.mono inter_subset_left
  rw [← hinj.ncard_image, K.normalize_image_link_zero_of_local_segments hK hzero L hu hv hlocal]
  exact ncard_pair (NormedSpace.normalize_ne_of_segment_inter hu hv hinter)

end Geometry.SimplicialComplex
