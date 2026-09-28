import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false

open Set Metric unitInterval

namespace Geometry.DiskBlockCover

abbrev Plane := Fin 2 → ℝ

def block : Set (Plane × ℝ) := closedBall (0 : Plane) 1 ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)

def lateral : Set (Plane × ℝ) := sphere (0 : Plane) 1 ×ˢ Ioo (-3 / 4 : ℝ) (3 / 4)

def core : Set (Plane × ℝ) := closedBall (0 : Plane) (1 / 2) ×ˢ Icc (-1 / 2 : ℝ) (1 / 2)

def cover : Set (Plane × ℝ) := block ∪ lateral

private noncomputable def clamp (t : ℝ) : ℝ := max (-1 / 2) (min (1 / 2) t)

private theorem clamp_mem (t : ℝ) : clamp t ∈ Icc (-1 / 2 : ℝ) (1 / 2) :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private theorem plane_mem {z : Plane × ℝ} (hz : z ∈ cover) : z.1 ∈ closedBall 0 1 := by
  rcases hz with hz | hz
  · exact hz.1
  · exact sphere_subset_closedBall hz.1

theorem contractible_cover : ContractibleSpace cover := by
  let r : C(cover, block) :=
    ⟨fun z => ⟨((z : Plane × ℝ).1, clamp (z : Plane × ℝ).2),
      plane_mem (z := (z : Plane × ℝ)) z.property, clamp_mem _⟩, by unfold clamp; fun_prop⟩
  let inc : C(block, cover) := ContinuousMap.inclusion subset_union_left
  let H : (ContinuousMap.id cover).Homotopy (inc.comp r) := {
    toFun := fun z => ⟨((z.2 : Plane × ℝ).1,
      (1 - (z.1 : ℝ)) * (z.2 : Plane × ℝ).2 + (z.1 : ℝ) * clamp (z.2 : Plane × ℝ).2), by
      rcases z.2.property with hb | hl
      · exact Or.inl ⟨hb.1, (convex_Icc (-1 / 2 : ℝ) (1 / 2)) hb.2 (clamp_mem _)
          (sub_nonneg.mpr z.1.property.2) z.1.property.1 (by ring)⟩
      · have hc : clamp (z.2 : Plane × ℝ).2 ∈ Ioo (-3 / 4 : ℝ) (3 / 4) := by
          have hh := clamp_mem (z.2 : Plane × ℝ).2
          constructor <;> linarith [hh.1, hh.2]
        exact Or.inr ⟨hl.1, (convex_Ioo (-3 / 4 : ℝ) (3 / 4)) hl.2 hc
          (sub_nonneg.mpr z.1.property.2) z.1.property.1 (by ring)⟩⟩
    continuous_toFun := by unfold clamp; fun_prop
    map_zero_left := by intro z; apply Subtype.ext; simp
    map_one_left := by
      intro z
      apply Subtype.ext
      change ((z : Plane × ℝ).1, (1 - (1 : ℝ)) * (z : Plane × ℝ).2 +
        1 * clamp (z : Plane × ℝ).2) = ((z : Plane × ℝ).1, clamp (z : Plane × ℝ).2)
      simp }
  have hcv : Convex ℝ block := (convex_closedBall (0 : Plane) 1).prod
    (convex_Icc (-1 / 2 : ℝ) (1 / 2))
  let : ContractibleSpace block := hcv.contractibleSpace ⟨(0, 0), by
    constructor <;> norm_num [mem_closedBall]⟩
  have hnull : (inc.comp r).Nullhomotopic := by
    simpa only [ContinuousMap.id_comp] using ((id_nullhomotopic block).comp_left r).comp_right inc
  obtain ⟨p, hp⟩ := hnull
  exact (contractible_iff_id_nullhomotopic cover).mpr ⟨p, (show
    (ContinuousMap.id cover).Homotopic (inc.comp r) from ⟨H⟩).trans hp⟩

theorem annulus_eq_radial_image :
    closedBall (0 : Plane) 1 \ closedBall (0 : Plane) (1 / 2) =
      (fun z : Plane × ℝ => z.2 • z.1) ''
        (sphere (0 : Plane) 1 ×ˢ Ioc (1 / 2 : ℝ) 1) := by
  ext x
  constructor
  · rintro ⟨hx, hnot⟩
    have hxle : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hxgt : (1 / 2 : ℝ) < ‖x‖ := by
      simpa only [mem_closedBall, dist_zero_right, not_le] using hnot
    have hxpos : 0 < ‖x‖ := by linarith
    refine ⟨(‖x‖⁻¹ • x, ‖x‖), ⟨?_, hxgt, hxle⟩, smul_inv_smul₀ (ne_of_gt hxpos) x⟩
    rw [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hxpos), inv_mul_cancel₀ (ne_of_gt hxpos)]
  · rintro ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩
    have hun : ‖u‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hu
    have htn : ‖t • u‖ = t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [ht.1]), hun, mul_one]
    simp only [mem_sdiff, mem_closedBall, dist_zero_right, htn, not_le]
    exact ⟨ht.2, ht.1⟩

theorem isPathConnected_annulus :
    IsPathConnected (closedBall (0 : Plane) 1 \ closedBall (0 : Plane) (1 / 2)) := by
  rw [annulus_eq_radial_image]
  exact ((isPathConnected_sphere (by simp [Plane]) (0 : Plane) zero_le_one).prod
    ((convex_Ioc (1 / 2 : ℝ) 1).isPathConnected ⟨1, by constructor <;> norm_num⟩)).image
      (by fun_prop)

theorem cover_sdiff_core :
    cover \ core =
      ((closedBall (0 : Plane) 1 \ closedBall (0 : Plane) (1 / 2)) ×ˢ
        Icc (-1 / 2 : ℝ) (1 / 2)) ∪ lateral := by
  have hlat : Disjoint lateral core := by
    apply Set.disjoint_left.mpr
    intro z hz hc
    have hn : ‖z.1‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz.1
    have hle : ‖z.1‖ ≤ 1 / 2 := by simpa only [mem_closedBall, dist_zero_right] using hc.1
    linarith
  ext z
  constructor
  · rintro ⟨hz | hz, hnot⟩
    · exact Or.inl ⟨⟨hz.1, fun hx => hnot ⟨hx, hz.2⟩⟩, hz.2⟩
    · exact Or.inr hz
  · rintro (hz | hz)
    · exact ⟨Or.inl ⟨hz.1.1, hz.2⟩, fun hc => hz.1.2 hc.1⟩
    · exact ⟨Or.inr hz, fun hc => Set.disjoint_left.mp hlat hz hc⟩

theorem isPathConnected_cover_sdiff_core : IsPathConnected (cover \ core) := by
  rw [cover_sdiff_core]
  have hs : IsPathConnected (sphere (0 : Plane) 1) :=
    isPathConnected_sphere (by simp [Plane]) 0 zero_le_one
  apply (isPathConnected_annulus.prod ((convex_Icc (-1 / 2 : ℝ) (1 / 2)).isPathConnected
    ⟨0, by constructor <;> norm_num⟩)).union
      (hs.prod ((convex_Ioo (-3 / 4 : ℝ) (3 / 4)).isPathConnected
        ⟨0, by constructor <;> norm_num⟩))
  obtain ⟨u, hu⟩ := hs.nonempty
  refine ⟨(u, 0), ⟨⟨⟨sphere_subset_closedBall hu, ?_⟩, by constructor <;> norm_num⟩,
    ⟨hu, by constructor <;> norm_num⟩⟩⟩
  intro hh
  have hn : ‖u‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hu
  have hle : ‖u‖ ≤ 1 / 2 := by simpa only [mem_closedBall, dist_zero_right] using hh
  linarith

end Geometry.DiskBlockCover
