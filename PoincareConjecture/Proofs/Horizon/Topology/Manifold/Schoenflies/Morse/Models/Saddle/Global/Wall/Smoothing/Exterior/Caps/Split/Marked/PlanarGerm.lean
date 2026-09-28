import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Marked.PlanarSlices



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem mem_tangentPlanarDiffeomorph_sphere_iff {t : Real}
    (ht : t ∈ Ioo (-1 : Real) 1) (y : E2) :
    y ∈ tangentPlanarDiffeomorph t ht '' sphere (0 : E2) 1 ↔
      vector (y 0) (y 1) t ∈ tangentFlatShear '' sphere (0 : E3) 1 := by
  rw [tangentPlanarDiffeomorph_sphere]
  constructor
  · rintro ⟨q, hq⟩
    have he : vector (y 0) (y 1) t = tangentFlatShearSlice (t, q) := by
      rw [← hq]
      ext i
      fin_cases i
      · rfl
      · rfl
      · exact (tangentFlatShearSlice_height t q).symm
    rw [he]
    exact ⟨sphereLatitude t q, sphereLatitude_mem_sphere ht q, rfl⟩
  · intro hy
    obtain ⟨q, hq⟩ := (range_tangentFlatShearSlice ht).symm ▸
      (show vector (y 0) (y 1) t ∈
        (tangentFlatShear '' sphere (0 : E3) 1) ∩ {p | p 2 = t} from ⟨hy, rfl⟩)
    refine ⟨q, ?_⟩
    change tangentFlatShearSlice (t, q) = vector (y 0) (y 1) t at hq
    change horizontal (tangentFlatShearSlice (t, q)) = y
    rw [hq]
    ext i
    fin_cases i <;> rfl


def tangentPlanarWallNeighborhood (t : Real) : Set E2 :=
  {y | |y 0| < 1 ∧ (y 1) ^ 2 + t ^ 2 < 1 / 4}

theorem isOpen_tangentPlanarWallNeighborhood (t : Real) :
    IsOpen (tangentPlanarWallNeighborhood t) := by
  change IsOpen ({y : E2 | |y 0| < 1} ∩ {y : E2 | (y 1) ^ 2 + t ^ 2 < 1 / 4})
  apply IsOpen.inter
  · exact isOpen_lt (by fun_prop) continuous_const
  · exact isOpen_lt (by fun_prop) continuous_const

theorem tangentPlanarDiffeomorph_mem_sphere_iff_of_mem_wallNeighborhood
    {t : Real} (ht : t ∈ Ioo (-1 : Real) 1) {y : E2}
    (hy : y ∈ tangentPlanarWallNeighborhood t) :
    y ∈ tangentPlanarDiffeomorph t ht '' sphere (0 : E2) 1 ↔ y 0 = 0 := by
  rw [mem_tangentPlanarDiffeomorph_sphere_iff]
  constructor
  · rintro ⟨p, hp, hpy⟩
    have h0 : p 0 - tangentFlattenDepth p = y 0 := by
      simpa only [tangentFlatShear_zero, vector_zero] using
        congrArg (fun z : E3 => z 0) hpy
    have h1 : p 1 = y 1 := by
      simpa only [tangentFlatShear_one, vector_one] using
        congrArg (fun z : E3 => z 1) hpy
    have h2 : p 2 = t := by
      simpa only [tangentFlatShear_two, vector_two] using
        congrArg (fun z : E3 => z 2) hpy
    have hs : tangentRadiusSq p < 1 / 4 := by
      simpa only [tangentRadiusSq, h1, h2] using hy.2
    have hχ : tangentFlattenCutoff (tangentRadiusSq p) = 1 := by
      simp only [tangentFlattenCutoff,
        Real.smoothTransition.zero_of_nonpos (by linarith : 4 * tangentRadiusSq p - 1 ≤ 0),
        sub_zero]
    have hd := tangentFlattenDepth_sq p
    rw [hχ, mul_one] at hd
    have hdpos : 1 / 2 < tangentFlattenDepth p := by
      nlinarith [tangentFlattenDepth_nonneg p]
    have hnorm : (p 0) ^ 2 + tangentRadiusSq p = 1 := by
      have hn := EuclideanSpace.norm_sq_eq p
      rw [mem_sphere_zero_iff_norm.mp hp] at hn
      simpa only [one_pow, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs,
        tangentRadiusSq, add_assoc] using hn.symm
    have heq : (p 0) ^ 2 = tangentFlattenDepth p ^ 2 := by linarith
    have hylower : -1 < y 0 := (abs_lt.mp hy.1).1
    obtain hsame | hneg := sq_eq_sq_iff_eq_or_eq_neg.mp heq
    · linarith
    · linarith
  · intro hy0
    have hwall : vector (y 0) (y 1) t ∈
        {p : E3 | p 0 = 0 ∧ tangentRadiusSq p ≤ 1 / 4} := ⟨hy0, hy.2.le⟩
    have hm := tangentFlatShear_sphere_inter_wall.symm ▸ hwall
    exact hm.1

theorem tangentPlanarDiffeomorph_sphere_inter_wallNeighborhood (t : Real)
    (ht : t ∈ Ioo (-1 : Real) 1) :
    (tangentPlanarDiffeomorph t ht '' sphere (0 : E2) 1) ∩ tangentPlanarWallNeighborhood t =
      {y : E2 | y 0 = 0} ∩ tangentPlanarWallNeighborhood t := by
  ext y
  exact and_congr_left (fun hy =>
    tangentPlanarDiffeomorph_mem_sphere_iff_of_mem_wallNeighborhood ht hy)

theorem tangentPlanarDiffeomorph_wall_germ {t : Real} (ht : t ∈ Ioo (-1 : Real) 1)
    {p : E2} (hp0 : p 0 = 0) (hp : (p 1) ^ 2 + t ^ 2 < 1 / 4) :
    ∀ᶠ y in 𝓝 p, y ∈ tangentPlanarDiffeomorph t ht '' sphere (0 : E2) 1 ↔ y 0 = 0 := by
  have hmem : p ∈ tangentPlanarWallNeighborhood t := ⟨by simp [hp0], hp⟩
  filter_upwards [(isOpen_tangentPlanarWallNeighborhood t).mem_nhds hmem] with y hy
  exact tangentPlanarDiffeomorph_mem_sphere_iff_of_mem_wallNeighborhood ht hy

theorem tangentPlanarDiffeomorph_wall_germ_on_set {t : Real}
    (ht : t ∈ Ioo (-1 : Real) 1) {K : Set E2}
    (hK : ∀ p ∈ K, p 0 = 0 ∧ (p 1) ^ 2 + t ^ 2 < 1 / 4) :
    ∀ᶠ y in 𝓝ˢ K, y ∈ tangentPlanarDiffeomorph t ht '' sphere (0 : E2) 1 ↔ y 0 = 0 := by
  have hmem : tangentPlanarWallNeighborhood t ∈ 𝓝ˢ K :=
    (isOpen_tangentPlanarWallNeighborhood t).mem_nhdsSet.mpr (by
      intro p hp
      exact ⟨by simp [(hK p hp).1], (hK p hp).2⟩)
  filter_upwards [hmem] with y hy
  exact tangentPlanarDiffeomorph_mem_sphere_iff_of_mem_wallNeighborhood ht hy

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split
