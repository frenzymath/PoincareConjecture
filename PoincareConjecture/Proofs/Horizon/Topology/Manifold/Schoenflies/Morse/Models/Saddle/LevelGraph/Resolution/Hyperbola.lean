import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Coordinates
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)

def hyperbolaRadius (r t : Real) : Real := Real.sqrt (r ^ 2 - t)

def positiveLevelArc (t : Real) (i : Fin 2) (s : Real) : E2 :=
  WithLp.toLp 2 ![s, if i = 0 then Real.sqrt (t + s ^ 2) else -Real.sqrt (t + s ^ 2)]

def saddleCoordinateSwap (x : E2) : E2 := WithLp.toLp 2 ![x 1, x 0]

def negativeLevelArc (t : Real) (i : Fin 2) (s : Real) : E2 :=
  saddleCoordinateSwap (positiveLevelArc t i s)

def positiveLevelContact (r t : Real) (i : Fin 2 × Fin 2) : E2 :=
  WithLp.toLp 2 ![if i.2 = 0 then -hyperbolaRadius r t else hyperbolaRadius r t,
    if i.1 = 0 then r else -r]

def negativeLevelContact (r t : Real) (i : Fin 2 × Fin 2) : E2 :=
  saddleCoordinateSwap (positiveLevelContact r t i)

theorem hyperbolaRadius_pos {r t : Real} (htr : t < r ^ 2) : 0 < hyperbolaRadius r t :=
  Real.sqrt_pos.2 (sub_pos.mpr htr)

theorem hyperbolaRadius_sq {r t : Real} (htr : t ≤ r ^ 2) :
    (hyperbolaRadius r t) ^ 2 = r ^ 2 - t := Real.sq_sqrt (sub_nonneg.mpr htr)

theorem hyperbolaRadius_lt {r t : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) :
    hyperbolaRadius r t < r := by
  have hs := hyperbolaRadius_sq htr.le
  have hp := hyperbolaRadius_pos htr
  nlinarith

@[simp] theorem positiveLevelArc_zero (t : Real) (i : Fin 2) (s : Real) :
    positiveLevelArc t i s 0 = s := rfl

@[simp] theorem positiveLevelArc_one (t : Real) (i : Fin 2) (s : Real) :
    positiveLevelArc t i s 1 =
      if i = 0 then Real.sqrt (t + s ^ 2) else -Real.sqrt (t + s ^ 2) := rfl

theorem contDiff_positiveLevelArc {t : Real} (ht : 0 < t) (i : Fin 2) :
    ContDiff Real ∞ (positiveLevelArc t i) := by
  apply (contDiff_piLp 2).mpr
  intro j
  fin_cases j
  · exact contDiff_id
  · change ContDiff Real ∞ (fun s : Real =>
      if i = 0 then Real.sqrt (t + s ^ 2) else -Real.sqrt (t + s ^ 2))
    have hroot : ContDiff Real ∞ (fun s : Real => Real.sqrt (t + s ^ 2)) :=
      (contDiff_const.add (contDiff_id.pow 2)).sqrt (fun s => ne_of_gt (by positivity))
    split_ifs
    · exact hroot
    · exact hroot.neg

theorem positiveLevelArc_injective (t : Real) (i : Fin 2) :
    Function.Injective (positiveLevelArc t i) := by
  intro s u hsu
  exact congrArg (fun x : E2 => x 0) hsu

theorem deriv_positiveLevelArc_zero {t : Real} (ht : 0 < t) (i : Fin 2) (s : Real) :
    deriv (positiveLevelArc t i) s 0 = 1 := by
  have hd := (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).hasFDerivAt.comp_hasDerivAt s
    ((contDiff_positiveLevelArc ht i).differentiable (by simp) s).hasDerivAt
  change HasDerivAt id (deriv (positiveLevelArc t i) s 0) s at hd
  exact hd.unique (hasDerivAt_id s)

theorem positiveLevelArc_height {t : Real} (ht : 0 < t) (i : Fin 2) (s : Real) :
    -(positiveLevelArc t i s 0) ^ 2 + (positiveLevelArc t i s 1) ^ 2 = t := by
  have hs := Real.sq_sqrt (show 0 ≤ t + s ^ 2 by positivity)
  simp only [positiveLevelArc_zero, positiveLevelArc_one]
  split_ifs <;> nlinarith

theorem positiveLevelArc_mem_closedSquare {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (i : Fin 2) (s : Real) :
    positiveLevelArc t i s ∈ closedSquare r ↔
      s ∈ Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) := by
  have hrad := hyperbolaRadius_pos htr
  have hrad2 := hyperbolaRadius_sq htr.le
  have hrads := hyperbolaRadius_lt hr ht htr
  have hsqrt := Real.sq_sqrt (show 0 ≤ t + s ^ 2 by positivity)
  have hsqrt0 := Real.sqrt_nonneg (t + s ^ 2)
  have habs : |positiveLevelArc t i s 1| = Real.sqrt (t + s ^ 2) := by
    simp only [positiveLevelArc_one]
    split_ifs <;> simp [abs_of_nonneg hsqrt0]
  change (|positiveLevelArc t i s 0| ≤ r ∧ |positiveLevelArc t i s 1| ≤ r) ↔ _
  rw [positiveLevelArc_zero, habs]
  constructor
  · rintro ⟨_, hs⟩
    have hs2 : s ^ 2 ≤ (hyperbolaRadius r t) ^ 2 := by nlinarith
    have habs := (sq_le_sq₀ (abs_nonneg s) hrad.le).mp (by simpa using hs2)
    exact abs_le.mp habs
  · intro hs
    have habs : |s| ≤ hyperbolaRadius r t := abs_le.mpr hs
    have hs2 : s ^ 2 ≤ (hyperbolaRadius r t) ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg s) hrad.le).mpr habs
    refine ⟨habs.trans hrads.le, ?_⟩
    nlinarith

theorem positiveLevelArc_mem_openSquare {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (i : Fin 2) (s : Real) :
    positiveLevelArc t i s ∈ openSquare r ↔
      s ∈ Ioo (-hyperbolaRadius r t) (hyperbolaRadius r t) := by
  have hrad := hyperbolaRadius_pos htr
  have hrad2 := hyperbolaRadius_sq htr.le
  have hrads := hyperbolaRadius_lt hr ht htr
  have hsqrt := Real.sq_sqrt (show 0 ≤ t + s ^ 2 by positivity)
  have hsqrt0 := Real.sqrt_nonneg (t + s ^ 2)
  have habs : |positiveLevelArc t i s 1| = Real.sqrt (t + s ^ 2) := by
    simp only [positiveLevelArc_one]
    split_ifs <;> simp [abs_of_nonneg hsqrt0]
  change (|positiveLevelArc t i s 0| < r ∧ |positiveLevelArc t i s 1| < r) ↔ _
  rw [positiveLevelArc_zero, habs]
  constructor
  · rintro ⟨_, hs⟩
    have hs2 : s ^ 2 < (hyperbolaRadius r t) ^ 2 := by nlinarith
    have habs := (sq_lt_sq₀ (abs_nonneg s) hrad.le).mp (by simpa using hs2)
    exact abs_lt.mp habs
  · intro hs
    have habs : |s| < hyperbolaRadius r t := abs_lt.mpr hs
    have hs2 : s ^ 2 < (hyperbolaRadius r t) ^ 2 := by
      simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg s) hrad.le).mpr habs
    refine ⟨habs.trans hrads, ?_⟩
    nlinarith

theorem positiveLevelArc_boundary_iff {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (i : Fin 2) (s : Real) :
    positiveLevelArc t i s ∈ closedSquare r \ openSquare r ↔
      s = -hyperbolaRadius r t ∨ s = hyperbolaRadius r t := by
  rw [mem_sdiff, positiveLevelArc_mem_closedSquare hr ht htr,
    positiveLevelArc_mem_openSquare hr ht htr]
  have hp := hyperbolaRadius_pos htr
  simp only [mem_Icc, mem_Ioo]
  constructor
  · rintro ⟨⟨hl, hu⟩, hn⟩
    by_cases he : s = -hyperbolaRadius r t
    · exact Or.inl he
    · exact Or.inr (le_antisymm hu (le_of_not_gt
        (fun hh => hn ⟨lt_of_le_of_ne hl (fun h => he h.symm), hh⟩)))
  · rintro (rfl | rfl) <;> constructor <;> (first | constructor <;> linarith | simp)

theorem positiveLevelArc_endpoint {r t : Real}
    (hr : 0 < r) (htr : t < r ^ 2) (i j : Fin 2) :
    positiveLevelArc t i (if j = 0 then -hyperbolaRadius r t else hyperbolaRadius r t) =
      positiveLevelContact r t (i, j) := by
  have hrad2 := hyperbolaRadius_sq htr.le
  have hsqrt : Real.sqrt (t + (hyperbolaRadius r t) ^ 2) = r := by
    rw [hrad2, add_sub_cancel, Real.sqrt_sq_eq_abs, abs_of_pos hr]
  ext k
  fin_cases k
  · rfl
  · fin_cases j <;> simp [positiveLevelArc, positiveLevelContact, hsqrt]

theorem positiveLevelArc_pairwise_disjoint {t : Real} (ht : 0 < t) :
    Pairwise (fun i j : Fin 2 => Disjoint (range (positiveLevelArc t i))
      (range (positiveLevelArc t j))) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro x ⟨s, rfl⟩ ⟨u, hu⟩
  have hsu : u = s := congrArg (fun x : E2 => x 0) hu
  subst u
  have hy := congrArg (fun x : E2 => x 1) hu
  have hp : 0 < Real.sqrt (t + s ^ 2) := Real.sqrt_pos.2 (by positivity)
  fin_cases i <;> fin_cases j
  · exact hij rfl
  · norm_num [positiveLevelArc] at hy
    linarith
  · norm_num [positiveLevelArc] at hy
    linarith
  · exact hij rfl

theorem closedSquare_positiveLevel_eq_arcs {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) :
    closedSquare r ∩ {x : E2 | -(x 0) ^ 2 + (x 1) ^ 2 = t} =
      ⋃ i : Fin 2, positiveLevelArc t i ''
        Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) := by
  ext x
  constructor
  · rintro ⟨hx, hlevel⟩
    have hy : Real.sqrt (t + (x 0) ^ 2) = |x 1| := by
      have he : t + (x 0) ^ 2 = (x 1) ^ 2 := by change -(x 0)^2 + (x 1)^2 = t at hlevel; linarith
      rw [he, Real.sqrt_sq_eq_abs]
    have harc : ∃ i : Fin 2, positiveLevelArc t i (x 0) = x := by
      by_cases hsign : 0 ≤ x 1
      · refine ⟨0, ?_⟩
        ext k
        fin_cases k <;> simp [positiveLevelArc, hy, abs_of_nonneg hsign]
      · refine ⟨1, ?_⟩
        ext k
        fin_cases k <;> simp [positiveLevelArc, hy, abs_of_neg (lt_of_not_ge hsign)]
    obtain ⟨i, hi⟩ := harc
    exact mem_iUnion.mpr ⟨i, x 0,
      (positiveLevelArc_mem_closedSquare hr ht htr i (x 0)).mp (hi ▸ hx), hi⟩
  · intro hx
    obtain ⟨i, s, hs, rfl⟩ := mem_iUnion.mp hx
    exact ⟨(positiveLevelArc_mem_closedSquare hr ht htr i s).mpr hs,
      positiveLevelArc_height ht i s⟩

theorem isCompact_positiveLevelArc_image {t : Real} (ht : 0 < t) (i : Fin 2) (a b : Real) :
    IsCompact (positiveLevelArc t i '' Icc a b) :=
  isCompact_Icc.image (contDiff_positiveLevelArc ht i).continuous

theorem square_boundary_positiveLevel {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) :
    (closedSquare r \ openSquare r) ∩ {x : E2 | -(x 0) ^ 2 + (x 1) ^ 2 = t} =
      range (positiveLevelContact r t) := by
  ext x
  constructor
  · rintro ⟨hx, hlevel⟩
    have hmem : x ∈ closedSquare r ∩ {x : E2 | -(x 0)^2 + (x 1)^2 = t} := ⟨hx.1, hlevel⟩
    rw [closedSquare_positiveLevel_eq_arcs hr ht htr] at hmem
    obtain ⟨i, s, _, rfl⟩ := mem_iUnion.mp hmem
    rcases (positiveLevelArc_boundary_iff hr ht htr i s).mp hx with he | he
    · refine ⟨(i, 0), ?_⟩
      simpa [he] using (positiveLevelArc_endpoint hr htr i 0).symm
    · refine ⟨(i, 1), ?_⟩
      simpa [he] using (positiveLevelArc_endpoint hr htr i 1).symm
  · rintro ⟨⟨i, j⟩, rfl⟩
    rw [← positiveLevelArc_endpoint hr htr i j]
    exact ⟨(positiveLevelArc_boundary_iff hr ht htr i _).mpr (by split_ifs <;> simp),
      positiveLevelArc_height ht i _⟩

theorem positiveLevelContact_injective {r t : Real}
    (hr : 0 < r) (htr : t < r ^ 2) : Function.Injective (positiveLevelContact r t) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ he
  have hx := congrArg (fun x : E2 => x 0) he
  have hy := congrArg (fun x : E2 => x 1) he
  have hp := hyperbolaRadius_pos htr
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [positiveLevelContact] at hx hy ⊢ <;> linarith

@[simp] theorem saddleCoordinateSwap_zero (x : E2) : saddleCoordinateSwap x 0 = x 1 := rfl
@[simp] theorem saddleCoordinateSwap_one (x : E2) : saddleCoordinateSwap x 1 = x 0 := rfl

@[simp] theorem saddleCoordinateSwap_swap (x : E2) :
    saddleCoordinateSwap (saddleCoordinateSwap x) = x := by
  ext i
  fin_cases i <;> rfl

theorem saddleCoordinateSwap_injective : Function.Injective saddleCoordinateSwap :=
  Function.LeftInverse.injective saddleCoordinateSwap_swap

theorem contDiff_saddleCoordinateSwap : ContDiff Real ∞ saddleCoordinateSwap := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
  · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff

@[simp] theorem saddleCoordinateSwap_mem_closedSquare (r : Real) (x : E2) :
    saddleCoordinateSwap x ∈ closedSquare r ↔ x ∈ closedSquare r := by
  exact and_comm

@[simp] theorem saddleCoordinateSwap_mem_openSquare (r : Real) (x : E2) :
    saddleCoordinateSwap x ∈ openSquare r ↔ x ∈ openSquare r := by
  exact and_comm

theorem contDiff_negativeLevelArc {t : Real} (ht : 0 < t) (i : Fin 2) :
    ContDiff Real ∞ (negativeLevelArc t i) :=
  contDiff_saddleCoordinateSwap.comp (contDiff_positiveLevelArc ht i)

theorem negativeLevelArc_injective (t : Real) (i : Fin 2) :
    Function.Injective (negativeLevelArc t i) :=
  saddleCoordinateSwap_injective.comp (positiveLevelArc_injective t i)

theorem deriv_negativeLevelArc_one {t : Real} (ht : 0 < t) (i : Fin 2) (s : Real) :
    deriv (negativeLevelArc t i) s 1 = 1 := by
  have hd := (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).hasFDerivAt.comp_hasDerivAt s
    ((contDiff_negativeLevelArc ht i).differentiable (by simp) s).hasDerivAt
  change HasDerivAt id (deriv (negativeLevelArc t i) s 1) s at hd
  exact hd.unique (hasDerivAt_id s)

theorem negativeLevelArc_height {t : Real} (ht : 0 < t) (i : Fin 2) (s : Real) :
    -(negativeLevelArc t i s 0) ^ 2 + (negativeLevelArc t i s 1) ^ 2 = -t := by
  have hh := positiveLevelArc_height ht i s
  change -(positiveLevelArc t i s 1)^2 + (positiveLevelArc t i s 0)^2 = -t
  linarith

theorem negativeLevelArc_mem_closedSquare {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (i : Fin 2) (s : Real) :
    negativeLevelArc t i s ∈ closedSquare r ↔
      s ∈ Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) := by
  rw [negativeLevelArc, saddleCoordinateSwap_mem_closedSquare]
  exact positiveLevelArc_mem_closedSquare hr ht htr i s

theorem negativeLevelArc_boundary_iff {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (i : Fin 2) (s : Real) :
    negativeLevelArc t i s ∈ closedSquare r \ openSquare r ↔
      s = -hyperbolaRadius r t ∨ s = hyperbolaRadius r t := by
  simpa only [negativeLevelArc, mem_sdiff, saddleCoordinateSwap_mem_closedSquare,
    saddleCoordinateSwap_mem_openSquare] using positiveLevelArc_boundary_iff hr ht htr i s

theorem negativeLevelArc_endpoint {r t : Real}
    (hr : 0 < r) (htr : t < r ^ 2) (i j : Fin 2) :
    negativeLevelArc t i (if j = 0 then -hyperbolaRadius r t else hyperbolaRadius r t) =
      negativeLevelContact r t (i, j) :=
  congrArg saddleCoordinateSwap (positiveLevelArc_endpoint hr htr i j)

theorem negativeLevelArc_pairwise_disjoint {t : Real} (ht : 0 < t) :
    Pairwise (fun i j : Fin 2 => Disjoint (range (negativeLevelArc t i))
      (range (negativeLevelArc t j))) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro x ⟨s, rfl⟩ ⟨u, hu⟩
  have he : positiveLevelArc t j u = positiveLevelArc t i s :=
    saddleCoordinateSwap_injective hu
  exact disjoint_left.mp (positiveLevelArc_pairwise_disjoint ht hij)
    (mem_range_self s) ⟨u, he⟩

theorem closedSquare_negativeLevel_eq_arcs {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) :
    closedSquare r ∩ {x : E2 | -(x 0) ^ 2 + (x 1) ^ 2 = -t} =
      ⋃ i : Fin 2, negativeLevelArc t i ''
        Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) := by
  ext x
  constructor
  · rintro ⟨hx, hlevel⟩
    have hswap : saddleCoordinateSwap x ∈ closedSquare r ∩
        {x : E2 | -(x 0)^2 + (x 1)^2 = t} := by
      refine ⟨(saddleCoordinateSwap_mem_closedSquare r x).mpr hx, ?_⟩
      change -(x 1)^2 + (x 0)^2 = t
      change -(x 0)^2 + (x 1)^2 = -t at hlevel
      linarith
    rw [closedSquare_positiveLevel_eq_arcs hr ht htr] at hswap
    obtain ⟨i, s, hs, he⟩ := mem_iUnion.mp hswap
    refine mem_iUnion.mpr ⟨i, s, hs, ?_⟩
    simpa only [negativeLevelArc, saddleCoordinateSwap_swap] using congrArg saddleCoordinateSwap he
  · intro hx
    obtain ⟨i, s, hs, rfl⟩ := mem_iUnion.mp hx
    exact ⟨(negativeLevelArc_mem_closedSquare hr ht htr i s).mpr hs,
      negativeLevelArc_height ht i s⟩

theorem isCompact_negativeLevelArc_image {t : Real} (ht : 0 < t) (i : Fin 2) (a b : Real) :
    IsCompact (negativeLevelArc t i '' Icc a b) :=
  isCompact_Icc.image (contDiff_negativeLevelArc ht i).continuous

theorem square_boundary_negativeLevel {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) :
    (closedSquare r \ openSquare r) ∩ {x : E2 | -(x 0) ^ 2 + (x 1) ^ 2 = -t} =
      range (negativeLevelContact r t) := by
  ext x
  constructor
  · rintro ⟨hx, hlevel⟩
    have hmem : x ∈ closedSquare r ∩ {x : E2 | -(x 0)^2 + (x 1)^2 = -t} := ⟨hx.1, hlevel⟩
    rw [closedSquare_negativeLevel_eq_arcs hr ht htr] at hmem
    obtain ⟨i, s, _, rfl⟩ := mem_iUnion.mp hmem
    rcases (negativeLevelArc_boundary_iff hr ht htr i s).mp hx with he | he
    · refine ⟨(i, 0), ?_⟩
      simpa [he] using (negativeLevelArc_endpoint hr htr i 0).symm
    · refine ⟨(i, 1), ?_⟩
      simpa [he] using (negativeLevelArc_endpoint hr htr i 1).symm
  · rintro ⟨⟨i, j⟩, rfl⟩
    rw [← negativeLevelArc_endpoint hr htr i j]
    exact ⟨(negativeLevelArc_boundary_iff hr ht htr i _).mpr (by split_ifs <;> simp),
      negativeLevelArc_height ht i _⟩

theorem negativeLevelContact_injective {r t : Real}
    (hr : 0 < r) (htr : t < r ^ 2) : Function.Injective (negativeLevelContact r t) :=
  saddleCoordinateSwap_injective.comp (positiveLevelContact_injective hr htr)

end Poincare.Manifold.Schoenflies.SaddleLevel
