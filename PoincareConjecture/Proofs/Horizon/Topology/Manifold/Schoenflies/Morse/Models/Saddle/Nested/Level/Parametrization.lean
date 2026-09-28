import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Level.Components
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional
import Mathlib.Geometry.Manifold.Algebra.Structures







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

private def ovalParameter (a b : Real) (p : S1) : Real :=
  (a + b) / 2 + (b - a) / 2 * (p : E2) 0

private theorem ovalParameter_mem {a b : Real} (hab : a < b) (p : S1) :
    ovalParameter a b p ∈ Icc a b := by
  have hn : ((p : E2) 0)^2 + ((p : E2) 1)^2 = 1 := by
    rw [← norm_sq_two]
    simp
  have hx : -1 ≤ (p : E2) 0 ∧ (p : E2) 0 ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg ((p : E2) 1)]
  dsimp [ovalParameter]
  constructor <;> nlinarith [hx.1, hx.2]

private def ovalCircle (a b : Real) (H : Real → Real) (p : S1) : E2 :=
  levelAbscissa (ovalParameter a b p) • EuclideanSpace.single 0 1 +
    ((b - a) / 2 * (p : E2) 1 * Real.sqrt (H (ovalParameter a b p))) •
      EuclideanSpace.single 1 1

private theorem ovalCircle_zero (a b : Real) (H : Real → Real) (p : S1) :
    ovalCircle a b H p 0 = levelAbscissa (ovalParameter a b p) := by simp [ovalCircle]

private theorem ovalCircle_one (a b : Real) (H : Real → Real) (p : S1) :
    ovalCircle a b H p 1 = (b - a) / 2 * (p : E2) 1 *
      Real.sqrt (H (ovalParameter a b p)) := by simp [ovalCircle]

private theorem ovalCircle_y_sq {a b : Real} (hab : a < b) {H : Real → Real}
    (hH : ∀ z ∈ Icc a b, 0 < H z)
    (hfactor : ∀ z, levelRadicand z = (z - a) * (b - z) * H z) (p : S1) :
    (ovalCircle a b H p 1)^2 = levelRadicand (ovalParameter a b p) := by
  have hn : ((p : E2) 0)^2 + ((p : E2) 1)^2 = 1 := by
    rw [← norm_sq_two]
    simp
  have hroot := Real.sq_sqrt (hH _ (ovalParameter_mem hab p)).le
  rw [ovalCircle_one, mul_pow, hroot, hfactor]
  have hc : ((b - a) / 2 * (p : E2) 1)^2 =
      (ovalParameter a b p - a) * (b - ovalParameter a b p) := by
    dsimp [ovalParameter]
    nlinarith [sq_nonneg ((b - a) / 2)]
  rw [hc]

private theorem sourceHeight_ovalCircle {a b : Real} (hab : a < b) {H : Real → Real}
    (hH : ∀ z ∈ Icc a b, 0 < H z)
    (hfactor : ∀ z, levelRadicand z = (z - a) * (b - z) * H z) (p : S1) :
    sourceHeight (ovalCircle a b H p) = ovalParameter a b p := by
  dsimp [sourceHeight]
  rw [ovalCircle_zero, ovalCircle_y_sq hab hH hfactor]
  dsimp [levelRadicand, levelAbscissa]
  ring

private theorem ovalCircle_contMDiff {a b : Real} (hab : a < b) {H : Real → Real}
    (hH : ContDiff Real ∞ H) (hpos : ∀ z ∈ Icc a b, 0 < H z) :
    ContMDiff (𝓡 1) (𝓡 2) ∞ (ovalCircle a b H) := by
  have hz : ContMDiff (𝓡 1) 𝓘(Real, Real) ∞ (ovalParameter a b) :=
    contMDiff_const.add (contMDiff_const.mul
      ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contMDiff.comp
        (contMDiff_coe_sphere (n := 1))))
  have hy : ContMDiff (𝓡 1) 𝓘(Real, Real) ∞ (fun p : S1 => (p : E2) 1) :=
    (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contMDiff.comp
      (contMDiff_coe_sphere (n := 1))
  have hs : ContMDiff (𝓡 1) 𝓘(Real, Real) ∞
      (fun p => Real.sqrt (H (ovalParameter a b p))) := by
    intro p
    exact (Real.contDiffAt_sqrt (hpos _ (ovalParameter_mem hab p)).ne').contMDiffAt.comp p
      ((hH.contMDiff.comp hz) p)
  exact (((by unfold levelAbscissa; fun_prop : ContDiff Real ∞ levelAbscissa).contMDiff.comp hz).smul
    contMDiff_const).add (((contMDiff_const.mul hy).mul hs).smul contMDiff_const)

private def ovalInverse (a b : Real) (H : Real → Real) (q : E2) : E2 :=
  ((sourceHeight q - (a + b) / 2) / ((b - a) / 2)) • EuclideanSpace.single 0 1 +
    (q 1 / (((b - a) / 2) * Real.sqrt (H (sourceHeight q)))) • EuclideanSpace.single 1 1

private theorem ovalInverse_zero (a b : Real) (H : Real → Real) (q : E2) :
    ovalInverse a b H q 0 = (sourceHeight q - (a + b) / 2) / ((b - a) / 2) := by
  simp [ovalInverse]

private theorem ovalInverse_one (a b : Real) (H : Real → Real) (q : E2) :
    ovalInverse a b H q 1 = q 1 / (((b - a) / 2) * Real.sqrt (H (sourceHeight q))) := by
  simp [ovalInverse]

private theorem ovalInverse_apply_circle {a b : Real} (hab : a < b) {H : Real → Real}
    (hpos : ∀ z ∈ Icc a b, 0 < H z)
    (hfactor : ∀ z, levelRadicand z = (z - a) * (b - z) * H z) (p : S1) :
    ovalInverse a b H (ovalCircle a b H p) = (p : E2) := by
  have hd : (b - a) / 2 ≠ 0 := by linarith
  have hba : b - a ≠ 0 := by linarith
  have hs : Real.sqrt (H (ovalParameter a b p)) ≠ 0 :=
    (Real.sqrt_pos.mpr (hpos _ (ovalParameter_mem hab p))).ne'
  ext i
  fin_cases i
  · simp [ovalInverse, sourceHeight_ovalCircle hab hpos hfactor, ovalParameter, hd]
  · change ovalInverse a b H (ovalCircle a b H p) 1 = (p : E2) 1
    rw [ovalInverse_one, sourceHeight_ovalCircle hab hpos hfactor, ovalCircle_one]
    field_simp [hba]

private theorem ovalInverse_contDiffAt {a b : Real} (hab : a < b) {H : Real → Real}
    (hH : ContDiff Real ∞ H) (q : E2) (hq : 0 < H (sourceHeight q)) :
    ContDiffAt Real ∞ (ovalInverse a b H) q := by
  have hz : ContDiff Real ∞ sourceHeight := by unfold sourceHeight; fun_prop
  have hs : ContDiffAt Real ∞ (fun q => Real.sqrt (H (sourceHeight q))) q :=
    (Real.contDiffAt_sqrt hq.ne').comp q ((hH.comp hz).contDiffAt)
  have hd : (b - a) / 2 ≠ 0 := by linarith
  have hden : ((b - a) / 2) * Real.sqrt (H (sourceHeight q)) ≠ 0 :=
    mul_ne_zero hd (Real.sqrt_pos.mpr hq).ne'
  exact ((((hz.contDiffAt.sub contDiffAt_const).div_const _).smul contDiffAt_const).add
    ((((EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff.contDiffAt).div
      (contDiffAt_const.mul hs) hden).smul contDiffAt_const))

private theorem ovalCircle_isSmoothEmbedding {a b : Real} (hab : a < b) {H : Real → Real}
    (hH : ContDiff Real ∞ H) (hpos : ∀ z ∈ Icc a b, 0 < H z)
    (hfactor : ∀ z, levelRadicand z = (z - a) * (b - z) * H z) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (ovalCircle a b H) := by
  have hγ := ovalCircle_contMDiff hab hH hpos
  have heq : ovalInverse a b H ∘ ovalCircle a b H = (Subtype.val : S1 → E2) :=
    funext (ovalInverse_apply_circle hab hpos hfactor)
  have hinj : Injective (ovalCircle a b H) := by
    intro p q hpq
    apply Subtype.val_injective
    rw [← ovalInverse_apply_circle hab hpos hfactor p,
      ← ovalInverse_apply_circle hab hpos hfactor q, hpq]
  apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv hγ hinj
  intro p
  have hi := ovalInverse_contDiffAt hab hH (ovalCircle a b H p)
    (by rw [sourceHeight_ovalCircle hab hpos hfactor]; exact hpos _ (ovalParameter_mem hab p))
  have hd : (mfderiv (𝓡 2) (𝓡 2) (ovalInverse a b H) (ovalCircle a b H p)).comp
      (mfderiv (𝓡 1) (𝓡 2) (ovalCircle a b H) p) =
      mfderiv (𝓡 1) (𝓡 2) (Subtype.val : S1 → E2) p := by
    rw [← mfderiv_comp p (hi.differentiableAt (by simp)).mdifferentiableAt
      (hγ.mdifferentiable (by simp) p), heq]
  have hc : Injective ((mfderiv (𝓡 2) (𝓡 2) (ovalInverse a b H) (ovalCircle a b H p)).comp
      (mfderiv (𝓡 1) (𝓡 2) (ovalCircle a b H) p)) := by
    rw [hd]
    convert! injective_mvfderiv_subtypeVal_sphere p
  intro u v huv
  apply hc
  change (mfderiv (𝓡 2) (𝓡 2) (ovalInverse a b H) (ovalCircle a b H p))
      ((mfderiv (𝓡 1) (𝓡 2) (ovalCircle a b H) p) u) = _
  rw [huv]
  rfl

private theorem levelArc_mem_range_ovalCircle {a b : Real} (hab : a < b) {H : Real → Real}
    (hpos : ∀ z ∈ Icc a b, 0 < H z)
    (hfactor : ∀ z, levelRadicand z = (z - a) * (b - z) * H z)
    {z σ : Real} (hz : z ∈ Icc a b) (hσ : σ^2 = 1) :
    levelArc σ z ∈ range (ovalCircle a b H) := by
  have hr : 0 ≤ levelRadicand z := by
    rw [hfactor]
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hz.1) (sub_nonneg.mpr hz.2)) (hpos z hz).le
  have hs := sourceHeight_levelArc hσ hr
  have hd : (b - a) / 2 ≠ 0 := by linarith
  have hba : b - a ≠ 0 := by linarith
  have hH : Real.sqrt (H z) ≠ 0 := (Real.sqrt_pos.mpr (hpos z hz)).ne'
  have hHsq := Real.sq_sqrt (hpos z hz).le
  have hyr : (levelArc σ z 1)^2 = levelRadicand z := by
    rw [levelArc_one, mul_pow, hσ, one_mul, Real.sq_sqrt hr]
  let q := ovalInverse a b H (levelArc σ z)
  have hqn : ‖q‖^2 = 1 := by
    rw [norm_sq_two]
    simp only [q, ovalInverse_zero, ovalInverse_one]
    rw [hs]
    field_simp [hba]
    rw [hHsq, hyr, hfactor]
    ring
  have hq : q ∈ sphere (0 : E2) 1 := by
    rw [mem_sphere_zero_iff_norm]
    nlinarith [norm_nonneg q]
  let p : S1 := ⟨q, hq⟩
  have hpz : ovalParameter a b p = z := by
    simp [ovalParameter, p, q, ovalInverse, hs]
    field_simp
    ring
  refine ⟨p, ?_⟩
  ext i
  fin_cases i
  · change ovalCircle a b H p 0 = levelArc σ z 0
    rw [ovalCircle_zero, hpz, levelArc_zero]
  · change ovalCircle a b H p 1 = levelArc σ z 1
    rw [ovalCircle_one, hpz]
    simp [p, q, ovalInverse, hs]
    field_simp [hba]

private theorem range_ovalCircle {a b : Real} (hab : a < b) {H : Real → Real}
    (hpos : ∀ z ∈ Icc a b, 0 < H z)
    (hfactor : ∀ z, levelRadicand z = (z - a) * (b - z) * H z) :
    range (ovalCircle a b H) = levelArc 1 '' Icc a b ∪ levelArc (-1) '' Icc a b := by
  apply Subset.antisymm
  · rintro q ⟨p, rfl⟩
    have hy := ovalCircle_y_sq hab hpos hfactor p
    have hs := sourceHeight_ovalCircle hab hpos hfactor p
    have hm : ovalCircle a b H p ∈ levelSet := by
      rw [mem_levelSet_iff, hs, norm_sq_two, ovalCircle_zero, hy]
      dsimp [levelRadicand]
      ring
    rcases levelSet_point_eq_arc hm with he | he
    · exact Or.inl ⟨ovalParameter a b p, ovalParameter_mem hab p, by rw [← hs]; exact he.symm⟩
    · exact Or.inr ⟨ovalParameter a b p, ovalParameter_mem hab p, by rw [← hs]; exact he.symm⟩
  · rintro q (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact levelArc_mem_range_ovalCircle hab hpos hfactor hz (by norm_num)
    · exact levelArc_mem_range_ovalCircle hab hpos hfactor hz (by norm_num)

private def outerWeight (z : Real) : Real := (100 / 9) * (upperRoot - z) * (1 - z)

private def innerWeight (z : Real) : Real := (100 / 9) * (z - lowerRoot) * (z - 3 / 5)

private theorem outerWeight_pos (z : Real) (hz : z ∈ Icc lowerRoot (3 / 5)) :
    0 < outerWeight z := by
  unfold outerWeight
  exact mul_pos (mul_pos (by norm_num) (by linarith [hz.2, upperRoot_bounds.1]))
    (by linarith [hz.2])

private theorem innerWeight_pos (z : Real) (hz : z ∈ Icc upperRoot 1) :
    0 < innerWeight z := by
  unfold innerWeight
  exact mul_pos (mul_pos (by norm_num) (by linarith [hz.1, upperRoot_bounds.1,
    lowerRoot_bounds.2])) (by linarith [hz.1, upperRoot_bounds.1])

private theorem outerWeight_factor (z : Real) :
    levelRadicand z = (z - lowerRoot) * (3 / 5 - z) * outerWeight z := by
  rw [levelRadicand_factor]
  unfold outerWeight
  ring

private theorem innerWeight_factor (z : Real) :
    levelRadicand z = (z - upperRoot) * (1 - z) * innerWeight z := by
  rw [levelRadicand_factor]
  unfold innerWeight
  ring


def outerCircle : S1 → E2 := ovalCircle lowerRoot (3 / 5) outerWeight


def innerCircle : S1 → E2 := ovalCircle upperRoot 1 innerWeight

theorem outerCircle_isSmoothEmbedding :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ outerCircle :=
  ovalCircle_isSmoothEmbedding (lowerRoot_bounds.2.trans (by norm_num))
    (by unfold outerWeight; fun_prop) outerWeight_pos outerWeight_factor

theorem innerCircle_isSmoothEmbedding :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ innerCircle :=
  ovalCircle_isSmoothEmbedding upperRoot_bounds.2
    (by unfold innerWeight; fun_prop) innerWeight_pos innerWeight_factor

theorem range_outerCircle : range outerCircle = outerOval :=
  range_ovalCircle (lowerRoot_bounds.2.trans (by norm_num)) outerWeight_pos outerWeight_factor

theorem range_innerCircle : range innerCircle = innerOval :=
  range_ovalCircle upperRoot_bounds.2 innerWeight_pos innerWeight_factor

end Poincare.Manifold.Schoenflies.Saddle.Nested
