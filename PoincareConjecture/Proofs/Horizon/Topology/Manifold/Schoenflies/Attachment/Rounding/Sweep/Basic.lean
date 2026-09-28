import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Rounding

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]

def sweepMap (p : E × Real) : E × Real :=
  (((1 + p.2 ^ 2) / (1 + p.2 ^ 2 * ‖p.1‖ ^ 2)) • p.1,
    p.2 * (1 - ‖p.1‖ ^ 2) / (1 + p.2 ^ 2 * ‖p.1‖ ^ 2))

private theorem sweep_den_pos (x : E) (k : Real) :
    0 < 1 + k ^ 2 * ‖x‖ ^ 2 := by positivity

theorem contDiff_sweepMap : ContDiff Real ∞ (sweepMap : E × Real → E × Real) := by
  have hd : ContDiff Real ∞ (fun p : E × Real => 1 + p.2 ^ 2 * ‖p.1‖ ^ 2) :=
    contDiff_const.add ((contDiff_snd.pow 2).mul (contDiff_fst.norm_sq Real))
  exact (((contDiff_const.add (contDiff_snd.pow 2)).div hd
    (fun p => (sweep_den_pos p.1 p.2).ne')).smul contDiff_fst).prodMk
    ((contDiff_snd.mul (contDiff_const.sub (contDiff_fst.norm_sq Real))).div hd
      (fun p => (sweep_den_pos p.1 p.2).ne'))

theorem sweepMap_fst_norm_sq (x : E) (k : Real) :
    ‖(sweepMap (x, k)).1‖ ^ 2 =
      ((1 + k ^ 2) / (1 + k ^ 2 * ‖x‖ ^ 2)) ^ 2 * ‖x‖ ^ 2 := by
  simp only [sweepMap, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem sweepMap_quadratic (x : E) (k q : Real) :
    ‖(sweepMap (x, k)).1‖ ^ 2 + (sweepMap (x, k)).2 ^ 2 +
      2 * q * (sweepMap (x, k)).2 - 1 =
      ((1 - ‖x‖ ^ 2) / (1 + k ^ 2 * ‖x‖ ^ 2)) * (k ^ 2 + 2 * q * k - 1) := by
  rw [sweepMap_fst_norm_sq]
  simp only [sweepMap]
  field_simp [(sweep_den_pos x k).ne']
  <;> ring

def sweepTarget : Set (E × Real) := {p | p.2 ≠ 0 ∨ ‖p.1‖ < 1}

theorem isOpen_sweepTarget : IsOpen (sweepTarget : Set (E × Real)) :=
  (isOpen_ne.preimage continuous_snd).union
    (isOpen_lt continuous_fst.norm continuous_const)

def sweepDiscriminant (p : E × Real) : Real :=
  Real.sqrt ((‖p.1‖ ^ 2 + p.2 ^ 2 - 1) ^ 2 + 4 * p.2 ^ 2)

def sweepScale (p : E × Real) : Real :=
  (1 + ‖p.1‖ ^ 2 + p.2 ^ 2 + sweepDiscriminant p) / 2

def sweepInv (p : E × Real) : E × Real :=
  ((sweepScale p)⁻¹ • p.1,
    2 * p.2 / (sweepDiscriminant p - (‖p.1‖ ^ 2 + p.2 ^ 2 - 1)))

private theorem norm_sq_lt_one {x : E} (hx : ‖x‖ < 1) : ‖x‖ ^ 2 < 1 := by
  nlinarith [norm_nonneg x]

theorem sweepDiscriminant_pos {p : E × Real} (hp : p ∈ sweepTarget) :
    0 < sweepDiscriminant p := by
  apply Real.sqrt_pos.mpr
  rcases hp with hp | hp
  · have := sq_pos_of_ne_zero hp
    nlinarith [sq_nonneg (‖p.1‖ ^ 2 + p.2 ^ 2 - 1)]
  · have hn := norm_sq_lt_one hp
    by_cases hw : p.2 = 0
    · rw [hw]
      nlinarith [sq_pos_of_ne_zero (show ‖p.1‖ ^ 2 + (0 : Real) ^ 2 - 1 ≠ 0 by
        nlinarith)]
    · nlinarith [sq_pos_of_ne_zero hw, sq_nonneg (‖p.1‖ ^ 2 + p.2 ^ 2 - 1)]

theorem sweepDiscriminant_sq (p : E × Real) :
    sweepDiscriminant p ^ 2 = (‖p.1‖ ^ 2 + p.2 ^ 2 - 1) ^ 2 + 4 * p.2 ^ 2 := by
  apply Real.sq_sqrt
  positivity

theorem sweepInv_den_pos {p : E × Real} (hp : p ∈ sweepTarget) :
    0 < sweepDiscriminant p - (‖p.1‖ ^ 2 + p.2 ^ 2 - 1) := by
  have hs := sweepDiscriminant_sq p
  have hd := sweepDiscriminant_pos hp
  rcases hp with hp | hp
  · nlinarith [sq_pos_of_ne_zero hp]
  · have hn := norm_sq_lt_one hp
    by_cases hw : p.2 = 0
    · rw [hw] at hs ⊢
      nlinarith
    · nlinarith [sq_pos_of_ne_zero hw]

theorem sweepScale_pos (p : E × Real) : 0 < sweepScale p := by
  unfold sweepScale sweepDiscriminant
  positivity

theorem sweepMap_mem_target (x : E) (k : Real) (hx : ‖x‖ < 1) :
    sweepMap (x, k) ∈ sweepTarget := by
  by_cases hk : k = 0
  · subst k
    right
    simpa [sweepMap] using hx
  · left
    exact div_ne_zero (mul_ne_zero hk (ne_of_gt (sub_pos.mpr (norm_sq_lt_one hx))))
      (sweep_den_pos x k).ne'

theorem sweepDiscriminant_map (x : E) (k : Real) (hx : ‖x‖ < 1) :
    sweepDiscriminant (sweepMap (x, k)) =
      (1 + k ^ 2) * (1 - ‖x‖ ^ 2) / (1 + k ^ 2 * ‖x‖ ^ 2) := by
  have hs := sweepDiscriminant_sq (sweepMap (x, k))
  have he : (‖(sweepMap (x, k)).1‖ ^ 2 + (sweepMap (x, k)).2 ^ 2 - 1) ^ 2 +
      4 * (sweepMap (x, k)).2 ^ 2 =
      ((1 + k ^ 2) * (1 - ‖x‖ ^ 2) / (1 + k ^ 2 * ‖x‖ ^ 2)) ^ 2 := by
    rw [sweepMap_fst_norm_sq]
    simp only [sweepMap]
    field_simp [(sweep_den_pos x k).ne']
    <;> ring
  rw [he] at hs
  have hd := sweepDiscriminant_pos (sweepMap_mem_target x k hx)
  have hv : 0 < (1 + k ^ 2) * (1 - ‖x‖ ^ 2) / (1 + k ^ 2 * ‖x‖ ^ 2) :=
    div_pos (mul_pos (by positivity) (sub_pos.mpr (norm_sq_lt_one hx)))
      (sweep_den_pos x k)
  nlinarith

theorem sweepScale_map (x : E) (k : Real) (hx : ‖x‖ < 1) :
    sweepScale (sweepMap (x, k)) = (1 + k ^ 2) / (1 + k ^ 2 * ‖x‖ ^ 2) := by
  unfold sweepScale
  rw [sweepDiscriminant_map x k hx, sweepMap_fst_norm_sq]
  simp only [sweepMap]
  field_simp [(sweep_den_pos x k).ne']
  <;> ring

theorem sweepInv_map (x : E) (k : Real) (hx : ‖x‖ < 1) :
    sweepInv (sweepMap (x, k)) = (x, k) := by
  apply Prod.ext
  · change (sweepScale (sweepMap (x, k)))⁻¹ • (sweepMap (x, k)).1 = x
    rw [sweepScale_map x k hx]
    change ((1 + k ^ 2) / (1 + k ^ 2 * ‖x‖ ^ 2))⁻¹ •
      (((1 + k ^ 2) / (1 + k ^ 2 * ‖x‖ ^ 2)) • x) = x
    rw [smul_smul, inv_mul_cancel₀ (div_ne_zero (by positivity)
      (sweep_den_pos x k).ne'), one_smul]
  · change 2 * (sweepMap (x, k)).2 /
      (sweepDiscriminant (sweepMap (x, k)) -
        (‖(sweepMap (x, k)).1‖ ^ 2 + (sweepMap (x, k)).2 ^ 2 - 1)) = k
    apply (div_eq_iff (sweepInv_den_pos (sweepMap_mem_target x k hx)).ne').mpr
    rw [sweepDiscriminant_map x k hx, sweepMap_fst_norm_sq]
    simp only [sweepMap]
    field_simp [(sweep_den_pos x k).ne']
    <;> ring

private theorem sweepScale_sq (p : E × Real) :
    sweepScale p ^ 2 - ‖p.1‖ ^ 2 = sweepScale p * sweepDiscriminant p := by
  have hs := sweepDiscriminant_sq p
  unfold sweepScale
  nlinarith

private theorem sweepScale_eq {p : E × Real} (hp : p ∈ sweepTarget) :
    sweepScale p = 1 + (sweepInv p).2 * p.2 := by
  have hs := sweepDiscriminant_sq p
  have hd := (sweepInv_den_pos hp).ne'
  change sweepScale p = 1 + (2 * p.2 /
    (sweepDiscriminant p - (‖p.1‖ ^ 2 + p.2 ^ 2 - 1))) * p.2
  unfold sweepScale
  field_simp
  <;> nlinarith

private theorem sweepInv_height_relation {p : E × Real} (hp : p ∈ sweepTarget) :
    (sweepInv p).2 * sweepDiscriminant p = (1 + (sweepInv p).2 ^ 2) * p.2 := by
  have hs := sweepDiscriminant_sq p
  have hd := (sweepInv_den_pos hp).ne'
  change (2 * p.2 / (sweepDiscriminant p - (‖p.1‖ ^ 2 + p.2 ^ 2 - 1))) *
    sweepDiscriminant p =
      (1 + (2 * p.2 / (sweepDiscriminant p - (‖p.1‖ ^ 2 + p.2 ^ 2 - 1))) ^ 2) * p.2
  field_simp
  <;> linear_combination p.2 * hs

theorem sweepInv_mem_source {p : E × Real} (hp : p ∈ sweepTarget) :
    ‖(sweepInv p).1‖ < 1 := by
  have hl := sweepScale_pos p
  have hs := sweepScale_sq p
  have hd := sweepDiscriminant_pos hp
  have hn : ‖p.1‖ < sweepScale p := by
    nlinarith [norm_nonneg p.1, mul_pos hl hd]
  change ‖(sweepScale p)⁻¹ • p.1‖ < 1
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hl, ← div_eq_inv_mul,
    div_lt_one hl]
  exact hn

theorem sweepMap_inv {p : E × Real} (hp : p ∈ sweepTarget) :
    sweepMap (sweepInv p) = p := by
  let n := ‖p.1‖ ^ 2
  let k := (sweepInv p).2
  let a := sweepScale p
  let d := sweepDiscriminant p
  have ha : 0 < a := sweepScale_pos p
  have hsq : a ^ 2 - n = a * d := sweepScale_sq p
  have hae : a = 1 + k * p.2 := sweepScale_eq hp
  have hke : k * d = (1 + k ^ 2) * p.2 := sweepInv_height_relation hp
  have hnorm : ‖(sweepInv p).1‖ ^ 2 = n / a ^ 2 := by
    change ‖a⁻¹ • p.1‖ ^ 2 = _
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simp [n, div_eq_mul_inv, mul_comm]
  have hden : a ^ 2 + k ^ 2 * n = a * (1 + k ^ 2) := by
    linear_combination (1 + k ^ 2) * a * hae - k * a * hke - k ^ 2 * hsq
  have hfac : (1 + k ^ 2) / (1 + k ^ 2 * (n / a ^ 2)) = a := by
    apply (div_eq_iff (by positivity : 1 + k ^ 2 * (n / a ^ 2) ≠ 0)).mpr
    field_simp
    nlinarith [ha]
  apply Prod.ext
  · change ((1 + k ^ 2) / (1 + k ^ 2 * ‖(sweepInv p).1‖ ^ 2)) •
      (a⁻¹ • p.1) = p.1
    rw [hnorm, hfac, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  · change k * (1 - ‖(sweepInv p).1‖ ^ 2) /
      (1 + k ^ 2 * ‖(sweepInv p).1‖ ^ 2) = p.2
    rw [hnorm]
    apply (div_eq_iff (by positivity : 1 + k ^ 2 * (n / a ^ 2) ≠ 0)).mpr
    field_simp
    linear_combination k * hsq + a * hke - p.2 * hden

theorem contDiffOn_sweepInv :
    ContDiffOn Real ∞ (sweepInv : E × Real → E × Real) sweepTarget := by
  intro p hp
  have hL : ContDiffAt Real ∞ (fun y : E × Real => ‖y.1‖ ^ 2 + y.2 ^ 2 - 1) p :=
    ((contDiffAt_fst.norm_sq Real).add (contDiffAt_snd.pow 2)).sub contDiffAt_const
  have hD : ContDiffAt Real ∞ (sweepDiscriminant : E × Real → Real) p := by
    apply ((hL.pow 2).add (contDiffAt_const.mul (contDiffAt_snd.pow 2))).sqrt
    exact (Real.sqrt_pos.mp (sweepDiscriminant_pos hp)).ne'
  have hA : ContDiffAt Real ∞ (sweepScale : E × Real → Real) p :=
    (((contDiffAt_const.add (contDiffAt_fst.norm_sq Real)).add
      (contDiffAt_snd.pow 2)).add hD).div_const 2
  exact (((hA.inv (sweepScale_pos p).ne').smul contDiffAt_fst).prodMk
    ((contDiffAt_const.mul contDiffAt_snd).div (hD.sub hL)
      (sweepInv_den_pos hp).ne')).contDiffWithinAt

def sweepPartialHomeomorph : OpenPartialHomeomorph (E × Real) (E × Real) where
  toFun := sweepMap
  invFun := sweepInv
  source := {p | ‖p.1‖ < 1}
  target := sweepTarget
  map_source' p hp := sweepMap_mem_target p.1 p.2 hp
  map_target' _ hp := sweepInv_mem_source hp
  left_inv' p hp := sweepInv_map p.1 p.2 hp
  right_inv' _ hp := sweepMap_inv hp
  open_source := isOpen_lt continuous_fst.norm continuous_const
  open_target := isOpen_sweepTarget
  continuousOn_toFun := contDiff_sweepMap.continuous.continuousOn
  continuousOn_invFun := contDiffOn_sweepInv.continuousOn

def sweepRange : TopologicalSpace.Opens (E × Real) :=
  ⟨sweepTarget, isOpen_sweepTarget⟩

def sweepParametrization :
    Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
      (E × Real) (sweepRange (E := E)) ∞ := by
  let u : OpenPartialHomeomorph E E := OpenPartialHomeomorph.univUnitBall
  have hu (x : E) : ‖u x‖ < 1 := mem_ball_zero_iff.mp (u.map_source (mem_univ x))
  let f : E × Real → sweepRange (E := E) := fun p =>
    ⟨sweepMap (u p.1, p.2), sweepMap_mem_target _ _ (hu _)⟩
  let g : sweepRange (E := E) → E × Real := fun q =>
    (u.symm (sweepInv (q : E × Real)).1, (sweepInv (q : E × Real)).2)
  have hleft : Function.LeftInverse g f := by
    rintro ⟨x, k⟩
    change (u.symm (sweepInv (sweepMap (u x, k))).1,
      (sweepInv (sweepMap (u x, k))).2) = (x, k)
    rw [sweepInv_map _ _ (hu x), u.left_inv (mem_univ x)]
  have hright : Function.RightInverse g f := by
    intro q
    apply Subtype.ext
    change sweepMap (u (u.symm (sweepInv (q : E × Real)).1),
      (sweepInv (q : E × Real)).2) = q
    rw [u.right_inv (mem_ball_zero_iff.mpr (sweepInv_mem_source q.property))]
    exact sweepMap_inv q.property
  have hf : ContMDiff 𝓘(Real, E × Real) 𝓘(Real, E × Real) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff (sweepRange (E := E)) f).mp
    exact (contDiff_sweepMap.comp
      ((OpenPartialHomeomorph.contDiff_univUnitBall.comp contDiff_fst).prodMk
        contDiff_snd)).contMDiff
  have hsi : ContMDiff 𝓘(Real, E × Real) 𝓘(Real, E × Real) ∞
      (fun q : sweepRange (E := E) => sweepInv (q : E × Real)) := by
    intro q
    exact (((contDiffOn_sweepInv (q : E × Real) q.property).contDiffAt
      (isOpen_sweepTarget.mem_nhds q.property)).contMDiffAt).comp q
        (contMDiff_subtype_val q)
  have hg : ContMDiff 𝓘(Real, E × Real) 𝓘(Real, E × Real) ∞ g := by
    have huinv : ∀ x ∈ ball (0 : E) 1, ContDiffAt Real ∞ u.symm x :=
      fun x hx => (OpenPartialHomeomorph.contDiffOn_univUnitBall_symm x hx).contDiffAt
        (isOpen_ball.mem_nhds hx)
    have hfirst : ContMDiff 𝓘(Real, E × Real) 𝓘(Real, E) ∞
        (fun q : sweepRange (E := E) => u.symm (sweepInv (q : E × Real)).1) := by
      intro q
      exact (huinv _ (mem_ball_zero_iff.mpr (sweepInv_mem_source q.property))).contMDiffAt.comp
        q ((contDiff_fst.contMDiff.comp hsi) q)
    have h := hfirst.prodMk (contDiff_snd.contMDiff.comp hsi)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h
  exact ⟨⟨f, g, hleft, hright⟩, hf, hg⟩

@[simp] theorem sweepParametrization_apply (p : E × Real) :
    (sweepParametrization p : E × Real) =
      sweepMap (OpenPartialHomeomorph.univUnitBall p.1, p.2) := rfl

theorem sweepMap_mem_quadratic_iff (x : E) (k q : Real) (hx : ‖x‖ < 1) :
    ‖(sweepMap (x, k)).1‖ ^ 2 + ((sweepMap (x, k)).2 + q) ^ 2 ≤ 1 + q ^ 2 ↔
      k ∈ Icc (-q - Real.sqrt (q ^ 2 + 1)) (-q + Real.sqrt (q ^ 2 + 1)) := by
  have hf : 0 < (1 - ‖x‖ ^ 2) / (1 + k ^ 2 * ‖x‖ ^ 2) :=
    div_pos (sub_pos.mpr (norm_sq_lt_one hx)) (sweep_den_pos x k)
  have hquadratic :
      ‖(sweepMap (x, k)).1‖ ^ 2 + ((sweepMap (x, k)).2 + q) ^ 2 ≤ 1 + q ^ 2 ↔
        k ^ 2 + 2 * q * k - 1 ≤ 0 := by
    have h := sweepMap_quadratic x k q
    constructor
    · intro hb
      have hm : ((1 - ‖x‖ ^ 2) / (1 + k ^ 2 * ‖x‖ ^ 2)) *
          (k ^ 2 + 2 * q * k - 1) ≤ 0 := by nlinarith
      nlinarith
    · intro hb
      have := mul_nonpos_of_nonneg_of_nonpos hf.le hb
      nlinarith
  rw [hquadratic]
  have hs : Real.sqrt (q ^ 2 + 1) ^ 2 = q ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have he : k ^ 2 + 2 * q * k - 1 ≤ 0 ↔
      (k + q) ^ 2 ≤ Real.sqrt (q ^ 2 + 1) ^ 2 := by
    rw [hs]
    constructor <;> intro h <;> nlinarith
  rw [he, sq_le_sq, abs_of_nonneg (Real.sqrt_nonneg _), abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

def sweepHeightChange (q : Real) :
    Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real) (E × Real) (E × Real) ∞ := by
  let a := Real.sqrt (q ^ 2 + 1)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  exact {
    toFun := fun p => (p.1, -q + a - 2 * a * p.2)
    invFun := fun p => (p.1, (-q + a - p.2) / (2 * a))
    left_inv := by
      intro p
      apply Prod.ext
      · rfl
      change (-q + a - (-q + a - 2 * a * p.2)) / (2 * a) = p.2
      field_simp
      <;> ring
    right_inv := by
      intro p
      apply Prod.ext
      · rfl
      change -q + a - 2 * a * ((-q + a - p.2) / (2 * a)) = p.2
      field_simp
      <;> ring
    contMDiff_toFun := (contDiff_fst.prodMk
      (contDiff_const.sub (contDiff_const.mul contDiff_snd))).contMDiff
    contMDiff_invFun := (contDiff_fst.prodMk
      ((contDiff_const.sub contDiff_snd).div_const (2 * a))).contMDiff }

def capSweepParametrization (q : Real) :
    Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
      (E × Real) (sweepRange (E := E)) ∞ :=
  (sweepHeightChange q).trans sweepParametrization

@[simp] theorem capSweepParametrization_apply (q : Real) (p : E × Real) :
    (capSweepParametrization q p : E × Real) =
      sweepMap (OpenPartialHomeomorph.univUnitBall p.1,
        -q + Real.sqrt (q ^ 2 + 1) - 2 * Real.sqrt (q ^ 2 + 1) * p.2) := rfl

theorem capSweepParametrization_mem_quadratic_iff (q : Real) (p : E × Real) :
    ‖(capSweepParametrization q p : E × Real).1‖ ^ 2 +
      ((capSweepParametrization q p : E × Real).2 + q) ^ 2 ≤ 1 + q ^ 2 ↔
      p.2 ∈ Icc (0 : Real) 1 := by
  rw [capSweepParametrization_apply]
  rw [sweepMap_mem_quadratic_iff _ _ _ (mem_ball_zero_iff.mp
    (OpenPartialHomeomorph.univUnitBall.map_source (mem_univ p.1)))]
  have ha : 0 < Real.sqrt (q ^ 2 + 1) := Real.sqrt_pos.mpr (by positivity)
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith

theorem capSweepParametrization_mem_quadratic_interior_iff (q : Real) (p : E × Real) :
    ‖(capSweepParametrization q p : E × Real).1‖ ^ 2 +
      ((capSweepParametrization q p : E × Real).2 + q) ^ 2 < 1 + q ^ 2 ↔
      p.2 ∈ Ioo (0 : Real) 1 := by
  let x : E := OpenPartialHomeomorph.univUnitBall p.1
  let a := Real.sqrt (q ^ 2 + 1)
  let k := -q + a - 2 * a * p.2
  have hx : ‖x‖ < 1 := mem_ball_zero_iff.mp
    (OpenPartialHomeomorph.univUnitBall.map_source (mem_univ p.1))
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hasq : a ^ 2 = q ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hf : 0 < (1 - ‖x‖ ^ 2) / (1 + k ^ 2 * ‖x‖ ^ 2) :=
    div_pos (sub_pos.mpr (norm_sq_lt_one hx)) (sweep_den_pos x k)
  have h := sweepMap_quadratic x k q
  change ‖(sweepMap (x, k)).1‖ ^ 2 + ((sweepMap (x, k)).2 + q) ^ 2 <
    1 + q ^ 2 ↔ _
  have he : ‖(sweepMap (x, k)).1‖ ^ 2 + ((sweepMap (x, k)).2 + q) ^ 2 <
      1 + q ^ 2 ↔ k ^ 2 + 2 * q * k - 1 < 0 := by
    constructor
    · intro hb
      by_contra hn
      have := mul_nonneg hf.le (le_of_not_gt hn)
      nlinarith
    · intro hb
      have := mul_neg_of_pos_of_neg hf hb
      nlinarith
  rw [he]
  have hk : k ^ 2 + 2 * q * k - 1 = 4 * a ^ 2 * (p.2 * (p.2 - 1)) := by
    dsimp only [k]
    nlinarith [hasq]
  rw [hk]
  have hc : 0 < 4 * a ^ 2 := by positivity
  constructor
  · intro ht
    have hn : p.2 * (p.2 - 1) < 0 := by nlinarith
    constructor <;> nlinarith
  · rintro ⟨ht0, ht1⟩
    exact mul_neg_of_pos_of_neg hc (mul_neg_of_pos_of_neg ht0 (sub_neg.mpr ht1))

theorem capSweepParametrization_image_boundary_zero (q : Real) :
    (fun p : E => (capSweepParametrization q (p, 0) : E × Real)) '' univ =
      {p | ‖p.1‖ ^ 2 + (p.2 + q) ^ 2 = 1 + q ^ 2 ∧ 0 < p.2} := by
  have hslice (p : E × Real) :
      ‖(capSweepParametrization q p : E × Real).1‖ ^ 2 +
        ((capSweepParametrization q p : E × Real).2 + q) ^ 2 = 1 + q ^ 2 ∧
        0 < (capSweepParametrization q p : E × Real).2 ↔ p.2 = 0 := by
    let x : E := OpenPartialHomeomorph.univUnitBall p.1
    let a := Real.sqrt (q ^ 2 + 1)
    let k := -q + a - 2 * a * p.2
    have hx : ‖x‖ < 1 := mem_ball_zero_iff.mp
      (OpenPartialHomeomorph.univUnitBall.map_source (mem_univ p.1))
    have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
    have hasq : a ^ 2 = q ^ 2 + 1 := Real.sq_sqrt (by positivity)
    have haq : q < a := by nlinarith
    have haq' : -a < q := by nlinarith
    have hf : 0 < (1 - ‖x‖ ^ 2) / (1 + k ^ 2 * ‖x‖ ^ 2) :=
      div_pos (sub_pos.mpr (norm_sq_lt_one hx)) (sweep_den_pos x k)
    have h := sweepMap_quadratic x k q
    have hz : (sweepMap (x, k)).2 = k *
        ((1 - ‖x‖ ^ 2) / (1 + k ^ 2 * ‖x‖ ^ 2)) := by simp [sweepMap, mul_div_assoc]
    change (‖(sweepMap (x, k)).1‖ ^ 2 + ((sweepMap (x, k)).2 + q) ^ 2 =
      1 + q ^ 2 ∧ 0 < (sweepMap (x, k)).2) ↔ _
    constructor
    · rintro ⟨hb, hw⟩
      have hpoly : k ^ 2 + 2 * q * k - 1 = 0 := by nlinarith
      have hkpos : 0 < k := by rw [hz] at hw; nlinarith
      have hfactor : (k + q - a) * (k + q + a) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfactor with he | he
      · dsimp only [k] at he
        nlinarith
      · nlinarith
    · intro hp
      have hk : k = -q + a := by simp [k, hp]
      have hpoly : k ^ 2 + 2 * q * k - 1 = 0 := by rw [hk]; nlinarith
      constructor
      · rw [hpoly, mul_zero] at h
        nlinarith
      · rw [hz]
        exact mul_pos (by rw [hk]; linarith) hf
  ext y
  constructor
  · rintro ⟨x, _, rfl⟩
    exact (hslice (x, 0)).mpr rfl
  · intro hy
    let z : sweepRange (E := E) := ⟨y, Or.inl (ne_of_gt hy.2)⟩
    let p := (capSweepParametrization q).symm z
    have hp : p.2 = 0 := (hslice p).mp (by
      change _ ∧ _
      simpa only [p, Diffeomorph.apply_symm_apply, z, mem_ofPred_eq] using hy)
    refine ⟨p.1, mem_univ _, ?_⟩
    rw [← hp]
    exact congrArg Subtype.val ((capSweepParametrization q).apply_symm_apply z)

theorem capSweepParametrization_image_slab (q : Real) :
    (fun p : E × Real => (capSweepParametrization q p : E × Real)) ''
        {p | p.2 ∈ Icc (0 : Real) 1} =
      {p | ‖p.1‖ ^ 2 + (p.2 + q) ^ 2 ≤ 1 + q ^ 2} ∩ sweepTarget := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(capSweepParametrization_mem_quadratic_iff q z).mpr hz,
      (capSweepParametrization q z).property⟩
  · rintro ⟨hp, hpt⟩
    let y : sweepRange (E := E) := ⟨p, hpt⟩
    refine ⟨(capSweepParametrization q).symm y, ?_, ?_⟩
    · apply (capSweepParametrization_mem_quadratic_iff q _).mp
      rw [Diffeomorph.apply_symm_apply]
      exact hp
    · exact congrArg Subtype.val ((capSweepParametrization q).apply_symm_apply y)

end Poincare.Manifold.Schoenflies.Rounding
