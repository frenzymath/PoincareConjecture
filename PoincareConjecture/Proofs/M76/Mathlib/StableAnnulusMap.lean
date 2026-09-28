import PoincareConjecture.Proofs.M76.Mathlib.CenteredAnnulusChart
import PoincareConjecture.Proofs.M76.Mathlib.PLFiberCompression
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusImage

set_option autoImplicit false

open Set Geometry

namespace PLAnnularStrip

theorem centeredAnnulusMap_middle {L s t : ℝ} (hL : 0 < L)
    (ht : 4 * |t| < L) (hl : 2 * |t| ≤ L / 2 + s)
    (hr : 2 * |t| ≤ L / 2 - s) :
    centeredAnnulusMap L hL ((s : AddCircle (4 * L)), t) = (s, t) := by
  unfold centeredAnnulusMap
  rw [← AddCircle.coe_add, annulusMap_middle hL ht hl (by linarith)]
  exact Prod.ext (by dsimp; ring) rfl

theorem centeredAnnulusMap_snd_mem {L d : ℝ} (hL : 0 < L)
    (hd : 0 ≤ d) (hwidth : 4 * d < L) (z : AddCircle (4 * L))
    {t : ℝ} (ht : t ∈ Icc (-d) d) :
    (centeredAnnulusMap L hL (z, t)).2 ∈ Icc (-d) (L + d) := by
  let q : AddCircle (4 * L) := ((L / 2 : ℝ) : AddCircle (4 * L)) + z
  have hq : annulusMap L hL (q, t) ∈ squareAnnulus L d := by
    rw [← range_annulusMap hL hd hwidth]
    exact ⟨(q, ⟨t, ht⟩), rfl⟩
  exact hq.1.2

end PLAnnularStrip

namespace StableAnnulus

noncomputable def squash : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun z := (z.1, z.2 / 64)
  invFun z := (z.1, 64 * z.2)
  left_inv z := Prod.ext rfl (by dsimp; ring)
  right_inv z := Prod.ext rfl (by dsimp; ring)
  continuous_toFun := continuous_fst.prodMk (continuous_snd.div_const 64)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.const_mul 64)

theorem squash_mem_piecewiseAffineGroupoid :
    squash.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid (ℝ × ℝ) := by
  let a := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let b := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  apply (mem_piecewiseAffineGroupoid_iff_forward squash.toOpenPartialHomeomorph).mpr
  apply (locallyPiecewiseAffineOn_affine (a.prod ((1 / 64 : ℝ) • b)) isOpen_univ).congr
  intro z _
  exact Prod.ext rfl (by change 1 / 64 * z.2 = z.2 / 64; ring)

noncomputable def width (x : ℝ) : ℝ := max 0 (|x| - 1)

theorem continuous_width : Continuous width := by
  unfold width
  fun_prop

theorem locallyPiecewiseAffineOn_width : LocallyPiecewiseAffineOn width univ := by
  intro x _
  obtain ⟨K, hK, hxK, _⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed
      isCompact_singleton isOpen_univ (singleton_subset_iff.mpr (mem_univ x))
  have hi := (K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)).finitePiecewiseAffineOn hK
  have hn := (K.affineOnFaces_affine (-ContinuousAffineMap.id ℝ ℝ)).finitePiecewiseAffineOn hK
  have habs : FinitePiecewiseAffineOn (abs : ℝ → ℝ) K.space :=
    (hi.max hn).congr (fun _ _ => abs_eq_max_neg.symm)
  have hone := (K.affineOnFaces_affine
    (ContinuousAffineMap.const ℝ ℝ (1 : ℝ))).finitePiecewiseAffineOn hK
  obtain ⟨J, hJ, hJK, hw⟩ := (habs.sub hone).positivePart
  refine ⟨J, hJ, ?_, fun _ _ => mem_univ _, hw⟩
  rw [hJK]
  exact hxK (mem_singleton x)

noncomputable def expand : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  PLFiberCompression.homeomorph 64 (by norm_num) width
    (fun _ => le_max_left _ _) continuous_width

theorem expand_mem_piecewiseAffineGroupoid :
    expand.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid (ℝ × ℝ) :=
  PLFiberCompression.homeomorph_mem_piecewiseAffineGroupoid
    64 (by norm_num) width (fun _ => le_max_left _ _)
      continuous_width locallyPiecewiseAffineOn_width

theorem expand_squash_core {s : ℝ} (hs : |s| ≤ 1) (t : ℝ) :
    expand (squash (s, t)) = (s, t) := by
  apply Prod.ext
  · rfl
  · change PLFiberCompression.value 64 (width s) (t / 64) = t
    rw [width, max_eq_left (sub_nonpos.mpr hs), PLFiberCompression.value_zero_width]
    ring

theorem expand_squash_outer {s t : ℝ} (hs : 5 < |s|) (ht : |t| < 1) :
    expand (squash (s, t)) = squash (s, t) := by
  have hw : 4 < width s := by
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  apply Prod.ext
  · rfl
  · change PLFiberCompression.value 64 (width s) (t / 64) = t / 64
    apply PLFiberCompression.value_of_mem
    have ht' := abs_lt.mp ht
    constructor <;> linarith [ht'.1, ht'.2]

theorem expand_squash_snd_mem (s : ℝ) {t : ℝ} (ht : |t| < 1) :
    (expand (squash (s, t))).2 ∈ Ioo (-1) 1 := by
  have h := PLFiberCompression.abs_value_le
    (delta := (64 : ℝ)) (w := width s) (t := t / 64) (by norm_num) (le_max_left _ _)
  have hbound : 64 * |t / 64| = |t| := by rw [abs_div]; norm_num; ring
  change PLFiberCompression.value 64 (width s) (t / 64) ∈ Ioo (-1) 1
  exact abs_lt.mp (lt_of_le_of_lt (h.trans_eq hbound) ht)

end StableAnnulus
