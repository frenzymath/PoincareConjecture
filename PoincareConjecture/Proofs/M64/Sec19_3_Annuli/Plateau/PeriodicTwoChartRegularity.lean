import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusTwoCutC1
import Mathlib.Algebra.Order.ToIntervalMod










noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "half" => curvePeriod / 2
local notation "v" => annulusPoint (curvePeriod / 2) 0

private theorem point_coordinates (p : LoopPlane) : annulusPoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> rfl




theorem m64PeriodicMap_contMDiffOn_of_two_charts
    {F G : LoopPlane → M} {Y : Set ℝ} {k : ℕ∞ω}
    (hF : ContMDiffOn (𝓡 2) (𝓡 n) k F
      {p : LoopPlane | p 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ p 1 ∈ Y})
    (hG : ContMDiffOn (𝓡 2) (𝓡 n) k G
      {p : LoopPlane | p 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ p 1 ∈ Y})
    (hperiod : ∀ x y, F (annulusPoint (x + curvePeriod) y) = F (annulusPoint x y))
    (hleft : EqOn F (fun p => G (p + v))
      {p : LoopPlane | p 0 ∈ Ioo (0 : ℝ) half ∧ p 1 ∈ Y})
    (hright : EqOn F (fun p => G (p - v))
      {p : LoopPlane | p 0 ∈ Ioo half curvePeriod ∧ p 1 ∈ Y})
    (hzero : ∀ y ∈ Y, F (annulusPoint 0 y) = G (annulusPoint half y)) :
    ContMDiffOn (𝓡 2) (𝓡 n) k F {p : LoopPlane | p 1 ∈ Y} := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  let S : Set LoopPlane := {p | p 1 ∈ Y}
  let D : Set LoopPlane := {p | p 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ p 1 ∈ Y}
  have hzeroReg (p : LoopPlane) (hp : p ∈ S) (hp0 : p 0 = 0) :
      ContMDiffWithinAt (𝓡 2) (𝓡 n) k F S p := by
    let O : Set LoopPlane := {q | q 0 ∈ Ioo (-half) half}
    have hO : O ∈ 𝓝 p := (isOpen_Ioo.preimage (by fun_prop)).mem_nhds
      (by change -half < p 0 ∧ p 0 < half; rw [hp0]; constructor <;> linarith)
    have hm : MapsTo (fun q : LoopPlane => q + v) (S ∩ O) D := by
      intro q hq
      change (q + v) 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ (q + v) 1 ∈ Y
      simp only [PiLp.add_apply, annulusPoint, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero]
      have hqx : -half < q 0 ∧ q 0 < half := hq.2
      exact ⟨⟨by linarith [hqx.1], by linarith [hqx.2]⟩, hq.1⟩
    have hs : ContMDiff (𝓡 2) (𝓡 2) k (fun q : LoopPlane => q + v) :=
      (contDiff_id.add contDiff_const).contMDiff
    have hc := (hG (p + v) (hm ⟨hp, mem_of_mem_nhds hO⟩)).comp p
      (hs p).contMDiffWithinAt hm
    have hc' := hc.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds hO))
    apply hc'.congr_of_eventuallyEq_of_mem _ hp
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hO] with q hq hqO
    change F q = G (q + v)
    rcases lt_trichotomy (q 0) 0 with hneg | heq | hpos
    · let z := q + annulusPoint curvePeriod 0
      have hzx : z 0 ∈ Ioo half curvePeriod := by
        change half < q 0 + curvePeriod ∧ q 0 + curvePeriod < curvePeriod
        have hqx : -half < q 0 := hqO.1
        constructor <;> linarith
      have hzy : z 1 ∈ Y := by simpa [S, z, annulusPoint] using hq
      have hzF : F z = F q := by
        have he : z = annulusPoint (q 0 + curvePeriod) (q 1) := by
          ext i
          fin_cases i <;> simp [z, annulusPoint]
        rw [he, hperiod, point_coordinates]
      have hzG : z - v = q + v := by
        ext i
        fin_cases i <;> simp [z, annulusPoint]
        ring
      exact hzF.symm.trans ((hright ⟨hzx, hzy⟩).trans (congrArg G hzG))
    · have hqpoint : q = annulusPoint 0 (q 1) := by
        ext i
        fin_cases i <;> simp [annulusPoint, heq]
      have hshift : q + v = annulusPoint half (q 1) := by
        rw [hqpoint]
        ext i
        fin_cases i <;> simp [annulusPoint]
      exact (congrArg F hqpoint).trans ((hzero _ hq).trans (congrArg G hshift.symm))
    · exact hleft ⟨⟨hpos, hqO.2⟩, hq⟩
  have hfund (p : LoopPlane) (hp : p ∈ S) (hx : p 0 ∈ Ico (0 : ℝ) curvePeriod) :
      ContMDiffWithinAt (𝓡 2) (𝓡 n) k F S p := by
    by_cases hz : p 0 = 0
    · exact hzeroReg p hp hz
    have hxp : p 0 ∈ Ioo (0 : ℝ) curvePeriod :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hz), hx.2⟩
    have hO : {q : LoopPlane | q 0 ∈ Ioo (0 : ℝ) curvePeriod} ∈ 𝓝 p :=
      (isOpen_Ioo.preimage (by fun_prop)).mem_nhds hxp
    exact (hF p ⟨hxp, hp⟩).mono_of_mem_nhdsWithin (by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hO] with q hq hqx
      exact ⟨hqx, hq⟩)
  intro p hp
  let j := -toIcoDiv hP 0 (p 0)
  let T := annulusPoint (j • curvePeriod) 0
  let q := annulusPoint (toIcoMod hP 0 (p 0)) (p 1)
  have hpoint : T + p = q := by
    ext i
    fin_cases i <;> simp [T, q, j, annulusPoint, toIcoMod, neg_smul,
      sub_eq_add_neg, add_comm]
  have hqS : q ∈ S := by simpa [q, S, annulusPoint] using hp
  have hqx : q 0 ∈ Ico (0 : ℝ) curvePeriod := toIcoMod_mem_Ico' hP (p 0)
  have hm : MapsTo (fun z : LoopPlane => T + z) S S := by
    intro z hz
    simpa [S, T, annulusPoint] using hz
  have htranslation : (fun z : LoopPlane => F (T + z)) = F := by
    funext z
    have hper : Function.Periodic (fun x => F (annulusPoint x (z 1))) curvePeriod :=
      fun x => hperiod x (z 1)
    have he : T + z = annulusPoint (z 0 + j • curvePeriod) (z 1) := by
      ext i
      fin_cases i <;> simp [T, annulusPoint, add_comm]
    rw [he]
    exact (hper.zsmul j (z 0)).trans (congrArg F (point_coordinates z))
  have hs : ContMDiff (𝓡 2) (𝓡 2) k (fun z : LoopPlane => T + z) :=
    (contDiff_const.add contDiff_id).contMDiff
  have hc := (hpoint.symm ▸ hfund q hqS hqx).comp p (hs p).contMDiffWithinAt hm
  change ContMDiffWithinAt (𝓡 2) (𝓡 n) k (fun z => F (T + z)) S p at hc
  rw [htranslation] at hc
  exact hc

end PoincareConjecture
