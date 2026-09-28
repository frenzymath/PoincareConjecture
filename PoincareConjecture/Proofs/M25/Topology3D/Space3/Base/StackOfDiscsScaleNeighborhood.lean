import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsScaleChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D

variable {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}


theorem exists_stackCapCoreNeighborhood (C : SurgeryCapTag psi u)
    (hpsi : IsCollarEmbedding psi) (K L : Set E3) (_hK : IsCompact K) (_hL : IsCompact L)
    (gap lambda : ℝ) (hgap : 0 < gap) (hlambda : 0 < lambda)
    (hcover : range (fun q => psi (q, 0)) = K ∪ C.cap ∪ L)
    (hseam : C.seam ⊆ K)
    (hKside : ∀ y ∈ K, 0 ≤ C.sign * (inner ℝ (u : E3) y -
      (C.cutHeight + C.sign * C.removal)))
    (hLside : ∀ y ∈ L, gap ≤ C.sign * (inner ℝ (u : E3) y -
      (C.cutHeight + C.sign * C.removal))) :
    let s := C.cutHeight + C.sign * C.removal
    let cyl := fun p : E2 × ℝ => C.tube (p.1, s + C.sign * p.2)
    ∃ d : ℝ, ∃ N : Set E3,
      0 < d ∧ d < lambda / 4 ∧ d < C.scale * C.overlapWidth ∧ d < gap / 4 ∧
      IsOpen N ∧ C.seam ⊆ N ∧
      N ∩ K = cyl '' (sphere (0 : E2) 1 ×ˢ Ico 0 d) ∧
      cyl '' (sphere (0 : E2) 1 ×ˢ Icc 0 d) ⊆ K ∧
      ∀ theta : UnitCircle, C.tube (theta.1, s + C.sign * d) ∉ N := by
  classical
  let s := C.cutHeight + C.sign * C.removal
  let cyl := fun p : E2 × ℝ => C.tube (p.1, s + C.sign * p.2)
  let j := fun q : UnitTwoSphere => psi (q, 0)
  let H := fun q : UnitTwoSphere => (heightCoordinates (q : E3)).2
  have hj : Continuous j := (collar_central_contMDiff psi hpsi).continuous
  have hji : Function.Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1
      (show (p, (0 : ℝ)) ∈ univ ×ˢ Ioo (-1) 1 by simp)
      (show (q, (0 : ℝ)) ∈ univ ×ˢ Ioo (-1) 1 by simp) hpq)
  have hH : Continuous H := (heightCoordinates.continuous.comp continuous_subtype_val).snd
  have hmpos : 0 < min (lambda / 4) (min (C.scale * C.overlapWidth) (gap / 4)) :=
    lt_min (div_pos hlambda (by norm_num))
      (lt_min (mul_pos C.scale_pos C.overlap_pos) (div_pos hgap (by norm_num)))
  obtain ⟨d, hd, hdm⟩ := exists_between hmpos
  have hdl : d < lambda / 4 := hdm.trans_le (min_le_left _ _)
  have hdo : d < C.scale * C.overlapWidth :=
    hdm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdg : d < gap / 4 := hdm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hdgap : d < gap := by linarith
  have heps : 0 < d / C.scale := div_pos hd C.scale_pos
  have hepslt : d / C.scale < C.overlapWidth :=
    (div_lt_iff₀ C.scale_pos).mpr (by simpa only [mul_comm] using hdo)
  have hepsquarter : d / C.scale < 1 / 4 := hepslt.trans_le C.overlap_le
  let B : Set UnitTwoSphere := {q | |H q| < d / C.scale}
  have hB : IsOpen B := isOpen_lt hH.abs continuous_const
  have hBs : B ⊆ C.sourceChart.source := by
    intro q hq
    exact C.source_band q ((le_abs_self (H q)).trans_lt (hq.trans hepslt))
  let A := C.sourceChart '' B
  have hA : IsOpen A := C.sourceChart.isOpen_image_of_subset_source hB hBs
  let N := (j '' Aᶜ)ᶜ
  have hN : IsOpen N := (hA.isClosed_compl.isCompact.image hj).isClosed.isOpen_compl
  have hNimage : N ∩ range j = j '' A := by
    ext y
    constructor
    · rintro ⟨hy, q, rfl⟩
      refine ⟨q, ?_, rfl⟩
      by_contra hq
      exact hy ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨?_, mem_range_self q⟩
      rintro ⟨p, hp, hpq⟩
      exact hp (hji hpq ▸ hq)
  have hsign : C.sign * C.sign = 1 := by nlinarith [C.sign_abs, sq_abs C.sign]
  have hheight (theta : UnitCircle) (w : ℝ) :
      C.sign * (inner ℝ (u : E3) (cyl (theta.1, w)) - s) = w := by
    have hs : (theta.1, s + C.sign * w) ∈ C.tube.source :=
      C.tube_source ⟨sphere_subset_closedBall theta.2, mem_univ _⟩
    change C.sign * (inner ℝ (u : E3) (C.tube _) - s) = w
    rw [C.tube_height _ hs]
    calc
      _ = (C.sign * C.sign) * w := by ring
      _ = w := by rw [hsign, one_mul]
  have hformula (q : UnitTwoSphere) (hq : |H q| ≤ d / C.scale) :
      j (C.sourceChart q) =
        cyl ((circleDirection (heightCoordinates (q : E3)).1 : E2), C.scale * H q) := by
    have hqband : H q < C.overlapWidth :=
      (le_abs_self _).trans_lt (hq.trans_lt hepslt)
    have hmodel : C.profile.model q =
        ((circleDirection (heightCoordinates (q : E3)).1 : E2), H q) :=
      surgeryCapModel_cylinder _ _ _ _ _ _ C.profile.horizontal_near C.profile.vertical_far
        q (hq.trans hepsquarter.le)
    change psi (C.sourceChart q, 0) = _
    rw [C.central_eq q hqband, SurgeryCapProfile.capMap_apply, hmodel]
    congr 1
    apply Prod.ext
    · rfl
    · dsimp only [s]
      ring
  have hparam (theta : UnitCircle) (w : ℝ) (hw : |w| ≤ d) :
      ∃ q : UnitTwoSphere, H q = w / C.scale ∧ |H q| ≤ d / C.scale ∧
        j (C.sourceChart q) = cyl (theta.1, w) := by
    let v := w / C.scale
    have hv : |v| ≤ d / C.scale := by
      dsimp only [v]
      rw [abs_div, abs_of_pos C.scale_pos]
      exact div_le_div_of_nonneg_right hw C.scale_pos.le
    have hv1 : |v| < 1 := by linarith
    have hrad : 0 < 1 - v ^ 2 := by
      obtain ⟨hneg, hpos⟩ := abs_lt.mp hv1
      nlinarith
    have hroot : 0 < Real.sqrt (1 - v ^ 2) := Real.sqrt_pos.2 hrad
    let Y := heightCoordinates.symm (Real.sqrt (1 - v ^ 2) • theta.1, v)
    have hY : ‖Y‖ = 1 := by
      have hsq : ‖Y‖ ^ 2 = 1 := by
        dsimp only [Y]
        rw [heightCoordinates_symm_norm_sq, norm_smul, Real.norm_eq_abs,
          abs_of_pos hroot, norm_eq_of_mem_sphere theta, mul_one, Real.sq_sqrt hrad.le]
        ring
      nlinarith [norm_nonneg Y]
    let q : UnitTwoSphere := ⟨Y, mem_sphere_zero_iff_norm.mpr hY⟩
    have hcoords : heightCoordinates (q : E3) = (Real.sqrt (1 - v ^ 2) • theta.1, v) :=
      heightCoordinates.apply_symm_apply _
    have hq : H q = v := congrArg Prod.snd hcoords
    refine ⟨q, hq, hq ▸ hv, ?_⟩
    rw [hformula q (hq ▸ hv), hcoords, circleDirection_smul theta hroot, hq]
    have hcancel : C.scale * v = w := by dsimp only [v]; field_simp [C.scale_pos.ne']
    rw [hcancel]
  have hseamN : C.seam ⊆ N := by
    rintro y ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    have hqB : q ∈ B := by
      change |H q| < d / C.scale
      change H q = 0 at hq
      rw [hq, abs_zero]
      exact heps
    have hm : j (C.sourceChart q) ∈ N ∩ range j := by
      rw [hNimage]
      exact ⟨C.sourceChart q, ⟨q, hqB, rfl⟩, rfl⟩
    exact hm.1
  have hcapSide : ∀ y ∈ C.cap, C.sign * (inner ℝ (u : E3) y - s) ≤ 0 := by
    intro y hy
    rw [C.cap_eq_image] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    have hs : ((C.profile.model q).1,
        C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2))
          ∈ C.tube.source :=
      C.tube_source ⟨mem_closedBall_zero_iff.mpr (C.profile.model_fst_norm_le q), mem_univ _⟩
    rw [SurgeryCapProfile.capMap_apply, C.tube_height _ hs]
    have hz : (C.profile.model q).2 ≤ 0 :=
      (surgeryCapModel_snd_nonpos_iff _ _ _ _ _ _ C.profile.vertical_pos q).mpr hq
    calc
      _ = (C.sign * C.sign) * (C.scale * (C.profile.model q).2) := by dsimp [s]; ring
      _ = C.scale * (C.profile.model q).2 := by rw [hsign, one_mul]
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos C.scale_pos.le hz
  have hclosed : cyl '' (sphere (0 : E2) 1 ×ˢ Icc 0 d) ⊆ K := by
    rintro y ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩
    let theta : UnitCircle := ⟨x, hx⟩
    obtain ⟨q, hq, _, heq⟩ := hparam theta w (by rw [abs_of_nonneg hw.1]; exact hw.2)
    by_cases hw0 : w = 0
    · apply hseam
      rw [← heq]
      refine ⟨C.sourceChart q, ⟨q, ?_, rfl⟩, rfl⟩
      change H q = 0
      rw [hq, hw0, zero_div]
    · have hwr : 0 < w := lt_of_le_of_ne hw.1 (Ne.symm hw0)
      have hy : cyl (theta.1, w) ∈ range j := ⟨C.sourceChart q, heq⟩
      rw [hcover] at hy
      rcases hy with (hy | hy) | hy
      · exact hy
      · have hh := hcapSide _ hy
        rw [hheight] at hh
        linarith
      · have hh := hLside _ hy
        change gap ≤ C.sign * (inner ℝ (u : E3) (cyl (theta.1, w)) - s) at hh
        rw [hheight] at hh
        linarith [hw.2]
  have hstrip : N ∩ K = cyl '' (sphere (0 : E2) 1 ×ˢ Ico 0 d) := by
    ext y
    constructor
    · rintro ⟨hyN, hyK⟩
      have hyr : y ∈ range j := by rw [hcover]; exact Or.inl (Or.inl hyK)
      have hya : y ∈ j '' A := by rw [← hNimage]; exact ⟨hyN, hyr⟩
      obtain ⟨p, ⟨q, hq, rfl⟩, rfl⟩ := hya
      have hq' : |H q| < d / C.scale := hq
      have heq := hformula q hq'.le
      have hh := hKside _ hyK
      rw [heq] at hh
      change 0 ≤ C.sign * (inner ℝ (u : E3)
        (cyl ((circleDirection (heightCoordinates (q : E3)).1 : E2), C.scale * H q)) - s) at hh
      rw [hheight] at hh
      refine ⟨((circleDirection (heightCoordinates (q : E3)).1 : E2), C.scale * H q),
        ⟨(circleDirection _).2, hh, ?_⟩, heq.symm⟩
      have hm := (lt_div_iff₀ C.scale_pos).mp hq'
      have ha := mul_le_mul_of_nonneg_left (le_abs_self (H q)) C.scale_pos.le
      nlinarith
    · rintro ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩
      let theta : UnitCircle := ⟨x, hx⟩
      obtain ⟨q, hq, _, heq⟩ := hparam theta w (by rw [abs_of_nonneg hw.1]; exact hw.2.le)
      refine ⟨?_, hclosed ⟨(x, w), ⟨hx, hw.1, hw.2.le⟩, rfl⟩⟩
      have hqB : q ∈ B := by
        change |H q| < d / C.scale
        rw [hq, abs_div, abs_of_pos C.scale_pos, abs_of_nonneg hw.1]
        exact (div_lt_div_iff_of_pos_right C.scale_pos).mpr hw.2
      have hm : j (C.sourceChart q) ∈ N ∩ range j := by
        rw [hNimage]
        exact ⟨C.sourceChart q, ⟨q, hqB, rfl⟩, rfl⟩
      rw [← heq]
      exact hm.1
  refine ⟨d, N, hd, hdl, hdo, hdg, hN, hseamN, hstrip, hclosed, ?_⟩
  intro theta hthetaN
  have hm : cyl (theta.1, d) ∈ N ∩ K :=
    ⟨hthetaN, hclosed ⟨(theta.1, d), ⟨theta.2, hd.le, le_rfl⟩, rfl⟩⟩
  rw [hstrip] at hm
  obtain ⟨⟨x, w⟩, ⟨hx, hw⟩, heq⟩ := hm
  have hh := congrArg (fun y => C.sign * (inner ℝ (u : E3) y - s)) heq
  rw [hheight ⟨x, hx⟩ w, hheight theta d] at hh
  exact (ne_of_lt hw.2) hh


theorem exists_stackCapScaleCutoff (C : SurgeryCapTag psi u)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsmall : lambda < C.scale)
    (K L N : Set E3) (hK : IsCompact K) (hL : IsCompact L)
    (hN : IsOpen N) (hseamN : C.seam ⊆ N)
    (gap : ℝ) (hgap : 0 < gap)
    (hKside : ∀ y ∈ K, 0 ≤ C.sign * (inner ℝ (u : E3) y -
      (C.cutHeight + C.sign * C.removal)))
    (hLside : ∀ y ∈ L, gap ≤ C.sign * (inner ℝ (u : E3) y -
      (C.cutHeight + C.sign * C.removal))) :
    let s := C.cutHeight + C.sign * C.removal
    let chi := fun y : E3 => C.sign * (inner ℝ (u : E3) y - s)
    let U := Ioo (-2 : ℝ) 3 ×ˢ
      ((C.tube.target ∩ {y | chi y < gap / 2}) \ ((K \ N) ∪ L))
    let Ktrack := (fun p : ℝ × UnitTwoSphere =>
      (p.1, stackCapScaleCap C lambda p.1 p.2)) ''
        (Icc (-1 : ℝ) 2 ×ˢ {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0})
    IsOpen U ∧ Ktrack ⊆ U ∧
    ∃ rho : ℝ × E3 → ℝ, ContDiff ℝ ∞ rho ∧ HasCompactSupport rho ∧
      tsupport rho ⊆ U ∧ (∀ᶠ p in 𝓝ˢ Ktrack, rho p = 1) ∧
      (∀ p, rho p ∈ Icc 0 1) ∧
      ContDiff ℝ ∞ (fun p => rho p •
        chartTimeField (stackCapScaleChart C lambda hlambda) p) ∧
      HasCompactSupport (fun p => rho p •
        chartTimeField (stackCapScaleChart C lambda hlambda) p) := by
  let s := C.cutHeight + C.sign * C.removal
  let chi := fun y : E3 => C.sign * (inner ℝ (u : E3) y - s)
  let U := Ioo (-2 : ℝ) 3 ×ˢ
    ((C.tube.target ∩ {y | chi y < gap / 2}) \ ((K \ N) ∪ L))
  let cap := stackCapScaleCap C lambda
  let Ktrack := (fun p : ℝ × UnitTwoSphere => (p.1, cap p.1 p.2)) ''
    (Icc (-1 : ℝ) 2 ×ˢ {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0})
  let e := stackCapScaleChart C lambda hlambda
  obtain ⟨_, hs, _, hcompact, _, hstart, _, _, _, hsouth, hzero, hseam⟩ :=
    stackCapScaleCap_spec C lambda hlambda hsmall
  have hchi : Continuous chi :=
    continuous_const.mul ((innerSL ℝ (u : E3)).continuous.sub continuous_const)
  have hU : IsOpen U := isOpen_Ioo.prod
    ((C.tube.open_target.inter (isOpen_lt hchi continuous_const)).sdiff
      ((hK.isClosed.sdiff hN).union hL.isClosed))
  have hKU : Ktrack ⊆ U := by
    rintro p ⟨⟨t, q⟩, ⟨ht, hq⟩, rfl⟩
    have hnonpos := hsouth t q hq
    change chi (cap t q) ≤ 0 at hnonpos
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩,
      ⟨C.tube.map_source (hs t q), ?_⟩, ?_⟩
    · change chi (cap t q) < gap / 2
      linarith
    · rintro (hy | hy)
      · have hnonneg := hKside _ hy.1
        have heq : chi (cap t q) = 0 := le_antisymm hnonpos hnonneg
        have hqzero := (hzero t q hq).mp heq
        have hm : cap t q ∈ C.seam := by
          change stackCapScaleCap C lambda t q ∈ C.seam
          rw [hseam t q hqzero, hstart q, C.seam_eq_image]
          exact ⟨q, hqzero, rfl⟩
        exact hy.2 (hseamN hm)
      · have hh := hLside _ hy
        change gap ≤ chi (cap t q) at hh
        linarith
  obtain ⟨rho, hrho, hrhoc, hrhoU, hnear, hrange⟩ :=
    exists_compact_smooth_cutoff hcompact hU hKU
  obtain ⟨_, _, _, htarget, he, hei, _⟩ := stackCapScaleChart_spec C lambda hlambda
  have hsupp : tsupport rho ⊆ e.target := by
    intro p hp
    rw [htarget]
    exact ⟨mem_univ _, (hrhoU hp).2.1.1⟩
  exact ⟨hU, hKU, rho, hrho, hrhoc, hrhoU, hnear, hrange,
    contDiff_cutoff_smul e.open_target rho hrho hsupp
      (chartTimeField e) (chartTimeField_contDiffOn e he hei), hrhoc.smul_right⟩

end PoincareConjecture.M25.Topology3D
