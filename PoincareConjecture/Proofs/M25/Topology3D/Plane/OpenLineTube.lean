import PoincareConjecture.Proofs.M25.Topology3D.Plane.Tube
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TubeInjectivity
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

open Set Function Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_fixedTail_openLine_normalTube
    (C : ((ℝ × ℝ) × ℝ) → (ℝ × ℝ))
    {a b c d R : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hR : 0 < R)
    (hC : ContDiff ℝ ∞ C)
    (hinj : ∀ z ∈ Icc a b ×ˢ Icc c d,
      Injective (fun u : ℝ => C (z, u)))
    (hreg : ∀ z ∈ Icc a b ×ˢ Icc c d, ∀ u : ℝ,
      fderiv ℝ (fun v : ℝ => C (z, v)) u 1 ≠ 0)
    (htail : ∀ z u, R ≤ |u| → C (z, u) = (u, 0)) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧
      ∃ w : ℝ, 0 < w ∧ w ≤ 1 ∧
        ∃ T : OpenPartialHomeomorph
          (((ℝ × ℝ) × (ℝ × ℝ))) (((ℝ × ℝ) × (ℝ × ℝ))),
          T.source =
              (Ioo (a - m) (b + m) ×ˢ Ioo (c - m) (d + m)) ×ˢ
                {q : ℝ × ℝ | |q.2| < w} ∧
          (∀ p, T p =
            (p.1, C (p.1, p.2.1) + p.2.2 •
              (-((fderiv ℝ (fun v : ℝ => C (p.1, v)) p.2.1) 1).2,
                 ((fderiv ℝ (fun v : ℝ => C (p.1, v)) p.2.1) 1).1))) ∧
          ContDiffOn ℝ ∞ T T.source ∧
          ContDiffOn ℝ ∞ T.symm T.target ∧
          (∀ z ∈ Ioo (a - m) (b + m) ×ˢ Ioo (c - m) (d + m),
            ∀ u y, |y| < w → R + 1 ≤ |u| →
              T (z, (u, y)) = (z, (u, y))) := by
  let V : ((ℝ × ℝ) × ℝ) → (ℝ × ℝ) :=
    fun p => fderiv ℝ (fun v : ℝ => C (p.1, v)) p.2 1
  let N : ((ℝ × ℝ) × ℝ) → (ℝ × ℝ) :=
    fun p => (- (V p).2, (V p).1)
  let Xi : ((ℝ × ℝ) × (ℝ × ℝ)) → ((ℝ × ℝ) × (ℝ × ℝ)) :=
    fun p => (p.1, C (p.1, p.2.1) + p.2.2 • N (p.1, p.2.1))
  have hV : ContDiff ℝ ∞ V := by
    have hunc : ContDiff ℝ ∞
        (Function.uncurry (fun p : (ℝ × ℝ) × ℝ => fun u => C (p.1, u))) :=
      hC.comp (contDiff_fst.fst.prodMk contDiff_snd)
    exact hunc.fderiv_apply (n := ∞) contDiff_snd contDiff_const (by simp)
  have hN : ContDiff ℝ ∞ N := by
    simpa only [N] using hV.snd.neg.prodMk hV.fst
  have hXi : ContDiff ℝ ∞ Xi := by
    have harg : ContDiff ℝ ∞
        (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) => (p.1, p.2.1)) :=
      contDiff_fst.prodMk contDiff_snd.fst
    have hcpart : ContDiff ℝ ∞
        (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) => C (p.1, p.2.1)) := hC.comp harg
    have hnpart : ContDiff ℝ ∞
        (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) => N (p.1, p.2.1)) := hN.comp harg
    have hheight : ContDiff ℝ ∞
        (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) => p.2.2) := contDiff_snd.snd
    have hsp : ContDiff ℝ ∞
        (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) => p.2.2 • N (p.1, p.2.1)) :=
      hheight.smul hnpart
    have hsecond : ContDiff ℝ ∞
        (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) =>
          C (p.1, p.2.1) + p.2.2 • N (p.1, p.2.1)) := hcpart.add hsp
    simpa only [Xi] using contDiff_fst.prodMk hsecond
  have htailV (z : ℝ × ℝ) (u : ℝ) (hu : R < |u|) : V (z, u) = (1, 0) := by
    have heq : (fun v : ℝ => C (z, v)) =ᶠ[𝓝 u] (fun v : ℝ => (v, 0)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hu] with v hv
      exact htail z v hv.le
    have hder := (hasFDerivAt_prodMk_left (𝕜 := ℝ) u (0 : ℝ)).congr_of_eventuallyEq heq
    change (fderiv ℝ (fun v : ℝ => C (z, v)) u) 1 = (1, 0)
    rw [hder.fderiv]
    rfl
  have htailXi (z : ℝ × ℝ) (u y : ℝ) (hu : R < |u|) :
      Xi (z, (u, y)) = (z, (u, y)) := by
    dsimp only [Xi]
    rw [htail z u hu.le]
    simp [N, htailV z u hu]
  have hcentral (z : ℝ × ℝ) (hz : z ∈ Icc a b ×ˢ Icc c d) (u : ℝ) :
      Injective (fderiv ℝ Xi (z, (u, 0))) := by
    let D : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (V (z, u)) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (N (z, u))
    have hCz : ContDiff ℝ ∞ (fun v : ℝ => C (z, v)) :=
      hC.comp (contDiff_const.prodMk contDiff_id)
    have hNz : ContDiff ℝ ∞ (fun q : ℝ × ℝ => N (z, q.1)) :=
      hN.comp (contDiff_const.prodMk contDiff_fst)
    have hsp : HasFDerivAt
        (fun q : ℝ × ℝ => C (z, q.1) + q.2 • N (z, q.1)) D (u, 0) := by
      have hc0 := (hCz.differentiable (by simp) u).hasFDerivAt.comp
        (u, (0 : ℝ)) (hasFDerivAt_fst (𝕜 := ℝ))
      have hdc : (fderiv ℝ (fun v : ℝ => C (z, v)) u).comp
          (ContinuousLinearMap.fst ℝ ℝ ℝ) =
            (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (V (z, u)) := by
        apply ContinuousLinearMap.ext
        intro q
        simp [V]
      rw [hdc] at hc0
      have hn0 := hasFDerivAt_snd.smul
        (hNz.differentiable (by simp) (u, (0 : ℝ))).hasFDerivAt
      convert! hc0.add hn0 using 1
      simp [D]
    have hDi : Injective D := by
      apply (injective_iff_map_eq_zero D).mpr
      intro q hq
      have hx : q.1 * (V (z, u)).1 - q.2 * (V (z, u)).2 = 0 := by
        simpa [D, N, sub_eq_add_neg] using congrArg Prod.fst hq
      have hy : q.1 * (V (z, u)).2 + q.2 * (V (z, u)).1 = 0 := by
        simpa [D, N] using congrArg Prod.snd hq
      have hv : (V (z, u)).1 ^ 2 + (V (z, u)).2 ^ 2 ≠ 0 := by
        intro heq
        have h1 : (V (z, u)).1 = 0 := by nlinarith [sq_nonneg (V (z, u)).2]
        have h2 : (V (z, u)).2 = 0 := by nlinarith [sq_nonneg (V (z, u)).1]
        exact hreg z hz u (Prod.ext h1 h2)
      have hq1 : q.1 = 0 := (mul_eq_zero.mp (show
          q.1 * ((V (z, u)).1 ^ 2 + (V (z, u)).2 ^ 2) = 0 by
        linear_combination (V (z, u)).1 * hx + (V (z, u)).2 * hy)).resolve_right hv
      have hq2 : q.2 = 0 := (mul_eq_zero.mp (show
          q.2 * ((V (z, u)).1 ^ 2 + (V (z, u)).2 ^ 2) = 0 by
        linear_combination -(V (z, u)).2 * hx + (V (z, u)).1 * hy)).resolve_right hv
      exact Prod.ext hq1 hq2
    let L := fderiv ℝ Xi (z, (u, 0))
    have hL : HasFDerivAt Xi L (z, (u, 0)) :=
      (hXi.differentiable (by simp) (z, (u, 0))).hasFDerivAt
    have hfirst : (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)).comp L =
        ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ) :=
      hL.fst.unique hasFDerivAt_fst
    have hright : L.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) (ℝ × ℝ)) =
        (0 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).prod D :=
      (hL.comp (u, (0 : ℝ)) (hasFDerivAt_prodMk_right z (u, (0 : ℝ)))).unique
        ((hasFDerivAt_const z (u, (0 : ℝ))).prodMk hsp)
    apply (injective_iff_map_eq_zero L).mpr
    intro q hq
    have hz0 : q.1 = 0 := by
      have he := congrArg (fun F : ((ℝ × ℝ) × (ℝ × ℝ)) →L[ℝ] (ℝ × ℝ) => F q) hfirst
      simpa [hq] using he.symm
    have hq0 : q = (0, q.2) := Prod.ext hz0 rfl
    have hD0 : D q.2 = 0 := by
      have he := congrArg (fun F : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) × (ℝ × ℝ)) => F q.2) hright
      have he2 := congrArg Prod.snd he
      simpa [← hq0, hq] using he2.symm
    exact Prod.ext hz0 (hDi (hD0.trans D.map_zero.symm))
  have hlocal (p : (ℝ × ℝ) × (ℝ × ℝ)) (hi : Injective (fderiv ℝ Xi p)) :
      ∃ l : OpenPartialHomeomorph ((ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ) × (ℝ × ℝ)),
        p ∈ l.source ∧ (∀ q, l q = Xi q) ∧ ContDiffAt ℝ ∞ l.symm (Xi p) := by
    let D := fderiv ℝ Xi p
    let e : ((ℝ × ℝ) × (ℝ × ℝ)) ≃L[ℝ] ((ℝ × ℝ) × (ℝ × ℝ)) :=
      (LinearEquiv.ofBijective D.toLinearMap
        ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
    have hd : HasFDerivAt Xi (e : _ →L[ℝ] _) p :=
      (hXi.differentiable (by simp) p).hasFDerivAt
    let l := hXi.contDiffAt.toOpenPartialHomeomorph Xi hd (by simp)
    exact ⟨l, hXi.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp),
      fun _ => rfl, hXi.contDiffAt.to_localInverse hd (by simp)⟩
  let P1 := Icc (a - 1) (b + 1) ×ˢ Icc (c - 1) (d + 1)
  let L1 := Icc (-(R + 1)) (R + 1)
  have hboundcont : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      |(C p).1| + |(N p).1|) := hC.continuous.fst.abs.add hN.continuous.fst.abs
  have hboxcompact : IsCompact (P1 ×ˢ L1) :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  obtain ⟨B, hB⟩ := hboxcompact.bddAbove_image hboundcont.continuousOn
  let M := max (R + 1) (B + 1) + 1
  have hRM : R + 1 < M := by
    dsimp [M]
    linarith [le_max_left (R + 1) (B + 1)]
  have hBM : B < M := by
    dsimp [M]
    linarith [le_max_right (R + 1) (B + 1)]
  have hM : 0 < M := by linarith
  let K : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
    (Icc a b ×ˢ Icc c d) ×ˢ (Icc (-M) M ×ˢ {0})
  have hKcompact : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_singleton)
  have hKinj : InjOn Xi K := by
    rintro ⟨z, u, y⟩ ⟨hz, hu, hy⟩ ⟨z', u', y'⟩ ⟨hz', hu', hy'⟩ he
    have hy0 : y = 0 := hy
    have hy0' : y' = 0 := hy'
    subst y
    subst y'
    have hzz : z = z' := congrArg Prod.fst he
    subst z'
    have hcc : C (z, u) = C (z, u') := by simpa [Xi] using congrArg Prod.snd he
    exact Prod.ext rfl (Prod.ext (hinj z hz hcc) rfl)
  have hKreg (p : (ℝ × ℝ) × (ℝ × ℝ)) (hp : p ∈ K) :
      Injective (fderiv ℝ Xi p) := by
    obtain ⟨z, u, y⟩ := p
    have hy : y = 0 := hp.2.2
    subst y
    exact hcentral z hp.1 u
  have hKlocal (p : (ℝ × ℝ) × (ℝ × ℝ)) (hp : p ∈ K) :
      ∃ W ∈ 𝓝 p, InjOn Xi W := by
    obtain ⟨l, hl, he, _⟩ := hlocal p (hKreg p hp)
    refine ⟨l.source, l.open_source.mem_nhds hl, ?_⟩
    have heq : (l : _ → _) = Xi := funext he
    rw [← heq]
    exact l.injOn
  obtain ⟨W, hW, hKW, hWinj⟩ := hKinj.exists_isOpen_superset hKcompact
    (fun p _ => hXi.continuous.continuousAt) hKlocal
  let Reg := {p : (ℝ × ℝ) × (ℝ × ℝ) | Injective (fderiv ℝ Xi p)}
  have hReg : IsOpen Reg := ContinuousLinearMap.isOpen_injective.preimage
    (hXi.continuous_fderiv (by simp))
  have hKO : K ⊆ W ∩ Reg := fun p hp => ⟨hKW hp, hKreg p hp⟩
  obtain ⟨A0, B0, hA0, hB0, hKA, hIB, hAB⟩ := generalized_tube_lemma
    (isCompact_Icc.prod isCompact_Icc) (isCompact_Icc.prod isCompact_singleton)
    (hW.inter hReg) hKO
  obtain ⟨A1, A2, hA1, hA2, hIA1, hIA2, hA12⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_Icc hA0 hKA
  obtain ⟨L0, Y0, _, hY0, hIL0, h0Y0, hLY⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hB0 hIB
  obtain ⟨m1, hm1, hmargin1⟩ := exists_interval_margin hab hA1 hIA1
  obtain ⟨m2, hm2, hmargin2⟩ := exists_interval_margin hcd hA2 hIA2
  obtain ⟨w0, hw0, hwidth0⟩ := exists_interval_margin (a := 0) (b := 0) le_rfl hY0
    (by simpa only [Icc_self] using h0Y0)
  let m := min 1 (min m1 m2)
  let w := min 1 w0
  have hm : 0 < m := lt_min (by norm_num) (lt_min hm1 hm2)
  have hmle : m ≤ 1 := min_le_left _ _
  have hmm1 : m ≤ m1 := (min_le_right _ _).trans (min_le_left _ _)
  have hmm2 : m ≤ m2 := (min_le_right _ _).trans (min_le_right _ _)
  have hw : 0 < w := lt_min (by norm_num) hw0
  have hwle : w ≤ 1 := min_le_left _ _
  have hww0 : w ≤ w0 := min_le_right _ _
  let P := Ioo (a - m) (b + m) ×ˢ Ioo (c - m) (d + m)
  let U : Set ((ℝ × ℝ) × (ℝ × ℝ)) := P ×ˢ {q | |q.2| < w}
  have hPO (z : ℝ × ℝ) (hz : z ∈ P) : z ∈ A0 := hA12 ⟨
    hmargin1 ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
    hmargin2 ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hPP1 (z : ℝ × ℝ) (hz : z ∈ P) : z ∈ P1 :=
    ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hcore (p : (ℝ × ℝ) × (ℝ × ℝ)) (hp : p ∈ U) (hpu : |p.2.1| ≤ M) :
      p ∈ W ∩ Reg := by
    have hpy := abs_lt.mp (show |p.2.2| < w from hp.2)
    exact hAB ⟨hPO p.1 hp.1, hLY ⟨hIL0 (abs_le.mp hpu),
      hwidth0 ⟨by linarith [hpy.1], by linarith [hpy.2]⟩⟩⟩
  have hcorebound (p : (ℝ × ℝ) × (ℝ × ℝ)) (hp : p ∈ U) (hpu : |p.2.1| ≤ M) :
      |(Xi p).2.1| ≤ M := by
    by_cases htailu : R < |p.2.1|
    · simpa only [htailXi p.1 p.2.1 p.2.2 htailu] using hpu
    · have hpuR : |p.2.1| ≤ R := le_of_not_gt htailu
      have hpp : (p.1, p.2.1) ∈ P1 ×ˢ L1 := ⟨hPP1 p.1 hp.1,
        ⟨by linarith [(abs_le.mp hpuR).1], by linarith [(abs_le.mp hpuR).2]⟩⟩
      have hbb : |(C (p.1, p.2.1)).1| + |(N (p.1, p.2.1)).1| ≤ B :=
        hB ⟨(p.1, p.2.1), hpp, rfl⟩
      have hyy : |p.2.2| ≤ 1 := hp.2.le.trans hwle
      calc
        |(Xi p).2.1| = |(C (p.1, p.2.1)).1 + p.2.2 * (N (p.1, p.2.1)).1| := rfl
        _ ≤ |(C (p.1, p.2.1)).1| + |p.2.2| * |(N (p.1, p.2.1)).1| :=
          (abs_add_le _ _).trans (by rw [abs_mul])
        _ ≤ |(C (p.1, p.2.1)).1| + |(N (p.1, p.2.1)).1| :=
          add_le_add le_rfl (mul_le_of_le_one_left (abs_nonneg _) hyy)
        _ ≤ B := hbb
        _ ≤ M := hBM.le
  have hU : IsOpen U := (isOpen_Ioo.prod isOpen_Ioo).prod
    (isOpen_lt continuous_snd.abs continuous_const)
  have hUinj : InjOn Xi U := by
    intro p hp q hq he
    by_cases hpu : |p.2.1| ≤ M
    · by_cases hqu : |q.2.1| ≤ M
      · exact hWinj (hcore p hp hpu).1 (hcore q hq hqu).1 he
      · have hqt : R < |q.2.1| := by linarith [lt_of_not_ge hqu]
        have hqeq := htailXi q.1 q.2.1 q.2.2 hqt
        have heq := congrArg (fun r : (ℝ × ℝ) × (ℝ × ℝ) => |r.2.1|) he
        rw [hqeq] at heq
        exact False.elim (hqu (heq ▸ hcorebound p hp hpu))
    · by_cases hqu : |q.2.1| ≤ M
      · have hpt : R < |p.2.1| := by linarith [lt_of_not_ge hpu]
        have hpeq := htailXi p.1 p.2.1 p.2.2 hpt
        have heq := congrArg (fun r : (ℝ × ℝ) × (ℝ × ℝ) => |r.2.1|) he
        rw [hpeq] at heq
        exact False.elim (hpu (heq.symm ▸ hcorebound q hq hqu))
      · have hpt : R < |p.2.1| := by linarith [lt_of_not_ge hpu]
        have hqt : R < |q.2.1| := by linarith [lt_of_not_ge hqu]
        rw [htailXi p.1 p.2.1 p.2.2 hpt, htailXi q.1 q.2.1 q.2.2 hqt] at he
        exact he
  have hUlocal (p : (ℝ × ℝ) × (ℝ × ℝ)) (hp : p ∈ U) :
      ∃ l : OpenPartialHomeomorph ((ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ) × (ℝ × ℝ)),
        p ∈ l.source ∧ (∀ q, l q = Xi q) ∧ ContDiffAt ℝ ∞ l.symm (Xi p) := by
    apply hlocal p
    by_cases hpu : |p.2.1| ≤ M
    · exact (hcore p hp hpu).2
    · have hpt : R < |p.2.1| := by linarith [lt_of_not_ge hpu]
      have hpeq : Xi =ᶠ[𝓝 p] id := by
        filter_upwards [(isOpen_lt continuous_const continuous_snd.fst.abs).mem_nhds hpt]
          with q hq
        exact htailXi q.1 q.2.1 q.2.2 hq
      rw [hpeq.fderiv_eq, fderiv_id]
      exact injective_id
  obtain ⟨T, hs, hT, hTi⟩ := exists_openPartialHomeomorph_of_injective_localInverses
    Xi U hU hXi.continuous.continuousOn hUinj hUlocal
  refine ⟨m, hm, hmle, w, hw, hwle, T, hs, hT, ?_, hTi, ?_⟩
  · have heq : (T : _ → _) = Xi := funext hT
    rw [heq]
    exact hXi.contDiffOn
  · intro z hz u y hy hu
    rw [hT]
    exact htailXi z u y (by linarith)

end PoincareConjecture.M25.Topology3D
