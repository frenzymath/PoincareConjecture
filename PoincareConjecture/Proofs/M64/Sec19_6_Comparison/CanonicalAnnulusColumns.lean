import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.CanonicalRampRegularity
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.AreaDensityProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

noncomputable def m64CanonicalAnnulusMap
    (P : M62.CircleProductData F circumference) (f : LoopPlane → M)
    (p : LoopPlane) : P.charts.Point :=
  (f p, P.circle.quotient (circumference * p 0 / curvePeriod))

theorem m64CanonicalAnnulusMap_contMDiffAt
    (P : M62.CircleProductData F circumference) {f : LoopPlane → M}
    {p : LoopPlane} (hf : ContMDiffAt (𝓡 2) (𝓡 n) 1 f p) :
    ContMDiffAt (𝓡 2) (𝓡 (n + 1)) 1 (m64CanonicalAnnulusMap P f) p := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  have hphi : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 1
      (fun z : LoopPlane => circumference * z 0 / curvePeriod) :=
    contMDiff_iff_contDiff.mpr
      ((contDiff_const.mul (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff).div_const _)
  exact (P.charts.from_product_smooth.of_le (m := 1) (by norm_num)).contMDiffAt.comp p
    (hf.prodMk ((P.circle.quotient_smooth.of_le (m := 1) (by norm_num)).contMDiffAt.comp p
      hphi.contMDiffAt))

theorem m64CanonicalAnnulusMap_split
    (P : M62.CircleProductData F circumference) {f : LoopPlane → M}
    {p : LoopPlane} (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f p)
    (v : LoopPlane) :
    P.charts.split (m64CanonicalAnnulusMap P f p)
        (mfderiv (𝓡 2) (𝓡 (n + 1)) (m64CanonicalAnnulusMap P f) p v) =
      (mfderiv (𝓡 2) (𝓡 n) f p v,
        mfderiv 𝓘(ℝ, ℝ) (𝓡 1) P.circle.quotient
          (circumference * p 0 / curvePeriod) ((circumference / curvePeriod) * v 0)) := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  let phi : LoopPlane → ℝ := fun z => circumference * z 0 / curvePeriod
  let L : LoopPlane →L[ℝ] ℝ :=
    (circumference / curvePeriod) • EuclideanSpace.proj 0
  have hphi : HasFDerivAt phi L p := by
    convert! L.hasFDerivAt (x := p) using 1
    funext z
    change circumference * z 0 / curvePeriod = (circumference / curvePeriod) * z 0
    ring
  have hc : MDifferentiableAt (𝓡 2) (𝓡 1)
      (fun z => P.circle.quotient (phi z)) p :=
    (P.circle.quotient_smooth.mdifferentiableAt (by simp)).comp p
      hphi.hasMFDerivAt.mdifferentiableAt
  have hgraph : MDifferentiableAt (𝓡 2) (𝓡 (n + 1)) (m64CanonicalAnnulusMap P f) p :=
    (P.charts.from_product_smooth.mdifferentiableAt (by simp)).comp p (hf.prodMk hc)
  apply Prod.ext
  · rw [P.charts.split_space]
    have h := mfderiv_comp_apply (f := m64CanonicalAnnulusMap P f)
      (g := (Prod.fst : P.charts.Point → M)) p
      ((contMDiff_fst.comp P.charts.to_product_smooth).mdifferentiableAt (by simp)) hgraph v
    exact h.symm
  · rw [P.charts.split_circle]
    have h := mfderiv_comp_apply (f := m64CanonicalAnnulusMap P f)
      (g := (Prod.snd : P.charts.Point → P.circle.Point)) p
      ((contMDiff_snd.comp P.charts.to_product_smooth).mdifferentiableAt (by simp)) hgraph v
    have hq := mfderiv_comp_apply p
      (P.circle.quotient_smooth.mdifferentiableAt (by simp))
      hphi.hasMFDerivAt.mdifferentiableAt v
    rw [hphi.hasMFDerivAt.mfderiv] at hq
    exact h.symm.trans hq

theorem m64CanonicalAnnulusMap_tangentNorm_sq
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {f : LoopPlane → M} {p : LoopPlane}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f p) (v : LoopPlane) :
    (P.flow.metric t).tangentNorm (m64CanonicalAnnulusMap P f p)
        (mfderiv (𝓡 2) (𝓡 (n + 1)) (m64CanonicalAnnulusMap P f) p v) ^ 2 =
      (F.metric t).tangentNorm (f p) (mfderiv (𝓡 2) (𝓡 n) f p v) ^ 2 +
        ((circumference / curvePeriod) * v 0) ^ 2 := by
  have hp : 0 ≤ (P.flow.metric t).inner (m64CanonicalAnnulusMap P f p)
      (mfderiv (𝓡 2) (𝓡 (n + 1)) (m64CanonicalAnnulusMap P f) p v)
      (mfderiv (𝓡 2) (𝓡 (n + 1)) (m64CanonicalAnnulusMap P f) p v) :=
    ((P.flow.metric t).toRiemannianMetric.toCore _).re_inner_nonneg _
  have hb : 0 ≤ (F.metric t).inner (f p)
      (mfderiv (𝓡 2) (𝓡 n) f p v) (mfderiv (𝓡 2) (𝓡 n) f p v) :=
    ((F.metric t).toRiemannianMetric.toCore _).re_inner_nonneg _
  rw [RiemannianMetric.tangentNorm, Real.sq_sqrt hp,
    P.metric_eq, m64CanonicalAnnulusMap_split P hf v]
  change (F.metric t).inner (f p) _ _ +
      P.circle.metricOnPoints.inner
        (P.circle.quotient (circumference * p 0 / curvePeriod)) _ _ = _
  erw [P.circle.metric_quotient]
  unfold RiemannianMetric.tangentNorm
  rw [Real.sq_sqrt hb]
  ring

theorem m64CanonicalAnnulusMap_column_bounds
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {f : LoopPlane → M} {p : LoopPlane}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f p)
    {B epsilon : ℝ} (hB : 0 ≤ B) (hepsilon : 0 ≤ epsilon)
    (h0 : (F.metric t).tangentNorm (f p)
      (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ B)
    (h1 : (F.metric t).tangentNorm (f p)
      (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ epsilon)
    (hcirc : circumference ≤ curvePeriod) :
    (P.flow.metric t).tangentNorm (m64CanonicalAnnulusMap P f p)
        (mfderiv (𝓡 2) (𝓡 (n + 1)) (m64CanonicalAnnulusMap P f) p
          (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ B + 1 ∧
    (P.flow.metric t).tangentNorm (m64CanonicalAnnulusMap P f p)
        (mfderiv (𝓡 2) (𝓡 (n + 1)) (m64CanonicalAnnulusMap P f) p
          (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ epsilon := by
  have hs0 := m64CanonicalAnnulusMap_tangentNorm_sq P t hf
    (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  have hs1 := m64CanonicalAnnulusMap_tangentNorm_sq P t hf
    (EuclideanSpace.basisFun (Fin 2) ℝ 1)
  have he0 : (EuclideanSpace.basisFun (Fin 2) ℝ 0) 0 = 1 := by
    simp [EuclideanSpace.basisFun_apply]
  have he1 : (EuclideanSpace.basisFun (Fin 2) ℝ 1) 0 = 0 := by
    simp [EuclideanSpace.basisFun_apply]
  rw [he0, mul_one] at hs0
  rw [he1, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at hs1
  have hk0 : 0 ≤ circumference / curvePeriod :=
    (div_pos P.circle.positive Real.two_pi_pos).le
  have hk1 : circumference / curvePeriod ≤ 1 :=
    (div_le_one Real.two_pi_pos).mpr hcirc
  have hn0 : 0 ≤ (F.metric t).tangentNorm (f p)
      (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) :=
    Real.sqrt_nonneg _
  have hn1 : 0 ≤ (F.metric t).tangentNorm (f p)
      (mfderiv (𝓡 2) (𝓡 n) f p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) :=
    Real.sqrt_nonneg _
  constructor
  · nlinarith
  · nlinarith

end PoincareConjecture
