import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamMatchingCircle
import PoincareConjecture.Proofs.M60.Mathlib.LipschitzGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

namespace PoincareConjecture

local notation "v" => m64AnnulusSeamTranslation

theorem m64Scalar_fderiv_translation {phi : LoopPlane → ℝ}
    (hp : ContDiff ℝ 1 phi) (a p w : LoopPlane) :
    fderiv ℝ (fun q => phi (a + q)) p w = fderiv ℝ phi (a + p) w := by
  have ht := (hasFDerivAt_id (𝕜 := ℝ) p).const_add a
  have hd := ((hp.differentiable (by norm_num) (a + p)).hasFDerivAt.comp p ht).fderiv
  have h := congrArg (fun L : LoopPlane →L[ℝ] ℝ => L w) hd
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using h

theorem m64_exists_compact_lipschitz_seam_test
    {K : Set LoopPlane} (hK : IsCompact K) (hKO : K ⊆ m64AnnulusSeamDomain)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi)
    (hseam : ∀ s ∈ Icc (0 : ℝ) 1,
      phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) :
    ∃ (psi : LoopPlane → ℝ) (L : ℝ≥0), LipschitzWith L psi ∧ HasCompactSupport psi ∧
      ∀ p ∈ K, p 0 ≠ 0 →
        psi p = (if p 0 < 0 then phi (v + p) else phi p) ∧
        ∀ i : Fin 2,
          fderiv ℝ psi p (EuclideanSpace.single i 1) =
            if p 0 < 0 then fderiv ℝ phi (v + p) (EuclideanSpace.single i 1)
            else fderiv ℝ phi p (EuclideanSpace.single i 1) := by
  classical
  obtain ⟨delta, eta, hdelta, -, heta, hetac, -, hone, hsupp⟩ :=
    Poincare.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      hK m64AnnulusSeamDomain_isOpen hKO
  let left := fun p : LoopPlane => eta p * phi (v + p)
  let right := fun p : LoopPlane => eta p * phi p
  let psi := {p : LoopPlane | p 0 ≤ 0}.piecewise left right
  have hleft : ContDiff ℝ 1 left :=
    (heta.of_le (by simp)).mul (hp.comp (contDiff_const.add contDiff_id))
  have hright : ContDiff ℝ 1 right := (heta.of_le (by simp)).mul hp
  have hlc : HasCompactSupport left := hetac.mul_right
  have hrc : HasCompactSupport right := hetac.mul_right
  obtain ⟨CL, hCL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hlc hleft (by norm_num)
  obtain ⟨CR, hCR⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hrc hright (by norm_num)
  have hmatch (p : LoopPlane) (hz : p 0 = 0) : left p = right p := by
    by_cases he : eta p = 0
    · simp only [left, right, he, zero_mul]
    have hO := hsupp (subset_tsupport eta he)
    have hpoint : p = annulusPoint 0 (p 1) := by
      ext i
      fin_cases i <;> simp [annulusPoint, hz]
    have htranslated : v + p = annulusPoint curvePeriod (p 1) := by
      ext i
      fin_cases i <;> simp [m64AnnulusSeamTranslation, annulusPoint, hz]
    have hvalue : phi (v + p) = phi p := by
      rw [htranslated, hpoint]
      exact hseam (p 1) ⟨hO.2.2.1.le, hO.2.2.2.le⟩
    simp only [left, right, hvalue]
  have hLip : LipschitzWith (max CL CR) psi := by
    apply lipschitzOnWith_univ.mp
    exact M60.lipschitzOnWith_piecewise_of_convex convex_univ
      (fun p : LoopPlane => p 0) (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.continuousOn 0
      hCL.lipschitzOnWith hCR.lipschitzOnWith (fun p _ hz => hmatch p hz)
  have hc : HasCompactSupport psi := by
    apply HasCompactSupport.intro' (K := tsupport eta) hetac (isClosed_tsupport eta)
    intro p hpeta
    have hz : eta p = 0 := image_eq_zero_of_notMem_tsupport hpeta
    simp only [psi, left, right, piecewise, hz, zero_mul, ite_self]
  refine ⟨psi, max CL CR, hLip, hc, ?_⟩
  intro p hpK hp0
  have hetanear : eta =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds p hdelta] with q hq
    exact hone q (Metric.mem_cthickening_of_dist_le q p delta K hpK
      (Metric.mem_ball.mp hq).le)
  rcases lt_or_gt_of_ne hp0 with hn | hpos
  · have hnear : psi =ᶠ[𝓝 p] (fun q => phi (v + q)) := by
      have hnegative := (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous
        continuous_const).mem_nhds hn
      filter_upwards [hetanear, hnegative] with q hq hneg
      change q 0 < 0 at hneg
      simp only [psi, piecewise, mem_ofPred_eq, if_pos hneg.le, left, hq, one_mul]
    refine ⟨?_, fun i => ?_⟩
    · simpa only [if_pos hn] using hnear.eq_of_nhds
    · rw [if_pos hn, hnear.fderiv_eq, m64Scalar_fderiv_translation hp]
  · have hnear : psi =ᶠ[𝓝 p] phi := by
      have hpositive := (isOpen_lt continuous_const
        (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous).mem_nhds hpos
      filter_upwards [hetanear, hpositive] with q hq hgt
      change 0 < q 0 at hgt
      simp only [psi, piecewise, mem_ofPred_eq, if_neg (not_le.mpr hgt), right, hq, one_mul]
    refine ⟨?_, fun i => ?_⟩
    · simpa only [if_neg (not_lt.mpr hpos.le)] using hnear.eq_of_nhds
    · rw [if_neg (not_lt.mpr hpos.le), hnear.fderiv_eq]

end PoincareConjecture
