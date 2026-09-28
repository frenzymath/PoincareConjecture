import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.RicciIntegralCutoff
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Minimizing
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Frame.Field
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Jacobi.CurvatureFrame












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle BigOperators

noncomputable section

universe u

namespace PoincareConjecture.LeviCivitaData

open Conjugate.Realization ConjugateFrame ConnectionAlongCurve ConjugateVariation
open Poincare.RicciIntegral

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private lemma exists_larger_interval {I : Set ℝ} {L : ℝ}
    (hI : IsOpen I) (hL : 0 ≤ L) (hsub : Icc 0 L ⊆ I) :
    ∃ a b : ℝ, a < 0 ∧ L < b ∧ Icc a b ⊆ I := by
  obtain ⟨a, c, hac, hleft⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hI.mem_nhds (hsub ⟨le_rfl, hL⟩))
  obtain ⟨d, b, hdb, hright⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hI.mem_nhds (hsub ⟨hL, le_rfl⟩))
  refine ⟨a / 2, (L + b) / 2, by linarith [hac.1], by linarith [hdb.2], ?_⟩
  intro s hs
  by_cases hs0 : s < 0
  · exact hleft ⟨by linarith [hs.1, hac.1], hs0.trans hac.2⟩
  by_cases hsL : L < s
  · exact hright ⟨hdb.1.trans hsL, by linarith [hs.2, hdb.2]⟩
  exact hsub ⟨le_of_not_gt hs0, le_of_not_gt hsL⟩



theorem integral_ricci_le_of_constant_speed_weighted_upper
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {γ : ℝ → M} {I : Set ℝ} {L scale c : ℝ} {Λ : ℝ → ℝ}
    (hI : IsOpen I) (hsub : Icc 0 L ⊆ I)
    (hgeo : g.IsGeodesicOn γ I) (hL : 0 ≤ L) (hc : 0 < c)
    (hspeed : ∀ s ∈ Icc 0 L, g.tangentNorm (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) = c)
    (hmin : g.edist (γ 0) (γ L) = ENNReal.ofReal (L * c))
    (hΛ : ContinuousOn Λ (Icc 0 L)) (hscale : 0 < scale)
    (hRic : ∀ s ∈ Icc 0 L, D.ricci (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) ≤ Λ s) :
    (∫ s in (0 : ℝ)..L, D.ricci (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)) ≤
      2 * (n : ℝ) * scale +
        ∫ s in (0 : ℝ)..L, (1 - cutoff L scale s ^ 2) * Λ s := by
  classical
  rcases hL.eq_or_lt with hzero | hL
  · subst L
    simp only [intervalIntegral.integral_same]
    positivity
  obtain ⟨a, b, ha, hb, hlarge⟩ := exists_larger_interval hI hL.le hsub
  have hab : a < b := ha.trans (hL.trans hb)
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I :=
    fun s hs => (contMDiffAt_of_isGeodesicOn hgeo hs).contMDiffWithinAt
  have hqt (s : ℝ) (hs : s ∈ I) : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ s :=
    contMDiffAt_of_isGeodesicOn hgeo hs
  obtain ⟨P, hi, hP, hp⟩ := exists_orthonormal_parallel_transport g hab hI hq hlarge
  have hsmall : Icc (0 : ℝ) L ⊆ Ioo a b :=
    fun s hs => ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  have hsmall' : Icc (0 : ℝ) L ⊆ Icc a b := hsmall.trans Ioo_subset_Icc_self
  let R := coefficient g γ P
  let basis := EuclideanSpace.basisFun (Fin n) ℝ
  let φ := cutoff L scale
  let r : ℝ → ℝ := fun s => D.ricci (γ s)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
  have hR : ContinuousOn R (Icc 0 L) := by
    intro s hs
    exact (contDiffAt_coefficient D hI hq (hsub hs) (hi s (hsmall' hs))
      (fun u => (hP s (hsmall' hs) u).1)).continuousAt.continuousWithinAt
  have htrace : ∀ s ∈ Icc 0 L, ∑ i, inner ℝ (R s (basis i)) (basis i) = r s := by
    intro s hs
    obtain ⟨Q, hQ⟩ := hi s (hsmall' hs)
    have heq : R s = D.radialCurvatureInFrame (γ s) Q
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) := by
      apply ContinuousLinearMap.ext
      intro u
      dsimp only [R, coefficient]
      rw [chartCoefficient_apply D P (mem_extChartAt_source _) (hqt s (hsub hs))]
      simp only [← hQ, radialCurvatureInFrame_apply,
        ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe]
      rfl
    rw [heq]
    change _ = D.ricci (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
    rw [← D.trace_radialCurvatureInFrame (γ s) Q
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)]
    rw [LinearMap.trace_eq_sum_inner _ basis]
    exact Finset.sum_congr rfl (fun i _ => real_inner_comm _ _)
  have hdiag (i : Fin n) : ContinuousOn (fun s => inner ℝ (R s (basis i)) (basis i))
      (Icc 0 L) := (hR.clm_apply continuousOn_const).inner continuousOn_const
  have hr : ContinuousOn r (Icc 0 L) :=
    (continuousOn_finsetSum Finset.univ (fun i _ => hdiag i)).congr
      (fun s hs => (htrace s hs).symm)
  have hφ : ContDiff ℝ ∞ φ := contDiff_cutoff L scale
  have hφ' : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have henergy : IntervalIntegrable (fun s => deriv φ s ^ 2) volume 0 L :=
    (hφ'.pow 2).intervalIntegrable 0 L
  have hweight (i : Fin n) : IntervalIntegrable
      (fun s => φ s ^ 2 * inner ℝ (R s (basis i)) (basis i)) volume 0 L :=
    ((hφ.continuous.pow 2).continuousOn.mul (hdiag i)).intervalIntegrable_of_Icc hL.le
  have hindex (i : Fin n) :
      (∫ s in (0 : ℝ)..L, φ s ^ 2 * inner ℝ (R s (basis i)) (basis i)) ≤
        ∫ s in (0 : ℝ)..L, deriv φ s ^ 2 := by
    let W : ℝ → EuclideanSpace ℝ (Fin n) := fun s => φ s • basis i
    let V : ℝ → EuclideanSpace ℝ (Fin n) := fun s => P s (W s)
    have hW : ContDiff ℝ ∞ W := hφ.smul contDiff_const
    have hdW : deriv W = fun s => deriv φ s • basis i := by
      funext s
      exact ((hφ.differentiable (by simp) s).hasDerivAt.smul_const (basis i)).deriv
    have hV : ∀ s ∈ Ioo a b, ContDiffAt ℝ ∞ (chartField γ (γ s) V) s := by
      intro s hs
      exact contDiffAt_frame_field (fun u => (hP s (Ioo_subset_Icc_self hs) u).1)
        hW.contDiffAt
    have hn := index_nonneg_of_minimizing g D
      (a := 0) (c := L / 2) (b := L) (by linarith) (by linarith)
      isOpen_Ioo hsmall (fun s hs => hgeo s (hlarge (Ioo_subset_Icc_self hs)))
      hV hV rfl (by simp [V, W, φ]) (by simp [V, W, φ]) hc hspeed
      (by simpa only [sub_zero] using hmin)
    have hbasis : inner ℝ (basis i) (basis i) = 1 := by
      rw [real_inner_self_eq_norm_sq, basis.orthonormal.1 i]
      norm_num
    have heq (s : ℝ) (hs : s ∈ Icc 0 L) :
        intrinsicIndexIntegrand g D γ V s =
          deriv φ s ^ 2 - φ s ^ 2 * inner ℝ (R s (basis i)) (basis i) := by
      rw [indexIntegrand_frame_field D (hsmall hs) hi (hqt s (hsub hs))
        (hP s (hsmall' hs)) (hp s (hsmall' hs)) hW.contDiffAt]
      simp only [Poincare.ODE.Jacobi.indexIntegrand, W, hdW, map_smul,
        real_inner_smul_left, real_inner_smul_right, hbasis]
      ring
    have hIc : ContinuousOn (intrinsicIndexIntegrand g D γ V) (Icc 0 L) :=
      ((hφ'.pow 2).continuousOn.sub
        ((hφ.continuous.pow 2).continuousOn.mul (hdiag i))).congr
          (fun s hs => heq s hs)
    have hIi : IntervalIntegrable (intrinsicIndexIntegrand g D γ V) volume 0 L :=
      hIc.intervalIntegrable_of_Icc hL.le
    have hhalf₀ : 0 ≤ L / 2 := by linarith
    have hhalfL : L / 2 ≤ L := by linarith
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hIi.mono_set (by
        simpa only [uIcc_of_le hhalf₀, uIcc_of_le hL.le] using
          Icc_subset_Icc le_rfl hhalfL))
      (hIi.mono_set (by
        simpa only [uIcc_of_le hhalfL, uIcc_of_le hL.le] using
          Icc_subset_Icc hhalf₀ le_rfl))] at hn
    have heqIntegral : (∫ s in (0 : ℝ)..L, intrinsicIndexIntegrand g D γ V s) =
        (∫ s in (0 : ℝ)..L, deriv φ s ^ 2) -
          ∫ s in (0 : ℝ)..L, φ s ^ 2 * inner ℝ (R s (basis i)) (basis i) := by
      calc
        _ = ∫ s in (0 : ℝ)..L,
            deriv φ s ^ 2 - φ s ^ 2 * inner ℝ (R s (basis i)) (basis i) :=
          intervalIntegral.integral_congr fun s hs => heq s
            (by simpa only [uIcc_of_le hL.le] using hs)
        _ = _ := intervalIntegral.integral_sub henergy (hweight i)
    rw [heqIntegral] at hn
    linarith
  have hweighted : (∫ s in (0 : ℝ)..L, φ s ^ 2 * r s) ≤
      (n : ℝ) * ∫ s in (0 : ℝ)..L, deriv φ s ^ 2 := by
    calc
      _ = ∫ s in (0 : ℝ)..L, ∑ i, φ s ^ 2 * inner ℝ (R s (basis i)) (basis i) := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp only
        rw [← htrace s (by simpa only [uIcc_of_le hL.le] using hs), Finset.mul_sum]
      _ = ∑ i, ∫ s in (0 : ℝ)..L, φ s ^ 2 * inner ℝ (R s (basis i)) (basis i) :=
        intervalIntegral.integral_finsetSum (fun i _ => hweight i)
      _ ≤ ∑ _i : Fin n, ∫ s in (0 : ℝ)..L, deriv φ s ^ 2 :=
        Finset.sum_le_sum (fun i _ => hindex i)
      _ = _ := by simp
  have hdefect : (∫ s in (0 : ℝ)..L, (1 - φ s ^ 2) * r s) ≤
      ∫ s in (0 : ℝ)..L, (1 - φ s ^ 2) * Λ s := by
    have hc : Continuous (fun s => 1 - φ s ^ 2) :=
      continuous_const.sub (hφ.continuous.pow 2)
    apply intervalIntegral.integral_mono_on hL.le
      ((hc.continuousOn.mul hr).intervalIntegrable_of_Icc hL.le)
      ((hc.continuousOn.mul hΛ).intervalIntegrable_of_Icc hL.le)
    intro s hs
    have hphi := cutoff_mem_Icc hscale.le hs
    have hnonneg : 0 ≤ 1 - φ s ^ 2 := by dsimp [φ]; nlinarith [hphi.1, hphi.2]
    exact mul_le_mul_of_nonneg_left (hRic s hs) hnonneg
  have hsplit : (∫ s in (0 : ℝ)..L, r s) =
      (∫ s in (0 : ℝ)..L, φ s ^ 2 * r s) +
        ∫ s in (0 : ℝ)..L, (1 - φ s ^ 2) * r s := by
    have hi₁ : IntervalIntegrable (fun s => φ s ^ 2 * r s) volume 0 L :=
      ((hφ.continuous.pow 2).continuousOn.mul hr).intervalIntegrable_of_Icc hL.le
    have hi₂ : IntervalIntegrable (fun s => (1 - φ s ^ 2) * r s) volume 0 L :=
      ((continuous_const.sub (hφ.continuous.pow 2)).continuousOn.mul hr).intervalIntegrable_of_Icc
        hL.le
    rw [← intervalIntegral.integral_add hi₁ hi₂]
    exact intervalIntegral.integral_congr (fun s _ => by ring)
  change (∫ s in (0 : ℝ)..L, r s) ≤ _
  rw [hsplit]
  calc
    _ ≤ (n : ℝ) * (2 * scale) +
        ∫ s in (0 : ℝ)..L, (1 - φ s ^ 2) * Λ s :=
      add_le_add (hweighted.trans (mul_le_mul_of_nonneg_left
        (integral_deriv_cutoff_sq_le hL.le hscale) (Nat.cast_nonneg _))) hdefect
    _ = _ := by ring

private lemma integral_ricci_le_of_constant_speed
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {γ : ℝ → M} {I : Set ℝ} {L Λ scale c : ℝ}
    (hI : IsOpen I) (hsub : Icc 0 L ⊆ I)
    (hgeo : g.IsGeodesicOn γ I) (hL : 0 ≤ L) (hc : 0 < c)
    (hspeed : ∀ s ∈ Icc 0 L, g.tangentNorm (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) = c)
    (hmin : g.edist (γ 0) (γ L) = ENNReal.ofReal (L * c))
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale)
    (hRic : ∀ s ∈ Icc 0 L, D.ricci (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) ≤ Λ) :
    (∫ s in (0 : ℝ)..L, D.ricci (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)) ≤
      2 * (n : ℝ) * scale + 4 * Λ / scale := by
  apply (D.integral_ricci_le_of_constant_speed_weighted_upper hI hsub hgeo hL hc
    hspeed hmin (Λ := fun _ => Λ) continuousOn_const hscale hRic).trans
  rw [intervalIntegral.integral_mul_const]
  have h := mul_le_mul_of_nonneg_right (integral_cutoff_defect_le hL hscale) hΛ
  gcongr
  convert h using 1
  ring



theorem integral_ricci_le_of_minimizing
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {γ : ℝ → M} {I : Set ℝ} {L Λ scale : ℝ}
    (hI : IsOpen I) (hsub : Icc 0 L ⊆ I)
    (hgeo : g.IsGeodesicOn γ I) (hL : 0 ≤ L)
    (hspeed : ∀ s ∈ Icc 0 L, g.tangentNorm (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) = 1)
    (hmin : g.edist (γ 0) (γ L) = ENNReal.ofReal L)
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale)
    (hRic : ∀ s ∈ Icc 0 L, D.ricci (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) ≤ Λ) :
    (∫ s in (0 : ℝ)..L, D.ricci (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)) ≤
      2 * (n : ℝ) * scale + 4 * Λ / scale :=
  integral_ricci_le_of_constant_speed D hI hsub hgeo hL zero_lt_one hspeed
    (by simpa only [mul_one] using hmin) hΛ hscale hRic



theorem integral_ricci_div_speed_le_of_minimizing
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {γ : ℝ → M} {I : Set ℝ} {L Λ scale c : ℝ}
    (hI : IsOpen I) (hsub : Icc 0 L ⊆ I)
    (hgeo : g.IsGeodesicOn γ I) (hL : 0 ≤ L) (hc : 0 < c)
    (hspeed : ∀ s ∈ Icc 0 L, g.tangentNorm (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) = c)
    (hmin : g.edist (γ 0) (γ L) = ENNReal.ofReal (L * c))
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale)
    (hRic : ∀ s ∈ Icc 0 L, D.ricci (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) ≤ Λ * c ^ 2) :
    (∫ s in (0 : ℝ)..L, D.ricci (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) / c) ≤
      2 * (n : ℝ) * scale + 4 * Λ / scale := by
  have h := integral_ricci_le_of_constant_speed D hI hsub hgeo hL hc hspeed hmin
    (mul_nonneg hΛ (sq_nonneg c)) (mul_pos hscale hc) hRic
  rw [intervalIntegral.integral_div]
  apply (div_le_iff₀ hc).mpr
  apply h.trans_eq
  field_simp

end PoincareConjecture.LeviCivitaData
