import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.RicciIntegral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Ricci.CovectorBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Transverse.RadialFrame

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle BigOperators

noncomputable section

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] in
private theorem continuousAt_ricci_curve
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    {q : ℝ → M} {V : (s : ℝ) → TangentSpace (𝓡 3) (q s)} {t : ℝ}
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞ q t)
    (hV : ContDiffAt ℝ ∞ (ConnectionAlongCurve.chartField q (q t) V) t) :
    ContinuousAt (fun s => D.ricci (q s) (V s) (V s)) t := by
  let c := extChartAt (𝓡 3) (q t)
  let R := fun s => LeviCivitaData.tensorCoordinateSection
    D.ricciEvaluation_isSmooth_manifold (q t) (c.symm (c (q s)))
  have hcoord := ConnectionAlongCurve.contDiffAt_chart_curve hq (mem_extChartAt_source _)
  have hR : ContDiffAt ℝ ∞ R t := by
    have hRt := LeviCivitaData.contDiffAt_tensorCoordinateSection
      D.ricciEvaluation_isSmooth_manifold (q t)
      (c.map_source (mem_extChartAt_source _))
    have hRc := hRt.comp t hcoord
    exact hRc
  have hVs : ContDiffAt ℝ ∞ (fun s => fun _ : Fin 2 =>
      ConnectionAlongCurve.chartField q (q t) V s) t :=
    contDiffAt_pi.mpr (fun _ => hV)
  have heval := (TensorFiber.continuousMultilinear
    (E := EuclideanSpace ℝ (Fin 3)) (k := 2)).analyticOnNhd_uncurry_of_multilinear
    (s := Set.univ) |>.contDiff (n := ∞)
  apply ((heval.contDiffAt.comp t (hR.prodMk hVs)).continuousAt).congr_of_eventuallyEq
  filter_upwards [hq.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓡 3) (q t)).mem_nhds
      (mem_extChartAt_source (I := 𝓡 3) _))] with s hs
  have hrec : LeviCivitaData.constantCoordinateField (q t)
      (ConnectionAlongCurve.chartField q (q t) V s) (q s) = V s := by
    unfold LeviCivitaData.constantCoordinateField ConnectionAlongCurve.chartField
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt
      (by simpa only [Set.mem_preimage, extChartAt_source] using hs)]
    exact Bundle.Trivialization.symmL_continuousLinearMapAt _
      (by simpa only [Set.mem_preimage, TangentBundle.trivializationAt_baseSet,
        extChartAt_source] using hs) _
  simp only [Function.comp_apply, TensorFiber.continuousMultilinear_apply, R,
    c.left_inv hs, LeviCivitaData.tensorCoordinateSection_apply,
    LeviCivitaData.tensorCoordinateEvaluation, LeviCivitaData.ricciEvaluation, hrec]

theorem exists_integral_abs_ricci_le_sqrt_length
    (S : GradientShrinkingSolitonData 3 M)
    (hD : S.connection.CurvatureTensorCalculus) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ → M) (I : Set ℝ) (L : ℝ),
      IsOpen I → Icc 0 L ⊆ I → S.metric.IsGeodesicOn γ I → 0 ≤ L →
      (∀ s ∈ Icc 0 L, S.metric.tangentNorm (γ s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1) = 1) →
      S.metric.edist (γ 0) (γ L) = ENNReal.ofReal L →
      ∀ W : (s : ℝ) → TangentSpace (𝓡 3) (γ s),
      (∀ s ∈ Icc 0 L, S.metric.inner (γ s) (W s) (W s) = 1) →
      (∫ s in (0 : ℝ)..L, |S.connection.ricci (γ s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1) (W s)|) ≤ C * Real.sqrt L := by
  obtain ⟨K, hK, hRm⟩ := S.bounded_curvature
  let B : ℝ := 3 * K
  let A : ℝ := 6 + 4 * B
  refine ⟨(B * A + 1) / 2, by dsimp [A, B]; positivity, ?_⟩
  intro γ I L hI hsub hgeo hL hspeed hmin W hW
  rcases hL.eq_or_lt with hzero | hL
  · subst L
    simp
  let v := fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1
  let r : ℝ → ℝ := fun s => S.connection.ricci (γ s) (v s) (v s)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR (x : M) : S.connection.scalarCurvature x ≤ B := by
    exact (S.connection.scalarCurvature_le_curvatureTensorNorm_sharp x).trans
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hRm x)) (by norm_num))
  have hRic (x : M) (w : TangentSpace (𝓡 3) x) :=
    S.connection.ricci_bounds_of_nonnegative_curvatureOperator hD x
      (S.nonnegative_curvature x) w
  have hunit (s : ℝ) (hs : s ∈ Icc 0 L) : S.metric.inner (γ s) (v s) (v s) = 1 := by
    have hn : 0 ≤ S.metric.inner (γ s) (v s) (v s) := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨S.metric.toRiemannianMetric⟩
      change 0 ≤ inner ℝ (v s) (v s)
      exact real_inner_self_nonneg
    have h := Real.sq_sqrt hn
    change (S.metric.tangentNorm (γ s) (v s)) ^ 2 = _ at h
    rw [hspeed s hs] at h
    norm_num at h ⊢
    exact h.symm
  have hrnonneg (s : ℝ) : 0 ≤ r s := (hRic (γ s) (v s)).1
  have hrbound (s : ℝ) (hs : s ∈ Icc 0 L) : r s ≤ B := by
    exact (hRic (γ s) (v s)).2.trans (by rw [hunit s hs, mul_one]; exact hR _)
  have hrc : ContinuousOn r (Icc 0 L) := by
    intro s hs
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_ricci_curve S.connection
      (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hgeo (hsub hs))
    exact RiemannianMetric.contDiffAt_chartField_velocity hI
      (fun s hs => (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hgeo hs).contMDiffWithinAt)
      (hsub hs) (mem_extChartAt_source _)
  have hri : IntervalIntegrable r volume 0 L := hrc.intervalIntegrable_of_Icc hL.le
  have hInt : (∫ s in (0 : ℝ)..L, r s) ≤ A := by
    convert
      S.connection.integral_ricci_le_of_minimizing hI hsub hgeo hL.le hspeed hmin
        hB (by norm_num : (0 : ℝ) < 1) hrbound using 1
    norm_num [A, r, v]
  have hpair (s : ℝ) (hs : s ∈ Icc 0 L) :
      (S.connection.ricci (γ s) (v s) (W s)) ^ 2 ≤ B * r s := by
    have hcs := S.connection.sq_ricci_le_ricci_mul_ricci hD (γ s)
      (fun w => (hRic (γ s) w).1) (v s) (W s)
    have hw : S.connection.ricci (γ s) (W s) (W s) ≤ B :=
      (hRic (γ s) (W s)).2.trans (by rw [hW s hs, mul_one]; exact hR _)
    exact hcs.trans ((mul_le_mul_of_nonneg_left hw (hrnonneg s)).trans_eq (mul_comm _ _))
  let upper : ℝ → ℝ := fun s => (L * B * r s + 1) / (2 * Real.sqrt L)
  have hupper : IntervalIntegrable upper volume 0 L :=
    ((hrc.const_mul (L * B)).add continuousOn_const |>.div_const
      (2 * Real.sqrt L)).intervalIntegrable_of_Icc hL.le
  have hpoint (s : ℝ) (hs : s ∈ Icc 0 L) :
      |S.connection.ricci (γ s) (v s) (W s)| ≤ upper s := by
    have hsq := sq_nonneg (Real.sqrt L * |S.connection.ricci (γ s) (v s) (W s)| - 1)
    have hLsqrt := Real.sq_sqrt hL.le
    have hp := mul_le_mul_of_nonneg_left (hpair s hs) hL.le
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt L)).mpr
    nlinarith [sq_abs (S.connection.ricci (γ s) (v s) (W s))]
  have hcompare : (∫ s in (0 : ℝ)..L,
      |S.connection.ricci (γ s) (v s) (W s)|) ≤ ∫ s in (0 : ℝ)..L, upper s := by
    rw [intervalIntegral.integral_of_le hL.le, intervalIntegral.integral_of_le hL.le]
    apply integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hupper.1
    exact (ae_restrict_mem measurableSet_Ioc).mono fun s hs => hpoint s (Ioc_subset_Icc_self hs)
  have hupperInt : (∫ s in (0 : ℝ)..L, upper s) ≤
      (B * A + 1) / 2 * Real.sqrt L := by
    rw [show upper = fun s => (L * B * r s + 1) / (2 * Real.sqrt L) from rfl,
      intervalIntegral.integral_div,
      intervalIntegral.integral_add (hri.const_mul (L * B)) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul, mul_one]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt L)).mpr
    have hb := mul_le_mul_of_nonneg_left hInt (mul_nonneg hL.le hB)
    calc
      _ ≤ L * B * A + L := add_le_add hb le_rfl
      _ = (B * A + 1) / 2 * Real.sqrt L * (2 * Real.sqrt L) := by
        calc
          _ = (B * A + 1) * (Real.sqrt L) ^ 2 := by rw [Real.sq_sqrt hL.le]; ring
          _ = _ := by ring
  exact hcompare.trans hupperInt

end PoincareConjecture.GradientShrinkingSolitonData
