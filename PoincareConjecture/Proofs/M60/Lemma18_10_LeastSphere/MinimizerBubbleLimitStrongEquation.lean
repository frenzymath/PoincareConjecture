import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerBubbleLimitRegularity
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.DerivativeLimit
import PoincareConjecture.Proofs.M60.Mathlib.CovariantIntegrationByPartsTests



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

open CoordinateExponential ConnectionVariation ConjugateVariation
  Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.WeakCompactness

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin 2) ℝ

local instance suStrongEquationBilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suStrongEquationBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance suStrongEquationTrilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suStrongEquationTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private theorem classical_columns
    {g : RiemannianMetric n M} {p : M} {u : LoopPlane → E}
    {V : Fin 2 → LoopPlane → E} {center : LoopPlane} {R r : ℝ}
    (S : SUWeakAlphaCoordinate g p 1 u V center R)
    (hsub : Metric.ball center r ⊆ Metric.ball center R)
    (hu : ∀ z ∈ Metric.closedBall center r, ContDiffAt ℝ 2 u z) :
    ∀ i, V i =ᵐ[volume.restrict (Metric.ball center r)]
      fun z => fderiv ℝ u z (e i) := by
  let O := Metric.ball center r
  let mu := volume.restrict O
  let : IsFiniteMeasure (volume.restrict (Metric.ball center R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hD (i : Fin 2) : ContinuousOn (fun z => fderiv ℝ u z (e i))
      (Metric.closedBall center r) := by
    intro z hz
    exact (((hu z hz).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).continuousAt.continuousWithinAt
  have huc : ContDiffOn ℝ 1 u O := fun z hz =>
    ((hu z (Metric.ball_subset_closedBall hz)).of_le (by norm_num)).contDiffWithinAt
  intro i
  have hcomp (a : Fin n) : (fun z => V i z a) =ᵐ[mu]
      fun z => (fderiv ℝ u z (e i)) a := by
    have hclass : HasWeakPartialDeriv i (fun z => (fderiv ℝ u z (e i)) a)
        (fun z => u z a) O := by
      intro phi hp hc hs
      have ht := setIntegral_test_fderiv Metric.isOpen_ball
        ((EuclideanSpace.proj a).contDiff.comp_contDiffOn huc) hp hc hs (e i)
      have hd (z : LoopPlane) (hz : z ∈ O) :
          fderiv ℝ (fun y => u y a) z (e i) = (fderiv ℝ u z (e i)) a := by
        exact congrArg (fun A : LoopPlane →L[ℝ] ℝ => A (e i))
          (((EuclideanSpace.proj a).hasFDerivAt.comp z
            ((huc.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt
              (by norm_num)).hasFDerivAt).fderiv)
      have he : (∫ z in O, phi z * fderiv ℝ (fun y => u y a) z (e i)) =
          ∫ z in O, (fderiv ℝ u z (e i)) a * phi z := by
        apply setIntegral_congr_fun measurableSet_ball
        intro z hz
        change phi z * fderiv ℝ (fun y => u y a) z (e i) = _
        rw [hd z hz, mul_comm]
      simp only [smul_eq_mul] at ht
      change (∫ z in O, phi z * fderiv ℝ (fun y => u y a) z (e i)) =
        -(∫ z in O, fderiv ℝ phi z (e i) * u z a) at ht
      rw [he] at ht
      simpa only [neg_neg, mul_comm, EuclideanSpace.basisFun_apply] using
        (congrArg Neg.neg ht).symm
    apply ((S.weak_derivative i a).restrict Metric.isOpen_ball hsub).ae_eq
      Metric.isOpen_ball hclass
    · have hI : IntegrableOn (fun z => V i z a) (Metric.ball center R) :=
        (EuclideanSpace.proj a : E →L[ℝ] ℝ).integrable_comp
          ((S.column_memLp i).integrable (by norm_num))
      exact (hI.mono_set hsub).locallyIntegrable
    · exact (((EuclideanSpace.proj a).continuous.comp_continuousOn (hD i)
        |>.integrableOn_compact (isCompact_closedBall center r)).mono_set
          Metric.ball_subset_closedBall).locallyIntegrable
  filter_upwards [ae_all_iff.mpr hcomp] with z hz
  exact PiLp.ext fun a => hz a

set_option maxHeartbeats 2200000 in




theorem suWeakAlphaCoordinate_harmonic_of_smooth
    {g : RiemannianMetric n M} {p : M} {u : LoopPlane → E}
    {V : Fin 2 → LoopPlane → E} {center : LoopPlane} {R : ℝ}
    (S : SUWeakAlphaCoordinate g p 1 u V center R) (hs : ContDiffAt ℝ ∞ u center) :
    ∑ i : Fin 2, covDerivAlong
      (christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)) u
      (fun y => fderiv ℝ u y (e i)) (e i) center = 0 := by
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
  let Gamma := christoffelBilinear G
  let W := fun i z => fderiv ℝ u z (e i)
  let tau := fun z => ∑ i : Fin 2, covDerivAlong Gamma u (W i) (e i) z
  have hnear := (hs.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).eventually
    (by norm_num)
  obtain ⟨r, hr, hsmall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hnear.and (Metric.ball_mem_nhds center S.radius_pos))
  let O := Metric.ball center r
  have hu (z : LoopPlane) (hz : z ∈ Metric.closedBall center r) : ContDiffAt ℝ 2 u z :=
    (hsmall hz).1
  have hsub : Metric.closedBall center r ⊆ Metric.ball center R := fun z hz => (hsmall hz).2
  have hV := classical_columns S (Metric.ball_subset_closedBall.trans hsub) hu
  have hrange (z : LoopPlane) (hz : z ∈ O) :=
    S.coordinate_range (Metric.ball_subset_closedBall (hsub (Metric.ball_subset_closedBall hz)))
  have hG (z : LoopPlane) (hz : z ∈ O) : ContDiffAt ℝ ∞ G (u z) :=
    (g.contDiffOn_chartCoefficients p).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds (hrange z hz))
  have huc : ContDiffOn ℝ 2 u O := fun z hz =>
    (hu z (Metric.ball_subset_closedBall hz)).contDiffWithinAt
  have hW (i : Fin 2) : ContDiffOn ℝ 1 (W i) O :=
    (huc.fderiv_of_isOpen Metric.isOpen_ball (by norm_num)).clm_apply contDiffOn_const
  have hpair (w : E) : G (u center) (tau center) w = 0 := by
    let F := fun i z => G (u z) (W i z) w
    let A := fun z => ∑ i : Fin 2, fderiv ℝ G (u z) w (W i z) (W i z)
    let T := fun z => 2 * (∑ i : Fin 2, fderiv ℝ (F i) z (e i)) - A z
    have hF (i : Fin 2) : ContDiffOn ℝ 1 (F i) O := by
      intro z hz
      exact ((((hG z hz).of_le (by simp)).comp z
        ((hu z (Metric.ball_subset_closedBall hz)).of_le (by norm_num))).clm_apply
          ((hW i).contDiffAt (Metric.isOpen_ball.mem_nhds hz)) |>.clm_apply
            contDiffAt_const).contDiffWithinAt
    have hA : ContinuousOn A O := by
      apply continuousOn_finsetSum
      intro i _ z hz
      have hd : ContDiffAt ℝ 1 (fderiv ℝ G) (u z) :=
        (hG z hz).fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)
      have hu1 : ContDiffAt ℝ 1 u z := (hu z (Metric.ball_subset_closedBall hz)).of_le (by norm_num)
      have hWi := (hW i).contDiffAt (Metric.isOpen_ball.mem_nhds hz)
      have hleft := ((hd.comp z hu1).clm_apply (contDiffAt_const (c := w))).clm_apply hWi
      have hc := hleft.clm_apply hWi
      exact hc.continuousAt.continuousWithinAt
    have hT : ContinuousOn T O :=
      (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ =>
        (((hF i).continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl).clm_apply
          continuousOn_const))).sub hA
    have hzero : T center = 0 := by
      apply eqOn_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
        Metric.isOpen_ball hT ?_ (Metric.mem_ball_self hr)
      intro psi hp hc hsupport
      let phi := fun z => psi z • w
      have hphi : ContDiff ℝ ∞ phi := hp.smul contDiff_const
      have hpc : HasCompactSupport phi := hc.smul_right
      have hps : tsupport phi ⊆ O := (tsupport_smul_subset_left psi (fun _ => w)).trans hsupport
      have hfull := S.variation_zero phi hphi hpc
        (hps.trans (Metric.ball_subset_closedBall.trans hsub))
      have hvi : (∫ z in O, suAlphaChartVariation g p 1 u V phi z) = 0 := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at hfull ⊢
        · exact hfull
        all_goals
          intro z hz
          have hnot : z ∉ tsupport phi := fun hh => hz (by
            first | exact hps hh | exact (hps.trans (Metric.ball_subset_closedBall.trans hsub)) hh)
          simp [suAlphaChartVariation, image_eq_zero_of_notMem_tsupport hnot,
            fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot]
      have hclass : (∫ z in O,
          psi z * A z + 2 * ∑ i : Fin 2, F i z * fderiv ℝ psi z (e i)) = 0 := by
        rw [← hvi]
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hV] with z hz
        have hd := (hp.differentiable (by simp) z).hasFDerivAt.smul_const w
        simp only [suAlphaChartVariation, sub_self, Real.rpow_zero, mul_one, one_mul,
          hz, phi, hd.fderiv, smul_apply, ContinuousLinearMap.smulRight_apply,
          map_smul, smul_eq_mul, EuclideanSpace.basisFun_apply]
        simp only [A, F, G, W, Fin.sum_univ_two, EuclideanSpace.basisFun_apply,
          extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_id]
        ring
      have hi (i : Fin 2) := integral_test_fderiv Metric.isOpen_ball (hF i) hp hc hsupport (e i)
      have hAi := integrable_test_smul Metric.isOpen_ball hp.continuous hc hsupport hA
      have hFi (i : Fin 2) := integrable_test_smul Metric.isOpen_ball
        (((hp.continuous_fderiv (by simp)).clm_apply continuous_const))
        (hc.fderiv_apply ℝ (e i)) ((tsupport_fderiv_apply_subset ℝ (e i)).trans hsupport)
        (hF i).continuousOn
      have hDi (i : Fin 2) := integrable_test_smul Metric.isOpen_ball hp.continuous hc hsupport
        (((hF i).continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl).clm_apply
          (continuousOn_const (c := e i)))
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at hclass
      · simp only [smul_eq_mul] at hi hAi hFi hDi ⊢
        have heqT (z : LoopPlane) : psi z * T z =
            2 * (psi z * fderiv ℝ (F 0) z (e 0) + psi z * fderiv ℝ (F 1) z (e 1)) -
              psi z * A z := by simp only [T, Fin.sum_univ_two]; ring
        have hDsum : Integrable (fun z => psi z * fderiv ℝ (F 0) z (e 0) +
            psi z * fderiv ℝ (F 1) z (e 1)) := (hDi 0).add (hDi 1)
        have hDtwo : Integrable (fun z => 2 * (psi z * fderiv ℝ (F 0) z (e 0) +
            psi z * fderiv ℝ (F 1) z (e 1))) := hDsum.const_mul 2
        simp_rw [heqT]
        rw [integral_sub hDtwo hAi,
          integral_const_mul, integral_add (hDi 0) (hDi 1), hi 0, hi 1]
        have heq (z : LoopPlane) : psi z * A z +
            2 * ∑ i : Fin 2, F i z * fderiv ℝ psi z (e i) =
            psi z * A z + 2 * (fderiv ℝ psi z (e 0) * F 0 z +
              fderiv ℝ psi z (e 1) * F 1 z) := by
          rw [Fin.sum_univ_two]
          ring
        simp_rw [heq] at hclass
        have hFsum : Integrable (fun z => fderiv ℝ psi z (e 0) * F 0 z +
            fderiv ℝ psi z (e 1) * F 1 z) := (hFi 0).add (hFi 1)
        have hFtwo : Integrable (fun z => 2 * (fderiv ℝ psi z (e 0) * F 0 z +
            fderiv ℝ psi z (e 1) * F 1 z)) := hFsum.const_mul 2
        rw [integral_add hAi hFtwo,
          integral_const_mul, integral_add (hFi 0) (hFi 1)] at hclass
        linarith
      · intro z hz
        have hn : z ∉ tsupport psi := fun h => hz (hsupport h)
        simp [image_eq_zero_of_notMem_tsupport hn, fderiv_of_notMem_tsupport (𝕜 := ℝ) hn]
    have hc0 : center ∈ O := Metric.mem_ball_self hr
    have hm := isMetricCompatibleAt_chartCoefficients g p (hrange center hc0)
    have hterm (i : Fin 2) :
        2 * fderiv ℝ (F i) center (e i) -
          fderiv ℝ G (u center) w (W i center) (W i center) =
        2 * G (u center) (covDerivAlong Gamma u (W i) (e i) center) w := by
      have hh := fderiv_metricAlong hm ((hG center hc0).differentiableAt (by simp))
        (hs.differentiableAt (by simp))
        (((hW i).contDiffAt (Metric.isOpen_ball.mem_nhds hc0)).differentiableAt (by norm_num))
        (differentiableAt_const w) (e i)
      change fderiv ℝ (F i) center (e i) = _ at hh
      rw [hh, hm w (W i center) (W i center)]
      have hsym : ∀ a b : E, G (u center) a b = G (u center) b a := fun a b => g.symm _ _ _
      rw [christoffelBilinear_chart_symm g p (u center) w (W i center),
        hsym (Gamma (u center) (W i center) w) (W i center)]
      simp only [covDerivAlong_def]
      change 2 * (G (u center) (fderiv ℝ (W i) center (e i) +
        Gamma (u center) (W i center) (W i center)) w +
          G (u center) (W i center)
            (fderiv ℝ (fun _ : LoopPlane => w) center (e i) +
              Gamma (u center) (W i center) w)) -
        (G (u center) (W i center) (Gamma (u center) (W i center) w) +
          G (u center) (W i center) (Gamma (u center) (W i center) w)) = _
      rw [fderiv_const_apply, zero_apply, zero_add]
      dsimp only [W]
      ring
    have h0 := hterm 0
    have h1 := hterm 1
    change 2 * (∑ i : Fin 2, fderiv ℝ (F i) center (e i)) - A center = 0 at hzero
    simp only [A, Fin.sum_univ_two] at hzero
    change G (u center) (∑ i : Fin 2, covDerivAlong Gamma u (W i) (e i) center) w = 0
    simp only [Fin.sum_univ_two, map_add, add_apply]
    linarith
  apply (g.isInvertible_chartCoefficients p
    (S.coordinate_range (Metric.mem_closedBall_self S.radius_pos.le))).injective
  ext w
  simpa only [map_zero, zero_apply] using hpair w

end PoincareConjecture.M60
