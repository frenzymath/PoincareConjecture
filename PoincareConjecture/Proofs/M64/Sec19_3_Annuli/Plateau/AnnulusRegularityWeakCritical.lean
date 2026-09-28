import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityLocalMinimum
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaFirstVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

set_option maxHeartbeats 1600000 in

theorem M64ObservedWeakAnnulus.weak_critical_coordinates
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsEmbedding e) (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q)
    (b : M) {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    {a : LoopPlane} {R : ℝ} (hR : 0 < R) (hRS : Metric.closedBall a R ⊆ S)
    (hu : Continuous u)
    (huT : MapsTo u (Metric.closedBall a R) (extChartAt (𝓡 n) b).target)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (Metric.ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j)
      (Metric.ball a R))
    (hmap : EqOn ((extChartAt (𝓡 n) b).symm ∘ u) A.map (Metric.closedBall a R)) :
    M60.SUWeakAlphaCoordinate g b 1 u W a ((R / 4) * Real.exp (-1)) := by
  let r := (R / 4) * Real.exp (-1)
  let D := Metric.ball a (R / 2)
  have hquarter : 0 < R / 4 := div_pos hR (by norm_num)
  have hr : 0 < r := mul_pos hquarter (Real.exp_pos _)
  have hexp : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hrquarter : r < R / 4 := mul_lt_of_lt_one_right hquarter hexp
  have hrhalf : r < R / 2 := by linarith
  have hrR : r < R := by linarith
  have hsmallR : Metric.closedBall a r ⊆ Metric.closedBall a R :=
    Metric.closedBall_subset_closedBall hrR.le
  have hsmallD : Metric.ball a r ⊆ D := Metric.ball_subset_ball hrhalf.le
  have hsmallB : Metric.ball a r ⊆ Metric.ball a R := Metric.ball_subset_ball hrR.le
  have htest (phi : LoopPlane → EuclideanSpace ℝ (Fin n)) (hp : ContDiff ℝ ∞ phi)
      (hps : tsupport phi ⊆ Metric.ball a r) :
      IntegrableOn (M60.suAlphaChartVariation g b 1 u W phi) (Metric.ball a r) ∧
        (∫ p in Metric.ball a r, M60.suAlphaChartVariation g b 1 u W phi p) = 0 := by
    obtain ⟨delta, K, hd, hK, hKt, hU⟩ := m64_affine_variation_compact_range
      (isCompact_closedBall a R) hu.continuousOn hp.continuous.continuousOn
      (isOpen_extChartAt_target b) huT
    let G := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let F := fun (t : ℝ) (p : LoopPlane) =>
      (G (u p + t • phi p)
          (W 0 p + t • fderiv ℝ phi p (EuclideanSpace.single 0 1))
          (W 0 p + t • fderiv ℝ phi p (EuclideanSpace.single 0 1)) +
        G (u p + t • phi p)
          (W 1 p + t • fderiv ℝ phi p (EuclideanSpace.single 1 1))
          (W 1 p + t • fderiv ℝ phi p (EuclideanSpace.single 1 1))) / 2
    let J := fun (t : ℝ) (p : LoopPlane) => M60.suAlphaLocalDensity g b 1 p
      ((u p, (W 0 p, W 1 p)) + t • (phi p, M60.suAlphaDerivativePair phi p))
    have hJ (t : ℝ) (p : LoopPlane) : J t p = M60.suAlphaRoundFactor p + 2 * F t p := by
      simp only [J, M60.suAlphaDerivativePair, EuclideanSpace.basisFun_apply]
      change (M60.suAlphaRoundFactor p) ^ (1 - (1 : ℝ)) *
        (M60.suAlphaRoundFactor p +
          (G (u p + t • phi p)
            (W 0 p + t • fderiv ℝ phi p (EuclideanSpace.single 0 1))
            (W 0 p + t • fderiv ℝ phi p (EuclideanSpace.single 0 1)) +
          G (u p + t • phi p)
            (W 1 p + t • fderiv ℝ phi p (EuclideanSpace.single 1 1))
            (W 1 p + t • fderiv ℝ phi p (EuclideanSpace.single 1 1)))) ^ (1 : ℝ) = _
      simp only [sub_self, Real.rpow_zero, one_mul, Real.rpow_one]
      dsimp only [F]
      ring
    have hlocal : ∀ t : ℝ, |t| < delta → IntegrableOn (F t) D ∧
        (∫ p in D, F 0 p) ≤ ∫ p in D, F t p :=
      A.affine_chart_energy_minimum g he hei Q hQ hb hdiag hmin b hR hRS
        hu.continuousOn hp hps hW hw hmap hd hK hKt hU
    have hzero : |(0 : ℝ)| < delta := by simpa using hd
    have hlam : Continuous M60.suAlphaRoundFactor := continuous_const.div₀
      (((continuous_norm.pow 2).add continuous_const).pow 2) (fun _ => by positivity)
    have hlamI : IntegrableOn M60.suAlphaRoundFactor D :=
      (hlam.continuousOn.integrableOn_compact (isCompact_closedBall a (R / 2))).mono_set
        Metric.ball_subset_closedBall
    have hint : IntegrableOn (fun p => M60.suAlphaLocalDensity g b 1 p
        (u p, (W 0 p, W 1 p))) D := by
      have h := hlamI.add ((hlocal 0 hzero).1.const_mul 2)
      apply h.congr
      filter_upwards with p
      simpa only [J, zero_smul, add_zero, Pi.add_apply] using (hJ 0 p).symm
    have hWsmall : ∀ i, MemLp (W i) (ENNReal.ofReal (2 * (1 : ℝ)))
        (volume.restrict (Metric.ball a (R / 2))) := by
      intro i
      simpa using (hW i).mono_measure
        (Measure.restrict_mono (Metric.ball_subset_ball (by linarith : R / 2 ≤ R)) le_rfl)
    obtain ⟨hvarI, hder⟩ := M60.suAlpha_integral_firstVariation g b (alpha := 1) le_rfl
      u phi hu hp W a (R / 2) hWsmall
      hK hKt hd
      (fun t ht p hpD => hU t ht
        ((Metric.closedBall_subset_closedBall (by linarith : R / 2 ≤ R)) hpD)) hint
    have hJint (t : ℝ) (ht : |t| < delta) :
        (∫ p in D, J t p) = (∫ p in D, M60.suAlphaRoundFactor p) +
          2 * ∫ p in D, F t p := by
      simp_rw [hJ]
      rw [integral_add hlamI ((hlocal t ht).1.const_mul 2), integral_const_mul]
    have hm : IsLocalMin (fun t : ℝ => ∫ p in D, J t p) 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hd] with t ht
      have ht' : |t| < delta := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
      rw [hJint t ht', hJint 0 hzero]
      linarith [(hlocal t ht').2]
    have hvar0 : (∫ p in D, M60.suAlphaChartVariation g b 1 u W phi p) = 0 :=
      hm.hasDerivAt_eq_zero hder
    refine ⟨hvarI.mono_set hsmallD, ?_⟩
    rw [← hvar0]
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet hsmallD
    intro p hpD
    have hnot : p ∉ tsupport phi := fun hpS => hpD.2 (hps hpS)
    have hp0 := image_eq_zero_of_notMem_tsupport hnot
    have hdp0 := fderiv_of_notMem_tsupport ℝ hnot
    simp only [M60.suAlphaChartVariation, hp0, hdp0, map_zero, zero_apply,
      mul_zero, Finset.sum_const_zero, add_zero]
  refine ⟨hr, (fun p hp => huT (hsmallR hp)), hu.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using m64MemLp_on_ball_of_continuous_closedBall hu.continuousOn 2 (a := a) (R := r)
  · intro i
    simpa using (hW i).mono_measure (Measure.restrict_mono hsmallB le_rfl)
  · intro i j
    exact (hw i j).restrict Metric.isOpen_ball hsmallB
  · intro phi hp _ hps
    exact (htest phi hp hps).1
  · intro phi hp _ hps
    exact (htest phi hp hps).2

end PoincareConjecture
