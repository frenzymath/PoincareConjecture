import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMixedRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64SmallPotential_bilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64SmallPotential_bilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64SmallPotential_trilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64SmallPotential_trilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 1000000 in

theorem m64WeightedMixedMetric_small_potential
    (dirichlet : Fin n → Prop) {a : LoopPlane} {R : ℝ} (hR : 0 < R)
    (G : LoopPlane → E →L[ℝ] E →L[ℝ] ℝ)
    (T : LoopPlane → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (w : Fin 2 → ℝ) (V : Fin 2 → LoopPlane → E) (u : LoopPlane → E)
    {kappa mu C Lambda : ℝ} (hk : 0 < kappa) (hmu : 0 < mu) (hC : 0 ≤ C)
    (hw : ∀ i, mu ≤ w i ∧ w i ≤ Lambda)
    (hG : ∀ p ∈ ball a R ∩ {p : LoopPlane | 0 < p 1},
      ‖G p‖ ≤ C ∧ ‖T p‖ ≤ C ∧ ∀ v : E, kappa * ‖v‖ ^ 2 ≤ G p v v)
    (hu : Continuous u) (hu0 : u a = 0)
    (hz : ∀ j, dirichlet j → ∀ p : LoopPlane, p 1 < 0 → u p j = 0)
    (hV : ∀ i, MemLp (V i) 2 volume)
    (hweak : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) univ)
    (hflux : ∀ j : Fin n, ∀ i : Fin 2,
      MemLp (fun p => w i * G p (V i p) (EuclideanSpace.single j 1))
        2 (volume.restrict (ball a R ∩ {p : LoopPlane | 0 < p 1})))
    (hsource : ∀ j : Fin n, IntegrableOn (fun p =>
      -(∑ i : Fin 2, w i * T p (EuclideanSpace.single j 1) (V i p) (V i p)) / 2)
      (ball a R ∩ {p : LoopPlane | 0 < p 1}))
    (heq : ∀ j : Fin n, ∀ phi : LoopPlane → ℝ,
      ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ ball a R →
      (dirichlet j → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) →
      (∫ p, ∑ i : Fin 2,
        (ball a R ∩ {p : LoopPlane | 0 < p 1}).indicator
          (fun q => w i * G q (V i q) (EuclideanSpace.single j 1)) p *
            fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p, (ball a R ∩ {p : LoopPlane | 0 < p 1}).indicator
          (fun q => -(∑ i : Fin 2,
            w i * T q (EuclideanSpace.single j 1) (V i q) (V i q)) / 2) p * phi p)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ phi : LoopPlane → ℝ,
      ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ ball a r →
      (∫ p in ball a r ∩ {p : LoopPlane | 0 < p 1},
        (∑ i : Fin 2, ‖V i p‖ ^ 2) * phi p ^ 2) ≤
        eta * ∫ p in ball a r ∩ {p : LoopPlane | 0 < p 1},
          ∑ i : Fin 2, (fderiv ℝ phi p (EuclideanSpace.single i 1)) ^ 2 := by
  let nu := kappa * mu
  have hnu : 0 < nu := mul_pos hk hmu
  have ht : Tendsto (fun s : ℝ => 4 * (C * Lambda) ^ 2 * s ^ 2 / nu)
      (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div] using
      (show Continuous (fun s : ℝ => 4 * (C * Lambda) ^ 2 * s ^ 2 / nu) by fun_prop
        ).continuousAt (x := 0)
  have ht' : Tendsto (fun s : ℝ => C * Lambda * s) (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, mul_zero] using
      (show Continuous (fun s : ℝ => C * Lambda * s) by fun_prop).continuousAt (x := 0)
  obtain ⟨eps, heps, he⟩ := Metric.eventually_nhds_iff.mp
    ((ht.eventually (eventually_lt_nhds (show (0 : ℝ) < eta * nu / 2 by positivity))).and
      (ht'.eventually (eventually_lt_nhds (show (0 : ℝ) < nu / 4 by positivity))))
  let delta := eps / 2
  have hd : 0 < delta := half_pos heps
  have hdmem : dist delta 0 < eps := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hd]
    exact half_lt_self heps
  have hdsmall := he hdmem
  obtain ⟨rho, hrho, hurho⟩ := Metric.continuousAt_iff.mp hu.continuousAt delta hd
  let r := min (R / 2) (rho / 2)
  have hr : 0 < r := lt_min (half_pos hR) (half_pos hrho)
  have hrR : r < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hrrho : r < rho := (min_le_right _ _).trans_lt (half_lt_self hrho)
  let S := ball a r ∩ {p : LoopPlane | 0 < p 1}
  have hSm : MeasurableSet S := measurableSet_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous).measurableSet
  have hsub : S ⊆ ball a R ∩ {p : LoopPlane | 0 < p 1} :=
    inter_subset_inter_left _ (ball_subset_ball hrR.le)
  have hub : ∀ p ∈ S, ‖u p‖ ≤ delta := by
    intro p hp
    have hh := (hurho (Metric.mem_ball.mp hp.1 |>.trans hrrho)).le
    simpa only [hu0, dist_zero_right] using hh
  have hsame : ball a r ∩ (ball a R ∩ {p : LoopPlane | 0 < p 1}) = S := by
    ext p
    constructor
    · intro hp
      exact ⟨hp.1, hp.2.2⟩
    · intro hp
      exact ⟨hp.1, ball_subset_ball hrR.le hp.1, hp.2⟩
  refine ⟨r, hr, hrR, fun phi hp hc hs => ?_⟩
  have hpot := m64WeightedMixedMetric_potential dirichlet isOpen_ball hSm G T w V V u
    hk hmu hC hd.le hw hdsmall.2.le (fun p hp => hG p (hsub hp)) hu hz hub hV hweak
    (fun _ _ _ => rfl) (fun i => (hV i).restrict S)
    (fun j i => (hflux j i).mono_measure (Measure.restrict_mono hsub le_rfl))
    (fun j => (hsource j).mono_set hsub) (fun j psi hpsi hpc hps hzero => by
      have heq' := m64MixedBoundary_indicator_restrict (ball_subset_ball hrR.le)
        (heq j) hpsi hpc hps hzero
      rwa [hsame] at heq') hp hc hs
  have hgrad : 0 ≤ ∫ p in S, ∑ i : Fin 2,
      (fderiv ℝ phi p (EuclideanSpace.single i 1)) ^ 2 :=
    integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbound := mul_le_mul_of_nonneg_right hdsmall.1.le hgrad
  change nu / 2 * _ ≤ _ at hpot
  change _ ≤ eta * _
  nlinarith

end PoincareConjecture
