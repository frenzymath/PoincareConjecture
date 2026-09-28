import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConformalInitialGain
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityAffineWeak

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64LocalGain_bilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64LocalGain_bilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64LocalGain_trilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64LocalGain_trilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 1600000 in

theorem m64WeightedMixedMetric_local_tangential_gain
    (dirichlet : Fin n → Prop) {a : LoopPlane} {R : ℝ}
    (hR : 0 < R) (ha : a 1 = 0)
    (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (w : Fin 2 → ℝ) (V : Fin 2 → LoopPlane → E) (u : LoopPlane → E)
    {kappa mu C Lambda : ℝ} (hk : 0 < kappa) (hmu : 0 < mu) (hC : 0 < C)
    (hw : ∀ i, mu ≤ w i ∧ w i ≤ Lambda)
    (hG : ∀ p ∈ ball a R ∩ {p : LoopPlane | 0 < p 1},
      ‖G (u p)‖ ≤ C ∧ ‖T (u p)‖ ≤ C ∧ ∀ v : E, kappa * ‖v‖ ^ 2 ≤ G (u p) v v)
    (hLip : ∀ p ∈ ball a R ∩ {p : LoopPlane | 0 < p 1},
      ∀ q ∈ ball a R ∩ {p : LoopPlane | 0 < p 1},
      ‖G (u p) - G (u q)‖ ≤ C * ‖u p - u q‖ ∧
      ‖T (u p) - T (u q)‖ ≤ C * ‖u p - u q‖)
    (hu : ContinuousOn u (closedBall a R))
    (hz : ∀ j, dirichlet j → ∀ p ∈ closedBall a R, p 1 ≤ 0 → u p j = 0)
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball a R)))
    (hweak : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) (ball a R))
    (hflux : ∀ j : Fin n, ∀ i : Fin 2,
      MemLp (fun p => w i * G (u p) (V i p) (EuclideanSpace.single j 1))
        2 (volume.restrict (ball a R ∩ {p : LoopPlane | 0 < p 1})))
    (hsource : ∀ j : Fin n, IntegrableOn (fun p =>
      -(∑ i : Fin 2, w i * T (u p) (EuclideanSpace.single j 1) (V i p) (V i p)) / 2)
      (ball a R ∩ {p : LoopPlane | 0 < p 1}))
    (heq : ∀ j : Fin n, ∀ phi : LoopPlane → ℝ,
      ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ ball a R →
      (dirichlet j → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) →
      (∫ p, ∑ i : Fin 2, (ball a R ∩ {p : LoopPlane | 0 < p 1}).indicator
        (fun q => w i * G (u q) (V i q) (EuclideanSpace.single j 1)) p *
          fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p, (ball a R ∩ {p : LoopPlane | 0 < p 1}).indicator
          (fun q => -(∑ i : Fin 2,
            w i * T (u q) (EuclideanSpace.single j 1) (V i q) (V i q)) / 2) p * phi p) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∃ Q : Fin 2 → LoopPlane → E,
      (∀ i, MemLp (Q i) 2 (volume.restrict (ball a r ∩ {p : LoopPlane | 0 < p 1}))) ∧
      (∀ i j, HasWeakPartialDeriv 0 (fun p => Q i p j) (fun p => V i p j)
        (ball a r ∩ {p : LoopPlane | 0 < p 1})) ∧
      ∀ q : ℝ, 1 ≤ q → MemLp (V 0) (ENNReal.ofReal q)
        (volume.restrict (ball a r ∩ {p : LoopPlane | 0 < p 1})) := by
  obtain ⟨chi, hchi, hchic, hchis, hone, hdata⟩ :=
    M60.suWeakMap_localization (by norm_num : (1 : ℝ) < 2) (half_lt_self hR)
      hu (by simpa using m64MemLp_on_ball_of_continuous_closedBall hu 2)
      (fun i => by simpa using hV i) hweak
  let U : LoopPlane → E := fun p => chi p • (u p - u a)
  let W : Fin 2 → LoopPlane → E := fun i p => chi p • V i p +
    fderiv ℝ chi p (EuclideanSpace.single i 1) • (u p - u a)
  let G' : E → E →L[ℝ] E →L[ℝ] ℝ := fun z => G (z + u a)
  let T' : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := fun z => T (z + u a)
  have hUc : Continuous U := by
    have h := (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
      (continuous_pi (fun j => (hdata j).1))
    convert h using 1
    funext p
    ext j
    simp only [U, Function.comp_apply, PiLp.smul_apply, PiLp.sub_apply,
      smul_eq_mul]
  have hUcompact : HasCompactSupport U := hchic.smul_right
  have hUa : U a = 0 := by simp [U]
  have hUz (j : Fin n) (hj : dirichlet j) (p : LoopPlane) (hp : p 1 < 0) :
      U p j = 0 := by
    have hza : u a j = 0 := hz j hj a (mem_closedBall_self hR.le) ha.le
    by_cases hps : p ∈ tsupport chi
    · have hzp : u p j = 0 := hz j hj p (ball_subset_closedBall (hchis hps)) hp.le
      simp [U, PiLp.smul_apply, PiLp.sub_apply, hza, hzp]
    · simp [U, image_eq_zero_of_notMem_tsupport hps]
  have hW (i : Fin 2) : MemLp (W i) 2 volume := by
    apply MemLp.of_eval_piLp
    intro j
    simpa only [W, PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply,
      smul_eq_mul, ENNReal.ofReal_ofNat] using ((hdata j).2.2.2 i).1
  have hweakW (i : Fin 2) (j : Fin n) :
      HasWeakPartialDeriv i (fun p => W i p j) (fun p => U p j) univ := by
    simpa only [U, W, PiLp.smul_apply, PiLp.sub_apply, PiLp.add_apply,
      smul_eq_mul] using ((hdata j).2.2.2 i).2
  have hUeq (p : LoopPlane) (hp : p ∈ ball a (R / 2)) : U p = u p - u a := by
    simp only [U, (hone p hp).1, one_smul]
  have hWeq (p : LoopPlane) (hp : p ∈ ball a (R / 2)) (i : Fin 2) : W i p = V i p := by
    simp only [W, (hone p hp).1, (hone p hp).2, one_smul, zero_apply, zero_smul, add_zero]
  have hGeq (p : LoopPlane) (hp : p ∈ ball a (R / 2)) : G' (U p) = G (u p) := by
    simp only [G', hUeq p hp, sub_add_cancel]
  have hTeq (p : LoopPlane) (hp : p ∈ ball a (R / 2)) : T' (U p) = T (u p) := by
    simp only [T', hUeq p hp, sub_add_cancel]
  let H : Set LoopPlane := {p : LoopPlane | 0 < p 1}
  let S : Set LoopPlane := ball a (R / 2) ∩ H
  have hH : IsOpen H := isOpen_lt continuous_const
    (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous
  have hS : MeasurableSet S := (isOpen_ball.inter hH).measurableSet
  have hsub : S ⊆ ball a R ∩ H :=
    inter_subset_inter_left _ (ball_subset_ball (half_le_self hR.le))
  have hGlocal (p : LoopPlane) (hp : p ∈ S) := hG p (hsub hp)
  have hGl : ∀ p ∈ S, ‖G' (U p)‖ ≤ C ∧ ‖T' (U p)‖ ≤ C ∧
      ∀ v : E, kappa * ‖v‖ ^ 2 ≤ G' (U p) v v := by
    intro p hp
    simpa only [hGeq p hp.1, hTeq p hp.1] using hGlocal p hp
  have hLipl : ∀ p ∈ S, ∀ q ∈ S,
      ‖G' (U p) - G' (U q)‖ ≤ C * ‖U p - U q‖ ∧
      ‖T' (U p) - T' (U q)‖ ≤ C * ‖U p - U q‖ := by
    intro p hp q hq
    rw [hGeq p hp.1, hGeq q hq.1, hTeq p hp.1, hTeq q hq.1]
    simpa only [hUeq p hp.1, hUeq q hq.1, sub_sub_sub_cancel_right]
      using hLip p (hsub hp) q (hsub hq)
  have hfluxl (j : Fin n) (i : Fin 2) : MemLp
      (fun p => w i * G' (U p) (W i p) (EuclideanSpace.single j 1)) 2
      (volume.restrict S) := by
    apply ((hflux j i).mono_measure (Measure.restrict_mono hsub le_rfl)).ae_eq
    filter_upwards [ae_restrict_mem hS] with p hp
    rw [hGeq p hp.1, hWeq p hp.1]
  have hsourcel (j : Fin n) : IntegrableOn (fun p =>
      -(∑ i : Fin 2, w i * T' (U p) (EuclideanSpace.single j 1) (W i p) (W i p)) / 2) S := by
    apply ((hsource j).mono_set hsub).congr
    filter_upwards [ae_restrict_mem hS] with p hp
    simp only [hTeq p hp.1, hWeq p hp.1]
  have hfluxeq (j : Fin n) (i : Fin 2) :
      S.indicator (fun p => w i * G' (U p) (W i p) (EuclideanSpace.single j 1)) =
      S.indicator (fun p => w i * G (u p) (V i p) (EuclideanSpace.single j 1)) := by
    funext p
    by_cases hp : p ∈ S
    · simp only [indicator_of_mem hp, hGeq p hp.1, hWeq p hp.1]
    · simp only [indicator_of_notMem hp]
  have hsourceeq (j : Fin n) :
      S.indicator (fun p => -(∑ i : Fin 2,
        w i * T' (U p) (EuclideanSpace.single j 1) (W i p) (W i p)) / 2) =
      S.indicator (fun p => -(∑ i : Fin 2,
        w i * T (u p) (EuclideanSpace.single j 1) (V i p) (V i p)) / 2) := by
    funext p
    by_cases hp : p ∈ S
    · simp only [indicator_of_mem hp, hTeq p hp.1, hWeq p hp.1]
    · simp only [indicator_of_notMem hp]
  have heql (j : Fin n) (phi : LoopPlane → ℝ) (hp : ContDiff ℝ ∞ phi)
      (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ ball a (R / 2))
      (hzphi : dirichlet j → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) :
      (∫ p, ∑ i : Fin 2, S.indicator
        (fun q => w i * G' (U q) (W i q) (EuclideanSpace.single j 1)) p *
          fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p, S.indicator (fun q => -(∑ i : Fin 2,
          w i * T' (U q) (EuclideanSpace.single j 1) (W i q) (W i q)) / 2) p * phi p := by
    simp_rw [hfluxeq j, hsourceeq j]
    have he := m64MixedBoundary_indicator_restrict
      (ball_subset_ball (half_le_self hR.le)) (heq j) hp hc hs hzphi
    have hsets : ball a (R / 2) ∩ (ball a R ∩ H) = S := by
      ext p
      constructor
      · rintro ⟨hp, -, hph⟩
        exact ⟨hp, hph⟩
      · rintro ⟨hp, hph⟩
        exact ⟨hp, ball_subset_ball (half_le_self hR.le) hp, hph⟩
    dsimp only [H] at hsets
    simpa only [hsets] using he
  obtain ⟨s, hs, hsR, h0, hh0, D, hD⟩ :=
    m64WeightedMixedMetric_uniform_tangential_quotients dirichlet (half_pos hR)
      G' T' w W U hk hmu hC hw hGl hLipl hUc hUcompact hUa hUz hW hweakW
      hfluxl hsourcel heql
  let O : Set LoopPlane := ball a s ∩ H
  have hO : IsOpen O := isOpen_ball.inter hH
  have hOc : IsCompact (closure O) := (isCompact_closedBall a s).of_isClosed_subset
    isClosed_closure (closure_minimal
      (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall)
  obtain ⟨Q, hQ, hQweak, hH1⟩ := m64TangentialHessian_of_integral_diffQuot_bound
    hO hOc hW (fun i j => (hweakW i j).restrict hO (subset_univ _))
    hh0 (fun _ => D) hD
  have hsmall : ball a (s / 2) ∩ H ⊆ O :=
    inter_subset_inter_left _ (ball_subset_ball (half_le_self hs.le))
  have hOS : O ⊆ S := inter_subset_inter_left _ (ball_subset_ball hsR.le)
  have hsmallOpen : IsOpen (ball a (s / 2) ∩ H) := isOpen_ball.inter hH
  have hWae (i : Fin 2) : W i =ᵐ[volume.restrict (ball a (s / 2) ∩ H)] V i := by
    filter_upwards [ae_restrict_mem ((isOpen_ball.inter hH).measurableSet)] with p hp
    exact hWeq p (hOS (hsmall hp)).1 i
  refine ⟨s / 2, half_pos hs, (half_lt_self hs).trans (hsR.trans (half_lt_self hR)),
    Q, fun i => (hQ i).mono_measure (Measure.restrict_mono hsmall le_rfl), ?_, ?_⟩
  · intro i j
    exact m64WeakPartialDeriv_ae_congr
      ((hWae i).mono fun p hp => congrArg (fun z : E => z j) hp)
      EventuallyEq.rfl ((hQweak i j).restrict hsmallOpen hsmall)
  · intro q hq
    have hgain : MemLp (W 0) (ENNReal.ofReal q)
        (volume.restrict (ball a (s / 2) ∩ H)) :=
      MemLp.of_eval_piLp (fun j => m64HalfBall_H1_memLp (half_lt_self hs) (hH1 j) hq)
    exact hgain.ae_eq (hWae 0)

end PoincareConjecture
