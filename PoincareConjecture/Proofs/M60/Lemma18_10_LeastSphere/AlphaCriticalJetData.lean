import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalBootstrap
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalQuadratic
import PoincareConjecture.Proofs.M60.Mathlib.SecondDerivativeChain
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Iteration.TestCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped ContDiff Topology ENNReal Manifold
open Poincare.Analysis.Sobolev.Weak

noncomputable section

namespace PoincareConjecture.M60

theorem suWeakDivergence_prolong
    {O : Set LoopPlane} {F DF : Fin 2 → LoopPlane → ℝ}
    {b Db : LoopPlane → ℝ} (k : Fin 2)
    (hF : ∀ i, IntegrableOn (F i) O) (hDF : ∀ i, IntegrableOn (DF i) O)
    (hwF : ∀ i, HasWeakPartialDeriv k (DF i) (F i) O)
    (hwb : HasWeakPartialDeriv k Db b O)
    (heq : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O →
      (∫ x in O, ∑ i : Fin 2, F i x * fderiv ℝ phi x (EuclideanSpace.single i 1)) =
        ∫ x in O, b x * phi x)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ O) :
    (∫ x in O, ∑ i : Fin 2, DF i x * fderiv ℝ phi x (EuclideanSpace.single i 1)) =
      ∫ x in O, Db x * phi x := by
  let dphi (i : Fin 2) (x : LoopPlane) := fderiv ℝ phi x (EuclideanSpace.single i 1)
  have hd (i : Fin 2) : ContDiff ℝ ∞ (dphi i) :=
    (hp.fderiv_right (by simp)).clm_apply contDiff_const
  have hdc (i : Fin 2) : HasCompactSupport (dphi i) := hc.fderiv_apply ℝ _
  have hds (i : Fin 2) : tsupport (dphi i) ⊆ O :=
    (tsupport_fderiv_apply_subset ℝ _).trans hs
  have hcomm (i : Fin 2) (x : LoopPlane) :
      fderiv ℝ (dphi i) x (EuclideanSpace.single k 1) =
        fderiv ℝ (dphi k) x (EuclideanSpace.single i 1) := by
    have hp2 : ContDiffAt ℝ 2 phi x := hp.contDiffAt.of_le (by decide)
    dsimp only [dphi]
    rw [fderiv_column hp2, fderiv_column hp2]
    exact (hp2.isSymmSndFDerivAt (by simp)).eq _ _
  have hI (A : LoopPlane → ℝ) (hA : IntegrableOn A O volume)
      (psi : LoopPlane → ℝ) (hpsi : ContDiff ℝ ∞ psi) (hpsic : HasCompactSupport psi) :
      IntegrableOn (fun x => A x * psi x) O volume :=
    memLp_one_iff_integrable.mp
      (((hpsi.continuous.memLp_of_hasCompactSupport hpsic : MemLp psi ⊤ volume).restrict O).mul'
        (memLp_one_iff_integrable.mpr hA))
  have hI1 (i : Fin 2) := hI (DF i) (hDF i) (dphi i) (hd i) (hdc i)
  have hI2 (i : Fin 2) := hI (F i) (hF i)
    (fun x => fderiv ℝ (dphi k) x (EuclideanSpace.single i 1))
    (((hd k).fderiv_right (by simp)).clm_apply contDiff_const) ((hdc k).fderiv_apply ℝ _)
  have hparts (i : Fin 2) : (∫ x in O, DF i x * dphi i x) =
      -(∫ x in O, F i x * fderiv ℝ (dphi k) x (EuclideanSpace.single i 1)) := by
    have he := hwF i (dphi i) (hd i) (hdc i) (hds i)
    simp_rw [hcomm i] at he
    linarith only [he]
  calc
    _ = ∑ i : Fin 2, ∫ x in O, DF i x * dphi i x :=
      integral_finsetSum _ (fun i _ => hI1 i)
    _ = -(∑ i : Fin 2, ∫ x in O, F i x *
        fderiv ℝ (dphi k) x (EuclideanSpace.single i 1)) := by
      simp_rw [hparts]
      exact Finset.sum_neg_distrib _
    _ = -(∫ x in O, ∑ i : Fin 2, F i x *
        fderiv ℝ (dphi k) x (EuclideanSpace.single i 1)) := by
      rw [integral_finsetSum _ (fun i _ => hI2 i)]
    _ = -(∫ x in O, b x * dphi k x) := by rw [heq _ (hd k) (hdc k) (hds k)]
    _ = _ := by rw [hwb phi hp hc hs, neg_neg]

def suFirstJet {m : ℕ} (u : LoopPlane → EuclideanSpace ℝ (Fin m))
    (x : LoopPlane) : EuclideanSpace ℝ (Fin (3 * m)) :=
  WithLp.toLp 2 fun a =>
    let j := (finProdFinEquiv : Fin 3 × Fin m ≃ Fin (3 * m)).symm a
    Fin.cases (u x j.2)
      (fun i : Fin 2 => fderiv ℝ u x (EuclideanSpace.single i 1) j.2) j.1

def suFirstJetWeakColumn {m : ℕ}
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m))
    (H : Fin 2 → Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m))
    (i : Fin 2) (x : LoopPlane) : EuclideanSpace ℝ (Fin (3 * m)) :=
  WithLp.toLp 2 fun a =>
    let j := (finProdFinEquiv : Fin 3 × Fin m ≃ Fin (3 * m)).symm a
    Fin.cases (V i x j.2) (fun l : Fin 2 => H l i x j.2) j.1

theorem suFirstJet_weak_data {m : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)} {center : LoopPlane} {R : ℝ}
    (G : SUInitialGain u V center R) (H : SUC1HolderGain u V center G.radius) :
    let r := H.radius / 2
    ContinuousOn (suFirstJet u) (Metric.closedBall center r) ∧
    MemLp (suFirstJet u) 2 (volume.restrict (Metric.ball center r)) ∧
    (∀ i, MemLp (suFirstJetWeakColumn V G.hessian i) 2
      (volume.restrict (Metric.ball center r))) ∧
    ∀ (i : Fin 2) (a : Fin (3 * m)),
      HasWeakPartialDeriv i (fun x => suFirstJetWeakColumn V G.hessian i x a)
        (fun x => suFirstJet u x a) (Metric.ball center r) := by
  classical
  let r := H.radius / 2
  have hr : 0 < r := half_pos H.radius_pos
  have hrH : r < H.radius := half_lt_self H.radius_pos
  have hrG : r < G.radius := hrH.trans H.radius_lt
  have hsubH : Metric.ball center r ⊆ Metric.ball center H.radius :=
    Metric.ball_subset_ball hrH.le
  have hsubG : Metric.ball center r ⊆ Metric.ball center G.radius :=
    Metric.ball_subset_ball hrG.le
  have hcsub : Metric.closedBall center r ⊆ Metric.ball center H.radius :=
    Metric.closedBall_subset_ball hrH
  have huc := H.coordinate_contDiff.continuousOn.mono hcsub
  have hdc := (H.coordinate_contDiff.continuousOn_fderiv_of_isOpen isOpen_ball
    (by norm_num)).mono hcsub
  have hjet : ContinuousOn (suFirstJet u) (Metric.closedBall center r) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (3 * m) => ℝ)).comp_continuousOn
    apply continuousOn_pi.mpr
    intro a
    obtain ⟨⟨j, c⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin m ≃ Fin (3 * m)).surjective a
    simp only [Equiv.symm_apply_apply]
    cases j using Fin.cases with
    | zero =>
      exact (EuclideanSpace.proj c).continuous.comp_continuousOn huc
    | succ l =>
      exact (EuclideanSpace.proj c).continuous.comp_continuousOn
        (hdc.clm_apply continuousOn_const)
  have hLp : MemLp (suFirstJet u) 2 (volume.restrict (Metric.ball center r)) := by
    let : IsFiniteMeasure (volume.restrict (Metric.ball center r)) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact measure_ball_lt_top⟩
    obtain ⟨C, hC⟩ := (isCompact_closedBall center r).exists_bound_of_continuousOn hjet
    exact MemLp.of_bound
      ((hjet.mono Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball) C
      ((ae_restrict_mem measurableSet_ball).mono fun x hx =>
        hC x (Metric.ball_subset_closedBall hx))
  have hcols (i : Fin 2) : MemLp (suFirstJetWeakColumn V G.hessian i) 2
      (volume.restrict (Metric.ball center r)) := by
    apply MemLp.of_eval_piLp
    intro a
    obtain ⟨⟨j, c⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin m ≃ Fin (3 * m)).surjective a
    dsimp only [suFirstJetWeakColumn]
    simp only [Equiv.symm_apply_apply]
    cases j using Fin.cases with
    | zero =>
      exact ((show MemLp (V i) 2 (volume.restrict (Metric.ball center G.radius)) by
        simpa only [ENNReal.ofReal_ofNat] using G.column_memLp 2 (by norm_num) i
        ).eval_piLp c).mono_measure (Measure.restrict_mono hsubG le_rfl)
    | succ l =>
      exact ((G.hessian_memLp l i).eval_piLp c).mono_measure
        (Measure.restrict_mono hsubG le_rfl)
  refine ⟨hjet, hLp, hcols, ?_⟩
  intro i a
  obtain ⟨⟨j, c⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin m ≃ Fin (3 * m)).surjective a
  dsimp only [suFirstJet, suFirstJetWeakColumn]
  simp only [Equiv.symm_apply_apply]
  cases j using Fin.cases with
  | zero => exact (G.weak_derivative i c).restrict isOpen_ball hsubG
  | succ l =>
    have hae := (H.column_ae l).filter_mono (ae_mono
      (Measure.restrict_mono hsubH le_rfl))
    intro phi hp hc hs
    have he := (G.second_weak_derivative l i c).restrict isOpen_ball hsubG phi hp hc hs
    calc
      _ = ∫ x in Metric.ball center r, V l x c *
          fderiv ℝ phi x (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        filter_upwards [hae] with x hx
        change (fderiv ℝ u x (EuclideanSpace.single l 1)) c * _ = _
        rw [hx]
      _ = _ := he

set_option maxHeartbeats 800000 in

theorem suAlphaCoordinateFlux_gradientDerivative
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ)
    (x : LoopPlane) (y : EuclideanSpace ℝ (Fin n))
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hG : ∀ v : EuclideanSpace ℝ (Fin n), kappa * ‖v‖ ^ 2 ≤
      g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm y v v)
    (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    let B := (suAlphaRoundFactor x)⁻¹ • suAlphaPairMetric
      (g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm y)
    HasFDerivAt (suAlphaCoordinateFlux g b alpha (x, y))
      (suAlphaRoundFactor x • suAlphaFluxLinearization B 1 alpha q) q := by
  let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm y
  let B := (suAlphaRoundFactor x)⁻¹ • suAlphaPairMetric G
  have hlambda : 0 < suAlphaRoundFactor x := by dsimp [suAlphaRoundFactor]; positivity
  have hpos (v : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : 0 ≤ B v v := by
    have he := suAlphaPairMetric_coercive G hkappa.le hG v
    change 0 ≤ (suAlphaRoundFactor x)⁻¹ * suAlphaPairMetric G v v
    exact mul_nonneg (inv_nonneg.mpr hlambda.le)
      ((mul_nonneg hkappa.le (sq_nonneg _)).trans he)
  have hsymm (v w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
      B v w = B w v := by
    change (suAlphaRoundFactor x)⁻¹ * (G v.1 w.1 + G v.2 w.2) =
      (suAlphaRoundFactor x)⁻¹ * (G w.1 v.1 + G w.2 v.2)
    congr 1
    exact congrArg₂ (fun a b : ℝ => a + b) (g.symm _ _ _) (g.symm _ _ _)
  exact (suAlphaFluxLinearization_hasFDerivAt B hpos hsymm
    (by norm_num) alpha q).const_smul (suAlphaRoundFactor x)

set_option maxHeartbeats 800000 in

theorem suAlphaCoordinateFlux_principal_coercive
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) {alpha : ℝ} (ha : 1 ≤ alpha)
    (x : LoopPlane) (y : EuclideanSpace ℝ (Fin n))
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hG : ∀ v : EuclideanSpace ℝ (Fin n), kappa * ‖v‖ ^ 2 ≤
      g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm y v v)
    (q v : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    2 * kappa * ‖v‖ ^ 2 ≤
      fderiv ℝ (suAlphaCoordinateFlux g b alpha (x, y)) q v v := by
  let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm y
  let B := (suAlphaRoundFactor x)⁻¹ • suAlphaPairMetric G
  have hlambda : 0 < suAlphaRoundFactor x := by dsimp [suAlphaRoundFactor]; positivity
  have hpair (w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    suAlphaPairMetric_coercive G hkappa.le hG w
  have hpos (w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : 0 ≤ B w w :=
    mul_nonneg (inv_nonneg.mpr hlambda.le)
      ((mul_nonneg hkappa.le (sq_nonneg _)).trans (hpair w))
  have hw : 1 ≤ (1 + B q q) ^ (alpha - 1) :=
    Real.one_le_rpow (by linarith [hpos q]) (by linarith)
  have hweight : 2 ≤ 2 * alpha * (1 + B q q) ^ (alpha - 1) := by
    nlinarith
  have hlo := suAlphaFluxLinearization_lower B hpos (show (0 : ℝ) ≤ 1 by norm_num) ha q v
  have hp := mul_le_mul_of_nonneg_right hweight (hpos v)
  rw [(suAlphaCoordinateFlux_gradientDerivative g b alpha x y hkappa hG q).fderiv]
  change 2 * kappa * ‖v‖ ^ 2 ≤ suAlphaRoundFactor x * suAlphaFluxLinearization B 1 alpha q v v
  have he : suAlphaRoundFactor x * (2 * B v v) = 2 * suAlphaPairMetric G v v := by
    change suAlphaRoundFactor x * (2 * ((suAlphaRoundFactor x)⁻¹ *
      suAlphaPairMetric G v v)) = _
    field_simp [hlambda.ne']
  calc
    _ ≤ 2 * suAlphaPairMetric G v v := by linarith [hpair v]
    _ = suAlphaRoundFactor x * (2 * B v v) := he.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hp.trans hlo) hlambda.le

theorem SUInitialGain.hessian_symm_ae {m : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)} {center : LoopPlane} {R : ℝ}
    (G : SUInitialGain u V center R) (i j : Fin 2) :
    G.hessian i j =ᵐ[volume.restrict (Metric.ball center G.radius)] G.hessian j i := by
  have he (a : Fin m) := Poincare.Analysis.Elliptic.Iteration.weakPartial_comm_ae isOpen_ball
    (G.weak_derivative i a) (G.weak_derivative j a)
    (G.second_weak_derivative i j a) (G.second_weak_derivative j i a)
    (((G.hessian_memLp i j).eval_piLp a).locallyIntegrable (by norm_num))
    (((G.hessian_memLp j i).eval_piLp a).locallyIntegrable (by norm_num))
  filter_upwards [ae_all_iff.mpr he] with x hx
  ext a
  exact hx a

def suJetBlock {k m : ℕ} (j : Fin k) :
    EuclideanSpace ℝ (Fin (k * m)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => WithLp.toLp 2 fun a => v (finProdFinEquiv (j, a))
    map_add' := by intro v w; ext a; rfl
    map_smul' := by intro c v; ext a; rfl
  }

def suJetBlockPrincipal {k m : ℕ}
    (C : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) :
    (EuclideanSpace ℝ (Fin (k * m)) × EuclideanSpace ℝ (Fin (k * m))) →L[ℝ]
      (EuclideanSpace ℝ (Fin (k * m)) × EuclideanSpace ℝ (Fin (k * m))) →L[ℝ] ℝ :=
  ∑ j : Fin k, C.bilinearComp ((suJetBlock j).prodMap (suJetBlock j))
    ((suJetBlock j).prodMap (suJetBlock j))

theorem suJetBlock_norm_sq {k m : ℕ} (v : EuclideanSpace ℝ (Fin (k * m))) :
    (∑ j : Fin k, ‖suJetBlock j v‖ ^ 2) = ‖v‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  change (∑ j : Fin k, ∑ a : Fin m, (v (finProdFinEquiv (j, a))) ^ 2) = ∑ a, v a ^ 2
  have he := (finProdFinEquiv : Fin k × Fin m ≃ Fin (k * m)).sum_comp (fun a => v a ^ 2)
  rw [Fintype.sum_prod_type] at he
  exact he

theorem suJetBlockPrincipal_coercive {k m : ℕ}
    {C : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ}
    {nu : ℝ} (hnu : 0 ≤ nu)
    (hC : ∀ q, nu * ‖q‖ ^ 2 ≤ C q q)
    (q : EuclideanSpace ℝ (Fin (k * m)) × EuclideanSpace ℝ (Fin (k * m))) :
    nu * ‖q‖ ^ 2 ≤ suJetBlockPrincipal C q q := by
  have he := Finset.sum_le_sum (s := Finset.univ) fun j (_ : j ∈ Finset.univ) =>
    hC (suJetBlock j q.1, suJetBlock j q.2)
  have hsq (v w : EuclideanSpace ℝ (Fin m)) :
      ‖v‖ ^ 2 ≤ ‖(v, w)‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ ‖(v, w)‖ ^ 2 := by
    rw [Prod.norm_def]
    exact ⟨pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) 2,
      pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) 2⟩
  have h0 := Finset.sum_le_sum (s := Finset.univ) fun j (_ : j ∈ Finset.univ) =>
    (hsq (suJetBlock j q.1) (suJetBlock j q.2)).1
  have h1 := Finset.sum_le_sum (s := Finset.univ) fun j (_ : j ∈ Finset.univ) =>
    (hsq (suJetBlock j q.1) (suJetBlock j q.2)).2
  rw [suJetBlock_norm_sq] at h0 h1
  have hq : ‖q‖ ^ 2 ≤ ∑ j : Fin k, ‖(suJetBlock j q.1, suJetBlock j q.2)‖ ^ 2 := by
    rw [Prod.norm_def]
    rcases le_total ‖q.1‖ ‖q.2‖ with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  have hb := mul_le_mul_of_nonneg_left hq hnu
  rw [Finset.mul_sum] at hb
  apply (hb.trans he).trans_eq
  simp only [suJetBlockPrincipal, sum_apply, ContinuousLinearMap.bilinearComp_apply]
  rfl

local instance affineJetPrincipalNormedGroup {m : ℕ} : NormedAddCommGroup
    ((EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance affineJetPrincipalNormedSpace {m : ℕ} : NormedSpace ℝ
    ((EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance affineJetSourceNormedGroup {m : ℕ} : NormedAddCommGroup
    ((EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance affineJetSourceNormedSpace {m : ℕ} : NormedSpace ℝ
    ((EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

structure SUAffineJetCoefficients (m : ℕ) where
  principal : (LoopPlane × EuclideanSpace ℝ (Fin m)) →
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ
  fluxOffset : (LoopPlane × EuclideanSpace ℝ (Fin m)) →
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ
  sourceLinear : (LoopPlane × EuclideanSpace ℝ (Fin m)) →
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ
  sourceOffset : (LoopPlane × EuclideanSpace ℝ (Fin m)) →
    EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ

namespace SUAffineJetCoefficients

variable {m : ℕ}

def flux (C : SUAffineJetCoefficients m)
    (z : LoopPlane × EuclideanSpace ℝ (Fin m))
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :=
  C.principal z q + C.fluxOffset z

def source (C : SUAffineJetCoefficients m)
    (z : LoopPlane × EuclideanSpace ℝ (Fin m))
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :=
  C.sourceLinear z q + C.sourceOffset z

def prolong (C : SUAffineJetCoefficients m) : SUAffineJetCoefficients (3 * m) where
  principal z := suJetBlockPrincipal (k := 3)
    (C.principal (z.1, suJetBlock (0 : Fin 3) z.2))
  fluxOffset z :=
    let p := (z.1, suJetBlock (0 : Fin 3) z.2)
    let q := (suJetBlock (1 : Fin 3) z.2, suJetBlock (2 : Fin 3) z.2)
    (C.fluxOffset p).comp ((suJetBlock (0 : Fin 3)).prodMap (suJetBlock (0 : Fin 3))) +
      ∑ k : Fin 2, ((fderiv ℝ C.principal p
        (EuclideanSpace.single k 1, suJetBlock k.succ z.2)) q +
          fderiv ℝ C.fluxOffset p (EuclideanSpace.single k 1, suJetBlock k.succ z.2)).comp
            ((suJetBlock k.succ).prodMap (suJetBlock k.succ))
  sourceLinear z :=
    let p := (z.1, suJetBlock (0 : Fin 3) z.2)
    ∑ j : Fin 3,
      ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin (3 * m)))
        (EuclideanSpace ℝ (Fin m)) ℝ).flip (suJetBlock j)).comp
          ((C.sourceLinear p).comp ((suJetBlock j).prodMap (suJetBlock j)))
  sourceOffset z :=
    let p := (z.1, suJetBlock (0 : Fin 3) z.2)
    let q := (suJetBlock (1 : Fin 3) z.2, suJetBlock (2 : Fin 3) z.2)
    (C.sourceOffset p).comp (suJetBlock (0 : Fin 3)) +
      ∑ k : Fin 2, ((fderiv ℝ C.sourceLinear p
        (EuclideanSpace.single k 1, suJetBlock k.succ z.2)) q +
          fderiv ℝ C.sourceOffset p (EuclideanSpace.single k 1, suJetBlock k.succ z.2)).comp
            (suJetBlock k.succ)

theorem prolong_coercive (C : SUAffineJetCoefficients m)
    (z : LoopPlane × EuclideanSpace ℝ (Fin (3 * m))) {nu : ℝ} (hnu : 0 ≤ nu)
    (hC : ∀ q, nu * ‖q‖ ^ 2 ≤ C.principal (z.1, suJetBlock (0 : Fin 3) z.2) q q)
    (q : EuclideanSpace ℝ (Fin (3 * m)) × EuclideanSpace ℝ (Fin (3 * m))) :
    nu * ‖q‖ ^ 2 ≤ C.prolong.principal z q q :=
  suJetBlockPrincipal_coercive hnu hC q

theorem flux_fderiv (C : SUAffineJetCoefficients m)
    (z : LoopPlane × EuclideanSpace ℝ (Fin m))
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (hA : DifferentiableAt ℝ C.principal z) (hc : DifferentiableAt ℝ C.fluxOffset z)
    (v : LoopPlane × EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (fun p => C.flux p.1 p.2) (z, q) (v, w) =
      C.principal z w + fderiv ℝ C.principal z v q + fderiv ℝ C.fluxOffset z v := by
  have h1 : HasFDerivAt (fun p => C.principal p.1)
      ((fderiv ℝ C.principal z).comp (ContinuousLinearMap.fst ℝ
        (LoopPlane × EuclideanSpace ℝ (Fin m))
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)))) (z, q) :=
    hA.hasFDerivAt.comp (z, q) hasFDerivAt_fst
  have h2 : HasFDerivAt (fun p => C.fluxOffset p.1)
      ((fderiv ℝ C.fluxOffset z).comp (ContinuousLinearMap.fst ℝ
        (LoopPlane × EuclideanSpace ℝ (Fin m))
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)))) (z, q) :=
    hc.hasFDerivAt.comp (z, q) hasFDerivAt_fst
  have he := ((h1.clm_apply (hasFDerivAt_snd (𝕜 := ℝ) (p := (z, q)))).add h2).fderiv
  rw [show fderiv ℝ (fun p => C.flux p.1 p.2) (z, q) = _ from he]
  rfl

theorem source_fderiv (C : SUAffineJetCoefficients m)
    (z : LoopPlane × EuclideanSpace ℝ (Fin m))
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (hB : DifferentiableAt ℝ C.sourceLinear z) (hd : DifferentiableAt ℝ C.sourceOffset z)
    (v : LoopPlane × EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (fun p => C.source p.1 p.2) (z, q) (v, w) =
      C.sourceLinear z w + fderiv ℝ C.sourceLinear z v q + fderiv ℝ C.sourceOffset z v := by
  have h1 : HasFDerivAt (fun p => C.sourceLinear p.1)
      ((fderiv ℝ C.sourceLinear z).comp (ContinuousLinearMap.fst ℝ
        (LoopPlane × EuclideanSpace ℝ (Fin m))
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)))) (z, q) :=
    hB.hasFDerivAt.comp (z, q) hasFDerivAt_fst
  have h2 : HasFDerivAt (fun p => C.sourceOffset p.1)
      ((fderiv ℝ C.sourceOffset z).comp (ContinuousLinearMap.fst ℝ
        (LoopPlane × EuclideanSpace ℝ (Fin m))
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)))) (z, q) :=
    hd.hasFDerivAt.comp (z, q) hasFDerivAt_fst
  have he := ((h1.clm_apply (hasFDerivAt_snd (𝕜 := ℝ) (p := (z, q)))).add h2).fderiv
  rw [show fderiv ℝ (fun p => C.source p.1 p.2) (z, q) = _ from he]
  rfl

end SUAffineJetCoefficients

def SUAffineJetCoefficients.principalTrace {m : ℕ} (C : SUAffineJetCoefficients m)
    (z : LoopPlane × EuclideanSpace ℝ (Fin m))
    (H : Fin 2 → Fin 2 → EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun a => ∑ i : Fin 2,
    C.principal z (H 0 i, H 1 i) (suColumnBasis a i)

def SUAffineJetCoefficients.lowerTrace {m : ℕ} (C : SUAffineJetCoefficients m)
    (z : LoopPlane × EuclideanSpace ℝ (Fin m)) (q : Fin 2 → EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun a => C.source z (q 0, q 1) (EuclideanSpace.single a 1) +
    ∑ i : Fin 2, (fderiv ℝ C.principal z (EuclideanSpace.single i 1, q i) (q 0, q 1) +
      fderiv ℝ C.fluxOffset z (EuclideanSpace.single i 1, q i)) (suColumnBasis a i)

structure SUAffineJetNormalization {m : ℕ} (C : SUAffineJetCoefficients m)
    (O : Set (LoopPlane × EuclideanSpace ℝ (Fin m))) (delta : ℝ) where
  targetChange : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)
  normalizer : (LoopPlane × EuclideanSpace ℝ (Fin m)) →
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)
  normalizer_smooth : ContDiffOn ℝ ∞ normalizer O
  residual_bound : ∀ z ∈ O, ∀ H : Fin 2 → Fin 2 → EuclideanSpace ℝ (Fin m),
    ‖targetChange ((∑ i : Fin 2, H i i) - normalizer z (C.principalTrace z H))‖ ≤
      delta * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖targetChange (H i j)‖ ^ 2)

end PoincareConjecture.M60
