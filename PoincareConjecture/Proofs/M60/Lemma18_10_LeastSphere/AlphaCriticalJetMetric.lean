import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalJetNormalization
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalMetricNormalization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Regularity.Metric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal Manifold

noncomputable section

namespace PoincareConjecture.M60

private abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)
private abbrev Grad (m : ℕ) := E m × E m
private abbrev Point (m : ℕ) := (LoopPlane × E m) × Grad m

local instance jetMetricBilinearNormedGroup {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

local instance jetMetricBilinearNormedSpace {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

def suAlphaMetricOperator {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (y : E n) : E n →L[ℝ] E n :=
  InnerProductSpace.continuousLinearMapOfBilin
    (g.pullbackCoefficients (chartAt (E n) b).symm y)

theorem suAlphaMetricOperator_isUnit {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (y : E n)
    (hy : y ∈ (extChartAt (𝓡 n) b).target) : IsUnit (suAlphaMetricOperator g b y) := by
  obtain ⟨kappa, _, hkappa, _, _, _, hmetric⟩ := suAlpha_coordinate_metric_bounds g b
    (K := {y}) isCompact_singleton (by simpa only [singleton_subset_iff] using hy)
  apply ReducedLengthMinimum.Variational.positive_form_operator_isUnit
  intro v hv
  exact (mul_pos hkappa (pow_pos (norm_pos_iff.mpr hv) 2)).trans_le
    (hmetric y (mem_singleton _) v)

theorem suAlphaMetricOperator_contDiffOn {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) :
    ContDiffOn ℝ ∞ (suAlphaMetricOperator g b) (extChartAt (𝓡 n) b).target := by
  unfold suAlphaMetricOperator InnerProductSpace.continuousLinearMapOfBilin
  exact contDiffOn_const.clm_comp (g.contDiffOn_chartCoefficients b)

def suAlphaPrincipalWeight {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (p : Point n) : ℝ :=
  let G := g.pullbackCoefficients (chartAt (E n) b).symm p.1.2
  2 * alpha * (1 + (G p.2.1 p.2.1 + G p.2.2 p.2.2) / suAlphaRoundFactor p.1.1) ^ (alpha - 1)

def suAlphaPrincipalNormalizer {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (p : Point n) : E n →L[ℝ] E n :=
  (suAlphaPrincipalWeight g b alpha p)⁻¹ • Ring.inverse (suAlphaMetricOperator g b p.1.2)

theorem suAlphaPrincipalWeight_pos_smooth {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) {alpha : ℝ} (ha : 1 ≤ alpha) (p : Point n)
    (hy : p.1.2 ∈ (extChartAt (𝓡 n) b).target) :
    0 < suAlphaPrincipalWeight g b alpha p ∧
      ContDiffAt ℝ ∞ (suAlphaPrincipalWeight g b alpha) p := by
  let G := g.pullbackCoefficients (chartAt (E n) b).symm
  obtain ⟨kappa, _, hkappa, _, _, _, hmetric⟩ := suAlpha_coordinate_metric_bounds g b
    (K := {p.1.2}) isCompact_singleton (by simpa only [singleton_subset_iff] using hy)
  have hnonneg (v : E n) : 0 ≤ G p.1.2 v v :=
    (mul_nonneg hkappa.le (sq_nonneg _)).trans (hmetric p.1.2 (mem_singleton _) v)
  have hlambda (x : LoopPlane) : 0 < suAlphaRoundFactor x := by
    unfold suAlphaRoundFactor
    positivity
  have hls : ContDiff ℝ ∞ suAlphaRoundFactor := by
    unfold suAlphaRoundFactor
    exact contDiff_const.div (((contDiff_norm_sq ℝ).add contDiff_const).pow 2)
      (fun x => by positivity)
  have hG := ((g.contDiffOn_chartCoefficients b).contDiffAt
    ((isOpen_extChartAt_target b).mem_nhds hy)).comp p contDiffAt_fst.snd
  have hQ : ContDiffAt ℝ ∞ (fun z : Point n =>
      G z.1.2 z.2.1 z.2.1 + G z.1.2 z.2.2 z.2.2) p :=
    ((hG.clm_apply contDiffAt_snd.fst).clm_apply contDiffAt_snd.fst).add
      ((hG.clm_apply contDiffAt_snd.snd).clm_apply contDiffAt_snd.snd)
  have hpos : 0 < 1 + (G p.1.2 p.2.1 p.2.1 + G p.1.2 p.2.2 p.2.2) /
      suAlphaRoundFactor p.1.1 := by
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (div_nonneg (add_nonneg (hnonneg _) (hnonneg _)) (hlambda _).le)
  refine ⟨?_, ?_⟩
  · unfold suAlphaPrincipalWeight
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos hpos _)
  · exact contDiffAt_const.mul
      ((contDiffAt_const.add (hQ.div (hls.contDiffAt.comp p contDiffAt_fst.fst)
        (hlambda _).ne')).rpow_const_of_ne hpos.ne')

theorem suAlphaPrincipalNormalizer_contDiffAt {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) {alpha : ℝ} (ha : 1 ≤ alpha) (p : Point n)
    (hy : p.1.2 ∈ (extChartAt (𝓡 n) b).target) :
    ContDiffAt ℝ ∞ (suAlphaPrincipalNormalizer g b alpha) p := by
  have hw := suAlphaPrincipalWeight_pos_smooth g b ha p hy
  have hi := ReducedLengthMinimum.Variational.contDiffOn_inverse_operator
    (suAlphaMetricOperator g b) (suAlphaMetricOperator_contDiffOn g b)
      (suAlphaMetricOperator_isUnit g b)
  exact (hw.2.inv hw.1.ne').smul ((hi.contDiffAt
    ((isOpen_extChartAt_target b).mem_nhds hy)).comp p contDiffAt_fst.snd)

theorem suAlphaMetricOperator_apply {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (y v : E n) (a : Fin n) :
    suAlphaMetricOperator g b y v a =
      g.pullbackCoefficients (chartAt (E n) b).symm y v (EuclideanSpace.single a 1) := by
  simpa only [suAlphaMetricOperator, EuclideanSpace.inner_single_right,
    starRingEnd_apply, star_trivial,
    one_mul] using InnerProductSpace.continuousLinearMapOfBilin_apply
      (g.pullbackCoefficients (chartAt (E n) b).symm y) v (EuclideanSpace.single a 1)

def suAlphaPrincipalTrace {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (p : Point n)
    (H : Fin 2 → Fin 2 → E n) : E n :=
  WithLp.toLp 2 fun a => ∑ i : Fin 2,
    fderiv ℝ (suAlphaCoordinateFlux g b alpha p.1) p.2
      (H 0 i, H 1 i) (suColumnBasis a i)

set_option maxHeartbeats 800000 in

theorem suAlphaPrincipalTrace_formula {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (p : Point n)
    (hy : p.1.2 ∈ (extChartAt (𝓡 n) b).target) (H : Fin 2 → Fin 2 → E n) :
    let G := g.pullbackCoefficients (chartAt (E n) b).symm p.1.2
    let v : Fin 2 → E n := fun i => if i = 0 then p.2.1 else p.2.2
    suAlphaPrincipalTrace g b alpha p H = suAlphaPrincipalWeight g b alpha p •
      suAlphaMetricOperator g b p.1.2
        ((∑ i : Fin 2, H i i) + (alpha - 1) •
          suAlphaHessianTerm G v H (suAlphaRoundFactor p.1.1 + ∑ i : Fin 2, G (v i) (v i))) := by
  let G := g.pullbackCoefficients (chartAt (E n) b).symm p.1.2
  let lambda := suAlphaRoundFactor p.1.1
  let Q := G p.2.1 p.2.1 + G p.2.2 p.2.2
  let a := 1 + Q / lambda
  obtain ⟨kappa, _, hkappa, _, _, _, hmetric⟩ := suAlpha_coordinate_metric_bounds g b
    (K := {p.1.2}) isCompact_singleton (by simpa only [singleton_subset_iff] using hy)
  have hl : 0 < lambda := by dsimp [lambda, suAlphaRoundFactor]; positivity
  have hQ : 0 ≤ Q := add_nonneg
    ((mul_nonneg hkappa.le (sq_nonneg _)).trans (hmetric _ (mem_singleton _) p.2.1))
    ((mul_nonneg hkappa.le (sq_nonneg _)).trans (hmetric _ (mem_singleton _) p.2.2))
  have ha : 0 < a := by dsimp [a]; positivity
  have hd : 0 < lambda + Q := add_pos_of_pos_of_nonneg hl hQ
  have hp : a ^ (alpha - 2) = a ^ (alpha - 1) / a := by
    rw [show alpha - 2 = (alpha - 1) - 1 by ring, Real.rpow_sub ha, Real.rpow_one]
  have hD := (suAlphaCoordinateFlux_gradientDerivative g b alpha p.1.1 p.1.2
    hkappa (hmetric _ (mem_singleton _)) p.2).fderiv
  ext c
  simp only [suAlphaPrincipalTrace, PiLp.smul_apply, smul_eq_mul, suAlphaMetricOperator_apply]
  simp only [Fin.sum_univ_two, Fin.isValue, ite_true, one_ne_zero, ite_false]
  rw [hD]
  simp only [suAlphaFluxLinearization, suAlphaPairMetric, suColumnBasis,
    smul_apply, add_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', map_zero, zero_add, add_zero,
    suAlphaHessianTerm, Fin.sum_univ_two, Fin.isValue, ite_true, one_ne_zero, ite_false,
    map_add, map_smul]
  rw [show 1 + lambda⁻¹ * Q = a by dsimp only [a]; ring]
  change _ = (2 * alpha * a ^ (alpha - 1)) * _
  change lambda * (2 * alpha * a ^ (alpha - 1) * (lambda⁻¹ * G (H 0 0) _) +
      (4 * alpha * (alpha - 1) * a ^ (alpha - 2) *
        (lambda⁻¹ * (G p.2.1 (H 0 0) + G p.2.2 (H 1 0)))) *
          (lambda⁻¹ * G p.2.1 _)) +
    lambda * (2 * alpha * a ^ (alpha - 1) * (lambda⁻¹ * G (H 1 1) _) +
      (4 * alpha * (alpha - 1) * a ^ (alpha - 2) *
        (lambda⁻¹ * (G p.2.1 (H 0 1) + G p.2.2 (H 1 1)))) *
          (lambda⁻¹ * G p.2.2 _)) = _
  rw [hp]
  dsimp only [a, Q, lambda, G] at hl hd ⊢
  field_simp [hl.ne', hd.ne']
  ring

theorem suAlphaPrincipalNormalizer_trace {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) {alpha : ℝ} (ha : 1 ≤ alpha) (p : Point n)
    (hy : p.1.2 ∈ (extChartAt (𝓡 n) b).target) (H : Fin 2 → Fin 2 → E n) :
    let G := g.pullbackCoefficients (chartAt (E n) b).symm p.1.2
    let v : Fin 2 → E n := fun i => if i = 0 then p.2.1 else p.2.2
    suAlphaPrincipalNormalizer g b alpha p (suAlphaPrincipalTrace g b alpha p H) =
      (∑ i : Fin 2, H i i) + (alpha - 1) •
        suAlphaHessianTerm G v H (suAlphaRoundFactor p.1.1 + ∑ i : Fin 2, G (v i) (v i)) := by
  rw [suAlphaPrincipalTrace_formula g b alpha p hy]
  simp only [suAlphaPrincipalNormalizer, smul_apply, map_smul, smul_smul]
  rw [mul_inv_cancel₀ (suAlphaPrincipalWeight_pos_smooth g b ha p hy).1.ne', one_smul]
  exact ReducedLengthMinimum.Variational.inverse_operator_apply _
    (suAlphaMetricOperator_isUnit g b p.1.2 hy) _

theorem suAlphaPrincipalNormalizer_residual {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) {alpha : ℝ} (ha : 1 ≤ alpha) (p : Point n)
    (hy : p.1.2 ∈ (extChartAt (𝓡 n) b).target) (L : E n ≃L[ℝ] E n)
    (hB : ‖(g.pullbackCoefficients (chartAt (E n) b).symm p.1.2).bilinearComp
      L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap‖ ≤ 2)
    (hc : ∀ w, (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤
      (g.pullbackCoefficients (chartAt (E n) b).symm p.1.2).bilinearComp
        L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap w w)
    (H : Fin 2 → Fin 2 → E n) :
    ‖L ((∑ i : Fin 2, H i i) -
      suAlphaPrincipalNormalizer g b alpha p (suAlphaPrincipalTrace g b alpha p H))‖ ≤
        (16 * (alpha - 1)) * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖L (H i j)‖ ^ 2) := by
  let G := g.pullbackCoefficients (chartAt (E n) b).symm p.1.2
  let v : Fin 2 → E n := fun i => if i = 0 then p.2.1 else p.2.2
  let Q := ∑ i : Fin 2, G (v i) (v i)
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => by
    have h := hc (L (v i))
    simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_apply,
      L.symm_apply_apply] at h
    exact (mul_nonneg (by norm_num) (sq_nonneg _)).trans h
  have hl : 0 < suAlphaRoundFactor p.1.1 := by unfold suAlphaRoundFactor; positivity
  have ht := suAlphaHessianTerm_transformed_bound G L v H
    (add_pos_of_pos_of_nonneg hl hQ) hB hc (le_add_of_nonneg_left hl.le)
  rw [suAlphaPrincipalNormalizer_trace g b ha p hy]
  simp only [sub_add_eq_sub_sub, sub_self, zero_sub, map_neg, norm_neg, map_smul,
    norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ha)]
  exact (mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr ha)).trans_eq (by ring)

theorem suAlphaFirstJet_principalTrace_block {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ)
    (z : LoopPlane × E (3 * n)) (H : Fin 2 → Fin 2 → E (3 * n)) (j : Fin 3) :
    suJetBlock j ((suAlphaFirstJetCoefficients g b alpha).principalTrace z H) =
      suAlphaPrincipalTrace g b alpha (suAlphaFirstJetPoint z)
        (fun i k => suJetBlock j (H i k)) := by
  classical
  ext a
  change (suAlphaFirstJetCoefficients g b alpha).principalTrace z H
    (finProdFinEquiv (j, a)) = _
  simp only [SUAffineJetCoefficients.principalTrace, suAlphaFirstJetCoefficients,
    suAlphaFirstJetPrincipal, suJetBlockPrincipal, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, suJetBlock_columnBasis]
  simp only [apply_ite, map_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rfl

def suAlphaFirstJetNormalization {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) {alpha delta : ℝ} (ha : 1 ≤ alpha)
    (hdelta : 16 * (alpha - 1) ≤ delta) (O : Set (LoopPlane × E (3 * n)))
    (L : E n ≃L[ℝ] E n)
    (hy : ∀ z ∈ O, suJetBlock (0 : Fin 3) z.2 ∈ (extChartAt (𝓡 n) b).target)
    (hmetric : ∀ z ∈ O,
      ‖(g.pullbackCoefficients (chartAt (E n) b).symm (suJetBlock (0 : Fin 3) z.2)).bilinearComp
        L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap‖ ≤ 2 ∧
      ∀ v, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
        (g.pullbackCoefficients (chartAt (E n) b).symm (suJetBlock (0 : Fin 3) z.2)).bilinearComp
          L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap v v) :
    SUAffineJetNormalization (suAlphaFirstJetCoefficients g b alpha) O delta where
  targetChange := suJetBlockDiagonalEquiv L
  normalizer z := suJetBlockDiagonal
    (suAlphaPrincipalNormalizer g b alpha (suAlphaFirstJetPoint z))
  normalizer_smooth := by
    intro z hz
    exact (suJetBlockDiagonalL.contDiff.contDiffAt.comp z
      ((suAlphaPrincipalNormalizer_contDiffAt g b ha _ (hy z hz)).comp z
        suAlphaFirstJetPoint_contDiff.contDiffAt)).contDiffWithinAt
  residual_bound := by
    intro z hz H
    let p := suAlphaFirstJetPoint z
    let T := suJetBlockDiagonalEquiv (k := 3) L
    let D := suJetBlockDiagonal (k := 3) (suAlphaPrincipalNormalizer g b alpha p)
    let R := (∑ i : Fin 2, H i i) - D ((suAlphaFirstJetCoefficients g b alpha).principalTrace z H)
    have hb (j : Fin 3) : suJetBlock j (T R) =
        L ((∑ i : Fin 2, suJetBlock j (H i i)) -
          suAlphaPrincipalNormalizer g b alpha p
            (suAlphaPrincipalTrace g b alpha p (fun i k => suJetBlock j (H i k)))) := by
      rw [suJetBlock_diagonalEquiv]
      dsimp only [R, D]
      rw [map_sub, map_sum, suJetBlock_diagonal, suAlphaFirstJet_principalTrace_block]
    have hs (j : Fin 3) : ‖suJetBlock j (T R)‖ ^ 2 ≤
        delta ^ 2 * ∑ i : Fin 2, ∑ k : Fin 2, ‖L (suJetBlock j (H i k))‖ ^ 2 := by
      rw [hb]
      have h := (suAlphaPrincipalNormalizer_residual g b ha p (hy z hz) L
        (hmetric z hz).1 (hmetric z hz).2 (fun i k => suJetBlock j (H i k))).trans
          (mul_le_mul_of_nonneg_right hdelta (Real.sqrt_nonneg _))
      have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
      rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun k _ => sq_nonneg _)] at hh
      exact hh
    have hblocks (i k : Fin 2) :
        (∑ j : Fin 3, ‖L (suJetBlock j (H i k))‖ ^ 2) = ‖T (H i k)‖ ^ 2 := by
      simpa only [T, suJetBlock_diagonalEquiv] using suJetBlock_norm_sq (T (H i k))
    have hsum : ‖T R‖ ^ 2 ≤
        delta ^ 2 * ∑ i : Fin 2, ∑ k : Fin 2, ‖T (H i k)‖ ^ 2 := by
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hs j)
      rw [suJetBlock_norm_sq, ← Finset.mul_sum] at hh
      have he : (∑ j : Fin 3, ∑ i : Fin 2, ∑ k : Fin 2,
          ‖L (suJetBlock j (H i k))‖ ^ 2) =
          ∑ i : Fin 2, ∑ k : Fin 2, ‖T (H i k)‖ ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        simp only [hblocks]
      rwa [he] at hh
    have hd : 0 ≤ delta := (mul_nonneg (by norm_num) (sub_nonneg.mpr ha)).trans hdelta
    have hsqrt := Real.sq_sqrt (show 0 ≤ ∑ i : Fin 2, ∑ k : Fin 2,
        ‖T (H i k)‖ ^ 2 from Finset.sum_nonneg fun i _ =>
          Finset.sum_nonneg fun k _ => sq_nonneg _)
    have hright : 0 ≤ delta * Real.sqrt (∑ i : Fin 2, ∑ k : Fin 2, ‖T (H i k)‖ ^ 2) :=
      mul_nonneg hd (Real.sqrt_nonneg _)
    change ‖T R‖ ≤ delta * Real.sqrt (∑ i : Fin 2, ∑ k : Fin 2, ‖T (H i k)‖ ^ 2)
    nlinarith [norm_nonneg (T R)]

theorem suAlphaFirstJet_normalization {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) {alpha delta : ℝ} (ha : 1 ≤ alpha)
    (hdelta : 16 * (alpha - 1) ≤ delta) (z : LoopPlane × E (3 * n))
    (hz : suJetBlock (0 : Fin 3) z.2 ∈ (extChartAt (𝓡 n) b).target) :
    let C := suAlphaFirstJetCoefficients g b alpha
    ∃ O : Set (LoopPlane × E (3 * n)), IsOpen O ∧ z ∈ O ∧
      O ⊆ {w | suJetBlock (0 : Fin 3) w.2 ∈ (extChartAt (𝓡 n) b).target} ∧
      ContDiffOn ℝ ∞ C.principal O ∧ ContDiffOn ℝ ∞ C.fluxOffset O ∧
      ContDiffOn ℝ ∞ C.sourceLinear O ∧ ContDiffOn ℝ ∞ C.sourceOffset O ∧
      ∃ nu : ℝ, 0 < nu ∧ (∀ w ∈ O, ∀ q : Grad (3 * n), nu * ‖q‖ ^ 2 ≤ C.principal w q q) ∧
        Nonempty (SUAffineJetNormalization C O delta) := by
  let y := suJetBlock (0 : Fin 3) z.2
  let G := g.pullbackCoefficients (chartAt (E n) b).symm
  have hG : ContinuousAt G y := ((g.contDiffOn_chartCoefficients b).contDiffAt
    ((isOpen_extChartAt_target b).mem_nhds hz)).continuousAt
  obtain ⟨k0, _, hk0, _, _, _, hG0⟩ := suAlpha_coordinate_metric_bounds g b
    (K := {y}) isCompact_singleton (by simpa only [singleton_subset_iff] using hz)
  have hp (v : E n) (hv : v ≠ 0) : 0 < G y v v :=
    (mul_pos hk0 (pow_pos (norm_pos_iff.mpr hv) 2)).trans_le (hG0 y (mem_singleton _) v)
  obtain ⟨L, _, hL⟩ := suContinuousMetric_local_normalization G y hG
    (fun v w => g.symm _ _ _) hp
  have hnhds : {w | w ∈ (extChartAt (𝓡 n) b).target ∧
      ‖(G w).bilinearComp L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap‖ ≤ 2 ∧
      ∀ v, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
        (G w).bilinearComp L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap v v} ∈ 𝓝 y :=
    inter_mem ((isOpen_extChartAt_target b).mem_nhds hz) hL
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hsmall : closedBall y (r / 2) ⊆ ball y r := closedBall_subset_ball (half_lt_self hr)
  have hchart : closedBall y (r / 2) ⊆ (extChartAt (𝓡 n) b).target :=
    fun w hw => (hball (hsmall hw)).1
  obtain ⟨kappa, _, hkappa, _, _, _, hmetric⟩ := suAlpha_coordinate_metric_bounds g b
    (isCompact_closedBall y (r / 2)) hchart
  let O : Set (LoopPlane × E (3 * n)) := {w | suJetBlock (0 : Fin 3) w.2 ∈ ball y (r / 2)}
  have hO : IsOpen O := isOpen_ball.preimage
    ((suJetBlock (0 : Fin 3)).continuous.comp continuous_snd)
  have htarget (w : LoopPlane × E (3 * n)) (hw : w ∈ O) :
      suJetBlock (0 : Fin 3) w.2 ∈ (extChartAt (𝓡 n) b).target :=
    hchart (ball_subset_closedBall hw)
  have hsmooth (w : LoopPlane × E (3 * n)) (hw : w ∈ O) :=
    suAlphaFirstJet_coefficients_contDiffAt g b alpha w (htarget w hw)
  refine ⟨O, hO, mem_ball_self (half_pos hr), htarget, ?_, ?_, ?_, ?_,
    2 * kappa, by positivity, ?_, ?_⟩
  · exact fun w hw => (hsmooth w hw).1.contDiffWithinAt
  · exact fun w hw => (hsmooth w hw).2.1.contDiffWithinAt
  · exact fun w hw => (hsmooth w hw).2.2.1.contDiffWithinAt
  · exact fun w hw => (hsmooth w hw).2.2.2.contDiffWithinAt
  · intro w hw q
    apply suJetBlockPrincipal_coercive (by positivity : 0 ≤ 2 * kappa)
    exact fun v => suAlphaCoordinateFlux_principal_coercive g b ha w.1
      (suJetBlock (0 : Fin 3) w.2) hkappa
        (hmetric _ (ball_subset_closedBall hw)) _ v
  · exact ⟨suAlphaFirstJetNormalization g b ha hdelta O L htarget
      (fun w hw => (hball (hsmall (ball_subset_closedBall hw))).2)⟩

end PoincareConjecture.M60
