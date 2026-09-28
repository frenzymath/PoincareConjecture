import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalGrowthNormalized










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal
open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak

noncomputable section

namespace PoincareConjecture.M60

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup ((E × E) →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ ((E × E) →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup ((E × E) →L[ℝ] (E × E) →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ ((E × E) →L[ℝ] (E × E) →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace



def suAlphaPairMetricDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    (E × E) →L[ℝ] (E × E) →L[ℝ] E →L[ℝ] ℝ :=
  let T := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    D.flip
  T.bilinearComp (ContinuousLinearMap.fst ℝ E E) (ContinuousLinearMap.fst ℝ E E) +
    T.bilinearComp (ContinuousLinearMap.snd ℝ E E) (ContinuousLinearMap.snd ℝ E E)

theorem suAlphaPairMetricDerivative_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (v w : E × E) (a : E) :
    suAlphaPairMetricDerivative D v w a = D a v.1 w.1 + D a v.2 w.2 := rfl


theorem suAlphaPairMetric_contDiffOn
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set P} {B : P → E →L[ℝ] E →L[ℝ] ℝ} {k : WithTop ℕ∞}
    (hB : ContDiffOn ℝ k B s) : ContDiffOn ℝ k (fun x => suAlphaPairMetric (B x)) s := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  change ContDiffOn ℝ k (fun x => B x v.1 w.1 + B x v.2 w.2) s
  exact ((hB.clm_apply contDiffOn_const).clm_apply contDiffOn_const).add
    ((hB.clm_apply contDiffOn_const).clm_apply contDiffOn_const)

theorem suAlphaPairMetricDerivative_contDiffOn
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set P} {D : P → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ} {k : WithTop ℕ∞}
    (hD : ContDiffOn ℝ k D s) :
    ContDiffOn ℝ k (fun x => suAlphaPairMetricDerivative (D x)) s := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  apply contDiffOn_clm_apply.mpr
  intro a
  change ContDiffOn ℝ k (fun x => D x a v.1 w.1 + D x a v.2 w.2) s
  exact (((hD.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply
    contDiffOn_const).add (((hD.clm_apply contDiffOn_const).clm_apply
      contDiffOn_const).clm_apply contDiffOn_const)



def suAlphaCoordinateFlux {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ)
    (x : LoopPlane × EuclideanSpace ℝ (Fin n))
    (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
  let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
  suAlphaRoundFactor x.1 • suAlphaFlux
    ((suAlphaRoundFactor x.1)⁻¹ • suAlphaPairMetric (G x.2)) 1 alpha q

def suAlphaCoordinateSource {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ)
    (x : LoopPlane × EuclideanSpace ℝ (Fin n))
    (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
  suAlphaSource ((suAlphaRoundFactor x.1)⁻¹ • suAlphaPairMetric (G x.2))
    (suAlphaPairMetricDerivative (fderiv ℝ G x.2)) 1 alpha q

theorem suAlphaCoordinateFlux_apply
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ)
    (z : LoopPlane) (u : EuclideanSpace ℝ (Fin n))
    (q v : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
    suAlphaCoordinateFlux g b alpha (z, u) q v =
      2 * alpha * (1 + (G u q.1 q.1 + G u q.2 q.2) / suAlphaRoundFactor z) ^ (alpha - 1) *
        (G u q.1 v.1 + G u q.2 v.2) := by
  have hlam : suAlphaRoundFactor z ≠ 0 := by dsimp [suAlphaRoundFactor]; positivity
  change suAlphaRoundFactor z * (2 * alpha *
      (1 + (suAlphaRoundFactor z)⁻¹ *
        (g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm u q.1 q.1 +
          g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm u q.2 q.2)) ^
        (alpha - 1) * ((suAlphaRoundFactor z)⁻¹ *
        (g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm u q.1 v.1 +
          g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm u q.2 v.2))) = _
  rw [show (suAlphaRoundFactor z)⁻¹ *
    (g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm u q.1 q.1 +
      g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm u q.2 q.2) =
    (g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm u q.1 q.1 +
      g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm u q.2 q.2) /
      suAlphaRoundFactor z by rw [div_eq_mul_inv, mul_comm]]
  field_simp

theorem suAlphaCoordinateSource_apply
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ)
    (z : LoopPlane) (u : EuclideanSpace ℝ (Fin n))
    (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) :
    let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
    suAlphaCoordinateSource g b alpha (z, u) q v =
      -(alpha * (1 + (G u q.1 q.1 + G u q.2 q.2) / suAlphaRoundFactor z) ^ (alpha - 1)) *
        (fderiv ℝ G u v q.1 q.1 + fderiv ℝ G u v q.2 q.2) := by
  dsimp only
  change (-alpha * (1 + (suAlphaRoundFactor z)⁻¹ *
      (g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm u q.1 q.1 +
        g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm u q.2 q.2)) ^
      (alpha - 1)) * _ = _
  rw [neg_mul]
  congr 3
  rw [div_eq_mul_inv, mul_comm]



theorem SUWeakAlphaCoordinate.coordinateFlux_pairing
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {center : LoopPlane} {R : ℝ}
    (S : SUWeakAlphaCoordinate g b alpha u V center R) (z : LoopPlane)
    (v : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    suAlphaCoordinateFlux g b alpha (z, u z) (V 0 z, V 1 z) v =
      ∑ a : Fin n, (S.flux a 0 z * v.1 a + S.flux a 1 z * v.2 a) := by
  rw [Finset.sum_add_distrib, S.flux_pairing, S.flux_pairing,
    suAlphaCoordinateFlux_apply]
  simp only [SUWeakAlphaCoordinate.naturalWeight, Fin.sum_univ_two]
  ring

theorem SUWeakAlphaCoordinate.coordinateSource_pairing
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {center : LoopPlane} {R : ℝ}
    (S : SUWeakAlphaCoordinate g b alpha u V center R) (z : LoopPlane)
    (v : EuclideanSpace ℝ (Fin n)) :
    suAlphaCoordinateSource g b alpha (z, u z) (V 0 z, V 1 z) v =
      ∑ a : Fin n, S.sourceTerm a z * v a := by
  rw [S.source_pairing, suAlphaCoordinateSource_apply]
  simp only [SUWeakAlphaCoordinate.naturalWeight, Fin.sum_univ_two]

set_option maxHeartbeats 800000 in




theorem suAlphaCoordinate_natural_bounds
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) {alpha : ℝ} (ha : 1 ≤ alpha)
    (center : LoopPlane) {R : ℝ} (_hR : 0 ≤ R)
    (u0 : EuclideanSpace ℝ (Fin n)) (radius : ℝ)
    (hrange : closedBall u0 radius ⊆ (extChartAt (𝓡 n) b).target) :
    let K := closedBall center R ×ˢ closedBall u0 radius
    ∃ nu C : ℝ, 0 < nu ∧ 0 < C ∧ ∀ x ∈ K,
      (∀ q r, nu * ((1 + ‖q‖ ^ 2) ^ (alpha - 1) + (1 + ‖r‖ ^ 2) ^ (alpha - 1)) *
          ‖q - r‖ ^ 2 ≤
        (suAlphaCoordinateFlux g b alpha x q - suAlphaCoordinateFlux g b alpha x r) (q - r)) ∧
      (∀ q r, ‖suAlphaCoordinateFlux g b alpha x q - suAlphaCoordinateFlux g b alpha x r‖ ≤
        C * ((1 + ‖q‖ ^ 2) ^ (alpha - 1) + (1 + ‖r‖ ^ 2) ^ (alpha - 1)) * ‖q - r‖) ∧
      (∀ q r, ‖suAlphaCoordinateSource g b alpha x q - suAlphaCoordinateSource g b alpha x r‖ ≤
        C * ((1 + ‖q‖ ^ 2) ^ (alpha - 1 / 2) +
          (1 + ‖r‖ ^ 2) ^ (alpha - 1 / 2)) * ‖q - r‖) ∧
      ∀ y ∈ K, ∀ q,
        ‖suAlphaCoordinateFlux g b alpha y q - suAlphaCoordinateFlux g b alpha x q‖ ≤
          C * (1 + ‖q‖ ^ 2) ^ (alpha - 1 / 2) * ‖y - x‖ ∧
        ‖suAlphaCoordinateSource g b alpha y q - suAlphaCoordinateSource g b alpha x q‖ ≤
          C * (1 + ‖q‖ ^ 2) ^ alpha * ‖y - x‖ := by
  let E := EuclideanSpace ℝ (Fin n)
  let K := closedBall center R ×ˢ closedBall u0 radius
  let G := g.pullbackCoefficients (chartAt E b).symm
  let B (x : LoopPlane × E) := (suAlphaRoundFactor x.1)⁻¹ • suAlphaPairMetric (G x.2)
  let D (x : LoopPlane × E) := suAlphaPairMetricDerivative (fderiv ℝ G x.2)
  let a (x : LoopPlane × E) := suAlphaRoundFactor x.1
  have hK : IsCompact K := (isCompact_closedBall center R).prod (isCompact_closedBall u0 radius)
  have hconv : Convex ℝ K := (convex_closedBall center R).prod (convex_closedBall u0 radius)
  have hlam (z : LoopPlane) : 0 < suAlphaRoundFactor z := by dsimp [suAlphaRoundFactor]; positivity
  have hlam1 (z : LoopPlane) : suAlphaRoundFactor z ≤ 1 := by
    unfold suAlphaRoundFactor
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg (‖z‖ ^ 2)]
  have hlamsmooth : ContDiff ℝ ∞ suAlphaRoundFactor := by
    unfold suAlphaRoundFactor
    exact contDiff_const.div (((contDiff_norm_sq ℝ).add contDiff_const).pow 2)
      (fun z => by positivity)
  have hG : ContDiffOn ℝ ∞ G (extChartAt (𝓡 n) b).target := g.contDiffOn_chartCoefficients b
  have hDG : ContDiffOn ℝ ∞ (fderiv ℝ G) (extChartAt (𝓡 n) b).target :=
    hG.fderiv_of_isOpen (isOpen_extChartAt_target b) (by simp)
  have hB (x : LoopPlane × E) (hx : x ∈ K) : ContDiffAt ℝ 1 B x := by
    have hm : ContDiffAt ℝ 1 (fun y => suAlphaPairMetric (G y)) x.2 :=
      ((suAlphaPairMetric_contDiffOn hG).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds (hrange hx.2))).of_le (by simp)
    exact (((hlamsmooth.contDiffAt.inv (hlam x.1).ne').of_le (by simp)).comp _
      contDiffAt_fst).smul (hm.comp _ contDiffAt_snd)
  have hD (x : LoopPlane × E) (hx : x ∈ K) : ContDiffAt ℝ 1 D x :=
    (((suAlphaPairMetricDerivative_contDiffOn hDG).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds (hrange hx.2))).of_le (by simp)).comp _ contDiffAt_snd
  have ha' (x : LoopPlane × E) : ContDiffAt ℝ 1 a x :=
    (hlamsmooth.contDiffAt.of_le (by simp)).comp _ contDiffAt_fst
  obtain ⟨k0, _, hk0, _, _, _, hkG⟩ :=
    suAlpha_coordinate_metric_bounds g b (isCompact_closedBall u0 radius) hrange
  let k := min 1 k0
  have hk : 0 < k := lt_min zero_lt_one hk0
  have hpositive (x : LoopPlane × E) (hx : x ∈ K) :
      k ≤ (1 : ℝ) ∧ ∀ q : E × E, k * ‖q‖ ^ 2 ≤ B x q q := by
    refine ⟨min_le_left _ _, fun q => ?_⟩
    have hp := suAlphaPairMetric_coercive (G x.2) hk0.le (hkG x.2 hx.2) q
    have hinv : 1 ≤ (suAlphaRoundFactor x.1)⁻¹ := (one_le_inv₀ (hlam x.1)).mpr (hlam1 x.1)
    change k * ‖q‖ ^ 2 ≤ (suAlphaRoundFactor x.1)⁻¹ * suAlphaPairMetric (G x.2) q q
    exact ((mul_le_mul_of_nonneg_right (min_le_right 1 k0) (sq_nonneg _)).trans hp).trans
      (le_mul_of_one_le_left ((mul_nonneg hk0.le (sq_nonneg _)).trans hp) hinv)
  obtain ⟨CF, hCF, hf⟩ := suAlphaFlux_coefficient_bounds hK hconv B (fun _ => 1) a alpha hk
    hB (fun _ _ => contDiffAt_const) (fun x _ => ha' x) hpositive
  obtain ⟨CS, hCS, hs⟩ := suAlphaSource_coefficient_bounds hK hconv B D (fun _ => 1)
    (fun _ => 1) alpha hk hB hD (fun _ _ => contDiffAt_const)
    (fun _ _ => contDiffAt_const) hpositive
  let a0 := 16 / (((‖center‖ + R) ^ 2 + 4) ^ 2)
  have ha0 : 0 < a0 := by dsimp [a0]; positivity
  have ha0le (z : LoopPlane) (hz : z ∈ closedBall center R) : a0 ≤ suAlphaRoundFactor z := by
    have hn : ‖z‖ ≤ ‖center‖ + R := by
      have hn := norm_le_norm_sub_add z center
      have hz' : ‖z - center‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hz
      linarith
    dsimp only [a0, suAlphaRoundFactor]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    gcongr
  let nu := a0 * (alpha * k * k ^ (alpha - 1))
  have hnu : 0 < nu := by dsimp [nu]; positivity
  have hfs (x : LoopPlane × E) (hx : x ∈ K) (q : E × E) :
      DifferentiableAt ℝ (suAlphaCoordinateFlux g b alpha x) q ∧
        ‖fderiv ℝ (suAlphaCoordinateFlux g b alpha x) q‖ ≤ CF * (1 + ‖q‖ ^ 2) ^ (alpha - 1) := by
    obtain ⟨t, ht, hu, hb, _⟩ := hf q
    have hp : t ^ (1 - 2 * alpha + 1) = (1 + ‖q‖ ^ 2) ^ (alpha - 1) := by
      rw [suGradientParameters_rpow ht hu]
      congr 1
      ring
    exact hp ▸ hb x hx
  have hss (x : LoopPlane × E) (hx : x ∈ K) (q : E × E) :
      DifferentiableAt ℝ (suAlphaCoordinateSource g b alpha x) q ∧
        ‖fderiv ℝ (suAlphaCoordinateSource g b alpha x) q‖ ≤
          CS * (1 + ‖q‖ ^ 2) ^ (alpha - 1 / 2) := by
    obtain ⟨t, ht, hu, hb, _⟩ := hs q
    have hp : t ^ (-2 * alpha + 1) = (1 + ‖q‖ ^ 2) ^ (alpha - 1 / 2) := by
      rw [suGradientParameters_rpow ht hu]
      congr 1
      ring
    have heq : (fun w => (1 : ℝ) • suAlphaSource (B x) (D x) 1 alpha w) =
        suAlphaCoordinateSource g b alpha x := by
      funext w
      simp only [one_smul]
      rfl
    have h := hb x hx
    rw [heq, hp] at h
    exact h
  refine ⟨nu, CF + CS, hnu, add_pos hCF hCS, fun x hx => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro q r
    have hsymm (v w : E × E) : B x v w = B x w v := by
      change (suAlphaRoundFactor x.1)⁻¹ * (G x.2 v.1 w.1 + G x.2 v.2 w.2) =
        (suAlphaRoundFactor x.1)⁻¹ * (G x.2 w.1 v.1 + G x.2 w.2 v.2)
      congr 1
      exact congrArg₂ (fun a b : ℝ => a + b) (g.symm _ _ _) (g.symm _ _ _)
    have hm := mul_le_mul_of_nonneg_left
      (suAlphaFlux_canonical_monotone (B x) hk (hpositive x hx).1 ha (hpositive x hx).2 hsymm q r)
      (hlam x.1).le
    have hl := mul_le_mul_of_nonneg_right (ha0le x.1 hx.1)
      (show 0 ≤ (alpha * k * k ^ (alpha - 1)) *
        ((1 + ‖q‖ ^ 2) ^ (alpha - 1) + (1 + ‖r‖ ^ 2) ^ (alpha - 1)) * ‖q - r‖ ^ 2 by positivity)
    change nu * _ * _ ≤ _
    dsimp only [suAlphaCoordinateFlux]
    simp only [sub_apply, smul_apply, smul_eq_mul]
    dsimp only [nu] at ⊢
    simp only [sub_apply] at hm
    change _ ≤ _ at hm
    dsimp only [B] at hm
    nlinarith
  · intro q r
    have h := suNaturalCoefficient_difference _ (fun z => (hfs x hx z).1) hCF.le
      (by linarith : 0 ≤ alpha - 1) (fun z => (hfs x hx z).2) q r
    exact h.trans (by gcongr; linarith)
  · intro q r
    have h := suNaturalCoefficient_difference _ (fun z => (hss x hx z).1) hCS.le
      (by linarith : 0 ≤ alpha - 1 / 2) (fun z => (hss x hx z).2) q r
    exact h.trans (by gcongr; linarith)
  · intro y hy q
    obtain ⟨t, ht, hu, _, hb⟩ := hf q
    obtain ⟨s, hs', hv, _, hd⟩ := hs q
    have hp : t ^ (1 - 2 * alpha) = (1 + ‖q‖ ^ 2) ^ (alpha - 1 / 2) := by
      rw [suGradientParameters_rpow ht hu]
      congr 1
      ring
    have hq : s ^ (-2 * alpha) = (1 + ‖q‖ ^ 2) ^ alpha := by
      rw [suGradientParameters_rpow hs' hv]
      congr 1
      ring
    have hf' := hb x hx y hy
    have hs' := hd x hx y hy
    rw [hp] at hf'
    simp only [one_smul, hq] at hs'
    exact ⟨hf'.trans (by gcongr; linarith), hs'.trans (by gcongr; linarith)⟩

set_option maxHeartbeats 1000000 in




theorem SUWeakAlphaCoordinate.natural_difference_bounds
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {center : LoopPlane} {R : ℝ}
    (S : SUWeakAlphaCoordinate g b alpha u V center R) (ha : 1 ≤ alpha) :
    ∃ radius nu C : ℝ, 0 < radius ∧ 0 < nu ∧ 0 < C ∧
      closedBall (u center) radius ⊆ (extChartAt (𝓡 n) b).target ∧
      (∀ delta : ℝ, 0 < delta → ∃ innerRadius : ℝ, 0 < innerRadius ∧ innerRadius < R ∧
        MapsTo u (closedBall center innerRadius) (ball (u center) (min delta (radius / 2)))) ∧
      ∀ x ∈ closedBall center R ×ˢ closedBall (u center) radius,
      ∀ y ∈ closedBall center R ×ˢ closedBall (u center) radius,
      ∀ q r : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ∀ w : EuclideanSpace ℝ (Fin n), ∀ h : ℝ, h ≠ 0 →
        ‖y - x‖ ≤ |h| * (1 + ‖w‖) →
        let d := h⁻¹ • (q - r)
        let W := (1 + ‖q‖ ^ 2) ^ (alpha - 1) + (1 + ‖r‖ ^ 2) ^ (alpha - 1)
        let H := (1 + ‖q‖ ^ 2) ^ alpha + (1 + ‖r‖ ^ 2) ^ alpha
        let P := h⁻¹ • (suAlphaCoordinateFlux g b alpha y q - suAlphaCoordinateFlux g b alpha y r)
        let A := h⁻¹ • (suAlphaCoordinateFlux g b alpha y r - suAlphaCoordinateFlux g b alpha x r)
        let B := h⁻¹ •
          (suAlphaCoordinateSource g b alpha y q - suAlphaCoordinateSource g b alpha y r)
        let D := h⁻¹ •
          (suAlphaCoordinateSource g b alpha y r - suAlphaCoordinateSource g b alpha x r)
        0 ≤ W ∧ 0 ≤ H ∧ nu * W * ‖d‖ ^ 2 ≤ P d ∧
          ‖P‖ ≤ C * W * ‖d‖ ∧
          ‖A‖ ^ 2 ≤ C ^ 2 * W * H * (1 + ‖w‖ ^ 2) ∧
          ‖B‖ ^ 2 ≤ C ^ 2 * W * H * ‖d‖ ^ 2 ∧
          ‖D‖ ≤ C * H * (1 + ‖w‖) := by
  obtain ⟨radius, _, _, hr, _, _, hrange, _, hshrink⟩ := S.coefficient_neighborhood
  obtain ⟨nu, C, hnu, hC, hbounds⟩ :=
    suAlphaCoordinate_natural_bounds g b ha center S.radius_pos.le (u center) radius hrange
  refine ⟨radius, nu, 2 * C, hr, hnu, by positivity, hrange, hshrink, ?_⟩
  intro x hx y hy q r w h hh hbase
  let d := h⁻¹ • (q - r)
  let W := (1 + ‖q‖ ^ 2) ^ (alpha - 1) + (1 + ‖r‖ ^ 2) ^ (alpha - 1)
  let H := (1 + ‖q‖ ^ 2) ^ alpha + (1 + ‖r‖ ^ 2) ^ alpha
  let P := h⁻¹ • (suAlphaCoordinateFlux g b alpha y q - suAlphaCoordinateFlux g b alpha y r)
  let A := h⁻¹ • (suAlphaCoordinateFlux g b alpha y r - suAlphaCoordinateFlux g b alpha x r)
  let B := h⁻¹ • (suAlphaCoordinateSource g b alpha y q - suAlphaCoordinateSource g b alpha y r)
  let D := h⁻¹ • (suAlphaCoordinateSource g b alpha y r - suAlphaCoordinateSource g b alpha x r)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hcancel : |h⁻¹| * |h| = 1 := by simp [abs_inv, hh]
  have hd : ‖d‖ = |h⁻¹| * ‖q - r‖ := by simp [d, norm_smul]
  have hmono : nu * W * ‖d‖ ^ 2 ≤ P d := by
    have hm := mul_le_mul_of_nonneg_left ((hbounds y hy).1 q r) (sq_nonneg h⁻¹)
    simpa only [d, P, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      smul_apply, map_smul, smul_eq_mul] using
      (show nu * W * (h⁻¹ ^ 2 * ‖q - r‖ ^ 2) ≤ h⁻¹ * (h⁻¹ *
        (suAlphaCoordinateFlux g b alpha y q - suAlphaCoordinateFlux g b alpha y r) (q - r)) by
        dsimp only [W] at ⊢
        nlinarith)
  have hP : ‖P‖ ≤ C * W * ‖d‖ := by
    calc
      ‖P‖ = |h⁻¹| * ‖suAlphaCoordinateFlux g b alpha y q - suAlphaCoordinateFlux g b alpha y r‖ :=
        by simp [P, norm_smul]
      _ ≤ |h⁻¹| * (C * W * ‖q - r‖) :=
        mul_le_mul_of_nonneg_left ((hbounds y hy).2.1 q r) (abs_nonneg _)
      _ = _ := by rw [hd]; ring
  have hA : ‖A‖ ≤ C * (1 + ‖r‖ ^ 2) ^ (alpha - 1 / 2) * (1 + ‖w‖) := by
    calc
      ‖A‖ = |h⁻¹| * ‖suAlphaCoordinateFlux g b alpha y r - suAlphaCoordinateFlux g b alpha x r‖ :=
        by simp [A, norm_smul]
      _ ≤ |h⁻¹| * (C * (1 + ‖r‖ ^ 2) ^ (alpha - 1 / 2) * ‖y - x‖) :=
        mul_le_mul_of_nonneg_left ((hbounds x hx).2.2.2 y hy r).1 (abs_nonneg _)
      _ ≤ |h⁻¹| * (C * (1 + ‖r‖ ^ 2) ^ (alpha - 1 / 2) * (|h| * (1 + ‖w‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbase (by positivity)) (abs_nonneg _)
      _ = _ := by
        calc
          _ = (|h⁻¹| * |h|) * (C * (1 + ‖r‖ ^ 2) ^ (alpha - 1 / 2) * (1 + ‖w‖)) := by ring
          _ = _ := by rw [hcancel, one_mul]
  have hB : ‖B‖ ≤ C * ((1 + ‖q‖ ^ 2) ^ (alpha - 1 / 2) +
      (1 + ‖r‖ ^ 2) ^ (alpha - 1 / 2)) * ‖d‖ := by
    calc
      ‖B‖ = |h⁻¹| *
          ‖suAlphaCoordinateSource g b alpha y q - suAlphaCoordinateSource g b alpha y r‖ :=
        by simp [B, norm_smul]
      _ ≤ |h⁻¹| * (C * ((1 + ‖q‖ ^ 2) ^ (alpha - 1 / 2) +
          (1 + ‖r‖ ^ 2) ^ (alpha - 1 / 2)) * ‖q - r‖) :=
        mul_le_mul_of_nonneg_left ((hbounds y hy).2.2.1 q r) (abs_nonneg _)
      _ = _ := by rw [hd]; ring
  have hD : ‖D‖ ≤ C * H * (1 + ‖w‖) := by
    have hb := ((hbounds x hx).2.2.2 y hy r).2
    have ht := mul_le_mul_of_nonneg_left
      (hb.trans (mul_le_mul_of_nonneg_left hbase (by positivity))) (abs_nonneg h⁻¹)
    have he : |h⁻¹| * (C * (1 + ‖r‖ ^ 2) ^ alpha * (|h| * (1 + ‖w‖))) =
        C * (1 + ‖r‖ ^ 2) ^ alpha * (1 + ‖w‖) := by
      calc
        _ = (|h⁻¹| * |h|) * (C * (1 + ‖r‖ ^ 2) ^ alpha * (1 + ‖w‖)) := by ring
        _ = _ := by rw [hcancel, one_mul]
    rw [he] at ht
    rw [show ‖D‖ = |h⁻¹| *
      ‖suAlphaCoordinateSource g b alpha y r - suAlphaCoordinateSource g b alpha x r‖ by
      simp [D, norm_smul]]
    exact ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)) hC.le)
      (by positivity))
  have hproduct := suNaturalWeights_pair_square alpha q r
  change ((1 + ‖q‖ ^ 2) ^ (alpha - 1 / 2) + (1 + ‖r‖ ^ 2) ^ (alpha - 1 / 2)) ^ 2 ≤
      2 * W * H ∧ ((1 + ‖r‖ ^ 2) ^ (alpha - 1 / 2)) ^ 2 ≤ W * H at hproduct
  have hAsq : ‖A‖ ^ 2 ≤ (2 * C) ^ 2 * W * H * (1 + ‖w‖ ^ 2) := by
    have ha' := pow_le_pow_left₀ (norm_nonneg A) hA 2
    have hw : (1 + ‖w‖) ^ 2 ≤ 2 * (1 + ‖w‖ ^ 2) := by nlinarith [sq_nonneg (‖w‖ - 1)]
    have ht := mul_le_mul hproduct.2 hw (sq_nonneg _) (mul_nonneg hW hH)
    have hm := mul_le_mul_of_nonneg_left ht (sq_nonneg C)
    nlinarith [show 0 ≤ C ^ 2 * W * H * (1 + ‖w‖ ^ 2) by positivity]
  have hBsq : ‖B‖ ^ 2 ≤ (2 * C) ^ 2 * W * H * ‖d‖ ^ 2 := by
    have hb' := pow_le_pow_left₀ (norm_nonneg B) hB 2
    have hm := mul_le_mul_of_nonneg_left hproduct.1 (by positivity : 0 ≤ C ^ 2 * ‖d‖ ^ 2)
    nlinarith [show 0 ≤ C ^ 2 * W * H * ‖d‖ ^ 2 by positivity]
  exact ⟨hW, hH, hmono, hP.trans (by nlinarith [show 0 ≤ C * W * ‖d‖ by positivity]),
    hAsq, hBsq, hD.trans (by nlinarith [show 0 ≤ C * H * (1 + ‖w‖) by positivity])⟩

end PoincareConjecture.M60
