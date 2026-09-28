import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.WeightedFiberBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Scaling
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Similarity








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology Bundle
namespace PoincareConjecture.RiemannianMetric
private theorem scaled_closedBall_iff
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {a : ℝ} (ha : 0 < a) (p x : M) (r : ℝ) :
    (PoincareConjecture.rescaledMetric g a ha).edist p x ≤ ENNReal.ofReal (Real.sqrt a*r) ↔
      g.edist p x ≤ ENNReal.ofReal r := by
  rw [PoincareConjecture.rescaledMetric_edist, ENNReal.ofReal_mul (Real.sqrt_nonneg a)]
  rw [mul_comm (ENNReal.ofReal (Real.sqrt a)) (g.edist p x),
    mul_comm (ENNReal.ofReal (Real.sqrt a)) (ENNReal.ofReal r)]
  exact ENNReal.mul_le_mul_iff_left (by positivity) ENNReal.ofReal_ne_top



theorem exists_scaled_openFiber_weighted_corner_geometry
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M]
    [IsManifold (𝓡 (m+k)) ∞ M]
    (g : RiemannianMetric (m+k) M) (D : LeviCivitaData g)
    (hc : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 (m+k)) x), -1 ≤ D.sectionalCurvature x v w)
    (f h : Fin k → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ, ℝ) ∞ (h i))
    (U : Opens M) {δ H : ℝ}
    (hunit : ∀ x ∈ U, ∀ i,
      g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (D.gradient (h i) x) ≤ 1)
    (hpair : ∀ x ∈ U, ∀ i,
      g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1+2*δ)
    (hcross : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (D.gradient (f i) x) (D.gradient (f j) x)| ≤ δ ∧
      |g.inner x (D.gradient (f i) x) (D.gradient (h j) x)| ≤ δ ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (f j) x)| ≤ δ ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (h j) x)| ≤ δ)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (D.gradient (f i) x) (D.gradient (f j) x) ≤ 0)
    (hhess : ∀ x ∈ U, ∀ i z,
      D.hessian (f i) x z z ≤ H*g.inner x z z ∧
      D.hessian (h i) x z z ≤ H*g.inner x z z)
    (v : Fin k → ℝ) (hm : 2 ≤ m) {a : ℝ} (ha : 1 ≤ a) :
    let P := fun x i => f i x
    let hP : ContMDiff (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) ∞ P := contMDiff_pi_space.mpr hf
    ∀ hreg : ∀ x ∈ U, Surjective
      (mfderiv (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) P x),
    let G := PoincareConjecture.rescaledMetric g a (zero_lt_one.trans_le ha)
    let DG := PoincareConjecture.rescaledMetric_connection g D a (zero_lt_one.trans_le ha)
    let fs := fun i x => Real.sqrt a * f i x
    let hs := fun i x => Real.sqrt a * h i x
    let Ps := fun x => Real.sqrt a • P x
    let vs := Real.sqrt a • v
    MetricComplete G ∧
      (∀ x (z w : TangentSpace (𝓡 (m+k)) x), -1 ≤ DG.sectionalCurvature x z w) ∧
      (∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ, ℝ) ∞ (fs i)) ∧
      (∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ, ℝ) ∞ (hs i)) ∧
      (∀ x ∈ U, ∀ i,
        G.tangentNorm x (DG.gradient (fs i) x) ≤ 1 ∧
        G.tangentNorm x (DG.gradient (hs i) x) ≤ 1) ∧
      (∀ x ∈ U, ∀ i,
        G.inner x (DG.gradient (fs i) x) (DG.gradient (hs i) x) ≤ -1+2*δ) ∧
      (∀ x ∈ U, ∀ i j, i ≠ j →
        |G.inner x (DG.gradient (fs i) x) (DG.gradient (fs j) x)| ≤ δ ∧
        |G.inner x (DG.gradient (fs i) x) (DG.gradient (hs j) x)| ≤ δ ∧
        |G.inner x (DG.gradient (hs i) x) (DG.gradient (fs j) x)| ≤ δ ∧
        |G.inner x (DG.gradient (hs i) x) (DG.gradient (hs j) x)| ≤ δ) ∧
      (∀ x ∈ U, ∀ i j, i ≠ j →
        G.inner x (DG.gradient (fs i) x) (DG.gradient (fs j) x) ≤ 0) ∧
      (∀ x ∈ U, ∀ i z,
        DG.hessian (fs i) x z z ≤ (H/Real.sqrt a)*G.inner x z z ∧
        DG.hessian (hs i) x z z ≤ (H/Real.sqrt a)*G.inner x z z) ∧
      ∃ hPs : ContMDiff (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) ∞ Ps,
      ∃ hregS : ∀ x ∈ U, Surjective
        (mfderiv (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) Ps x),
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI := openFiberChartedSpace (m := m) hP U hreg v
        letI := isManifold_openFiber (m := m) hP U hreg v
        letI := openFiberChartedSpace (m := m) hPs U hregS vs
        letI := isManifold_openFiber (m := m) hPs U hregS vs
        let gOld := g.openRegularFiberMetric hP U hreg v
        let gNew := G.openRegularFiberMetric hPs U hregS vs
        ∃ e : openFiber P U v ≃ₘ⟮𝓡 m, 𝓡 m⟯ openFiber Ps U vs,
          (∀ x, openFiberIncl Ps U vs (e x) = openFiberIncl P U v x) ∧
          (∀ (x : openFiber P U v) (z w : TangentSpace (𝓡 m) x),
            gNew.inner (e x) (mfderiv (𝓡 m) (𝓡 m) e x z)
              (mfderiv (𝓡 m) (𝓡 m) e x w) = a*gOld.inner x z w) ∧
          (∀ x y, gNew.edist (e x) (e y) =
            ENNReal.ofReal (Real.sqrt a)*gOld.edist x y) ∧
          (∀ (p : M) (r : ℝ),
            e '' {x | openFiberIncl P U v x ∈ g.ball p r} =
              {y | openFiberIncl Ps U vs y ∈ G.ball p (Real.sqrt a*r)}) ∧
          (∀ η : ℝ,
            (∀ x : openFiber P U v, ∀ y : M,
              g.edist (openFiberIncl P U v x) y ≤ ENNReal.ofReal η → y ∈ U) →
            ∀ x : openFiber Ps U vs, ∀ y : M,
              G.edist (openFiberIncl Ps U vs x) y ≤ ENNReal.ofReal (Real.sqrt a*η) →
                y ∈ U) ∧
          ∀ K : openFiber P U v → ℝ, Continuous K → (∀ x, 0 ≤ K x) →
            (∀ x (z w : TangentSpace (𝓡 m) x),
              -K x ≤ gOld.leviCivitaData.sectionalCurvature x z w) →
            let Knew := fun y => a⁻¹*K (e.symm y)
            Continuous Knew ∧ (∀ y, 0 ≤ Knew y) ∧
              (∀ y (z w : TangentSpace (𝓡 m) y),
                -Knew y ≤ gNew.leviCivitaData.sectionalCurvature y z w) ∧
              ∀ (p : M) (r R : ℝ),
                g.openFiberWeightedAmbientBallRatio hP U hreg v K p r R ≤
                  G.openFiberWeightedAmbientBallRatio hPs U hregS vs Knew p
                    (Real.sqrt a*r) (Real.sqrt a*R) := by
  dsimp only
  intro hreg
  let P := fun x i => f i x
  let hP : ContMDiff (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) ∞ P :=
    contMDiff_pi_space.mpr hf
  have hap : 0 < a := zero_lt_one.trans_le ha
  let G := PoincareConjecture.rescaledMetric g a hap
  let DG := PoincareConjecture.rescaledMetric_connection g D a hap
  let Ps := fun x => Real.sqrt a • P x
  let vs := Real.sqrt a • v
  have hcG : MetricComplete G := PoincareConjecture.metricComplete_rescaledMetric g a hap hc
  have hsecG : ∀ x (z w : TangentSpace (𝓡 (m+k)) x),
      -1 ≤ DG.sectionalCurvature x z w := by
    intro x z w
    change -1 ≤ (PoincareConjecture.rescaledMetric_connection g D a hap).sectionalCurvature x z w
    rw [PoincareConjecture.rescaledMetric_sectionalCurvature]
    have hl := mul_le_mul_of_nonneg_left (hsec x z w) (inv_nonneg.mpr hap.le)
    have hi : a⁻¹ ≤ 1 := (inv_le_one₀ hap).mpr ha
    nlinarith
  obtain ⟨hfs, hhs, hunitS, hpairS, hcrossS, htightS, hhessS⟩ :=
    D.rescaled_smooth_strainer_pair_bounds f h hf hh hunit hpair hcross htight hhess hap
  refine ⟨hcG, hsecG, hfs, hhs, hunitS, hpairS, hcrossS, htightS, hhessS, ?_⟩
  obtain ⟨hPs, hregS, hdata⟩ :=
    g.exists_scaled_openFiber_weighted_ambientBall_equivalence hP U hreg v hm ha
  refine ⟨hPs, hregS, ?_⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hP U hreg v
  let := isManifold_openFiber (m := m) hP U hreg v
  let := openFiberChartedSpace (m := m) hPs U hregS vs
  let := isManifold_openFiber (m := m) hPs U hregS vs
  let gOld := g.openRegularFiberMetric hP U hreg v
  let gNew := G.openRegularFiberMetric hPs U hregS vs
  obtain ⟨e, hinc, hmetric, hdist, _, himage, hratio⟩ := hdata
  refine ⟨e, hinc, hmetric, hdist, himage, ?_, ?_⟩
  · intro η hbuffer x y hxy
    obtain ⟨x, rfl⟩ := e.surjective x
    change G.edist (openFiberIncl Ps U vs (e x)) y ≤ ENNReal.ofReal (Real.sqrt a*η) at hxy
    rw [hinc] at hxy
    exact hbuffer x y ((scaled_closedBall_iff g hap (openFiberIncl P U v x) y η).mp hxy)
  · intro K hK hK0 hKsec
    refine ⟨continuous_const.mul (hK.comp e.symm.continuous),
      (fun y => mul_nonneg (inv_nonneg.mpr hap.le) (hK0 (e.symm y))),
      ?_, ?_⟩
    · exact gOld.leviCivitaData.sectionalCurvature_lower_bound_of_metric_similarity
        gNew.leviCivitaData e hap hmetric hKsec
    · intro p r R
      exact hratio K hK0 p r R


end PoincareConjecture.RiemannianMetric
