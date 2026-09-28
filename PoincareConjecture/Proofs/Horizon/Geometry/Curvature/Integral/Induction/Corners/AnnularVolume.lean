import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.LocalVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Connected
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.ModelBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Covering
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Balls
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ZeroDimensional








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology Bundle


def PoincareConjecture.RiemannianMetric.annularCornerVolumeConstant
    (m k : ℕ) (H η : ℝ) : ℝ :=
  let l := min (1 / 4 : ℝ) (η / 4)
  (⌈(12 / l) ^ (m + k) * Real.exp (6 * ((m + k : ℕ) : ℝ))⌉₊ : ℝ) *
    (2 * ((k : ℝ) + 1) / l) ^ k * max 1 (euclideanUnitBallVolume (m + k)) *
      4 ^ (m + k) * Real.exp (((m + k : ℕ) : ℝ) * (H + 4))


theorem PoincareConjecture.RiemannianMetric.annularCornerVolumeConstant_pos
    (m k : ℕ) (H : ℝ) {η : ℝ} (hη : 0 < η) :
    0 < annularCornerVolumeConstant m k H η := by
  have hl : 0 < min (1 / 4 : ℝ) (η / 4) := lt_min (by norm_num) (by positivity)
  have hN : 0 < ⌈(12 / min (1 / 4 : ℝ) (η / 4)) ^ (m + k) *
      Real.exp (6 * ((m + k : ℕ) : ℝ))⌉₊ :=
    Nat.ceil_pos.mpr (by positivity)
  unfold annularCornerVolumeConstant
  positivity

namespace PoincareConjecture.RiemannianMetric

private theorem annular_cover
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w)
    (p : M) {r l : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hl : 0 < l) (hl1 : l ≤ 1 / 4) :
    ∃ S : Finset M,
      S.card ≤ ⌈(12 / l) ^ n * Real.exp (6 * (n : ℝ))⌉₊ ∧
      ∀ x, g.edist p x < ENNReal.ofReal (2 * r) →
        ∃ z ∈ S, g.edist z x < ENNReal.ofReal (l * r) := by
  classical
  let U := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  let gU := g.connectedComponentMetric p
  let pU : U := ⟨p, mem_connectedComponent⟩
  have hmem (x : M) (hx : g.edist p x < ENNReal.ofReal (2 * r)) : x ∈ U :=
    mem_of_edist_lt_top isClosed_connectedComponent g pU.2
      (hx.trans (ENNReal.ofReal_lt_top))
  have hed (x y : U) : gU.edist x y = g.edist x y :=
    edist_subtype_val isClosed_connectedComponent g gU (fun _ _ _ => rfl) x y
  by_cases hn : n = 0
  · subst n
    let : Subsingleton U := Poincare.subsingleton_of_preconnected_euclidean_zero U
    refine ⟨{p}, by simp, ?_⟩
    intro x hx
    have he : x = p := congrArg Subtype.val (Subsingleton.elim (⟨x, hmem x hx⟩ : U) pU)
    refine ⟨p, by simp, ?_⟩
    subst x
    simp only [edist, Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr (mul_pos hl hr)
  · have hnpos : 1 ≤ n := by omega
    have hcU := g.metricComplete_connectedComponentMetric hc p
    let : MetricSpace U := gU.toMetricSpace
    let : ProperSpace U := gU.properSpace_toMetricSpace hcU
    let : SecondCountableTopology U := gU.secondCountableTopology
    have hcompact : IsCompact (closure (gU.ball pU (5 * (2 * r)))) := by
      rw [← gU.toMetricSpace_ball]
      exact (isCompact_closedBall pU (5 * (2 * r))).of_isClosed_subset
        isClosed_closure Metric.closure_ball_subset_closedBall
    have hsecU (x : U) (v w : TangentSpace (𝓡 n) x) :
        -1 ≤ gU.leviCivitaData.sectionalCurvature x v w := by
      rw [sectionalCurvature_connectedComponentMetric]
      exact hsec _ _ _
    obtain ⟨S, _, hcard, _, hcover⟩ := gU.exists_finset_cover_of_precompact_ball
      pU hnpos (show 0 < 2 * r by positivity) (mul_pos hl hr)
      (show l * r ≤ 2 * r by nlinarith) zero_le_one hcompact gU.leviCivitaData
      (fun x _ v => by
        simpa only [mul_one] using
          gU.leviCivitaData.ricci_quadratic_lower_bound_of_sectionalCurvature_lower_bound
            x 1 (hsecU x) v)
    have hratio : modelVolume n 1 (3 * (2 * r)) / modelVolume n 1 (l * r / 2) ≤
        (12 / l) ^ n * Real.exp (6 * (n : ℝ)) := by
      have hb := modelVolume_div_le hnpos zero_le_one
        (show 0 < l * r / 2 by positivity) (show 0 ≤ 3 * (2 * r) by positivity)
      simp only [Real.sqrt_one, one_mul] at hb
      rw [show 3 * (2 * r) / (l * r / 2) = 12 / l by field_simp; ring] at hb
      refine hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
      have hd : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      have h1 := mul_le_mul_of_nonneg_right hd (show 0 ≤ 6 * r by positivity)
      have h2 := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ 6 * (n : ℝ) by positivity)
      nlinarith only [h1, h2]
    refine ⟨S.image Subtype.val,
      (Finset.card_image_le).trans (hcard.trans (Nat.ceil_mono hratio)), ?_⟩
    intro x hx
    let xU : U := ⟨x, hmem x hx⟩
    have hxU : xU ∈ gU.ball pU (2 * r) := by
      change gU.edist pU xU < ENNReal.ofReal (2 * r)
      rw [hed]
      exact hx
    obtain ⟨z, hz, hzx⟩ := mem_iUnion₂.mp (hcover hxU)
    refine ⟨z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
    change gU.edist z xU < ENNReal.ofReal (l * r) at hzx
    simpa only [hed] using hzx

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RiemannianMetric

private theorem modelVolume_four_mul_le_power {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    modelVolume n 1 (4 * r) ≤
      euclideanUnitBallVolume n * 4 ^ n * Real.exp (4 * (n : ℝ)) * r ^ n := by
  have h := modelVolume_le_exp_mul_zero (n := n) (κ := 1)
    zero_le_one (by positivity : 0 ≤ 4 * r)
  rw [modelVolume_zero_curvature hn] at h
  simp only [Real.sqrt_one, one_mul] at h
  have hnr : ((n - 1 : ℕ) : ℝ) * (4 * r) ≤ 4 * (n : ℝ) := by
    have hdim : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    have h1 := mul_le_mul_of_nonneg_right hdim (show 0 ≤ 4 * r by positivity)
    have h2 := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ 4 * (n : ℝ) by positivity)
    nlinarith only [h1, h2]
  calc
    _ ≤ euclideanUnitBallVolume n * (4 * r) ^ n *
        Real.exp (((n - 1 : ℕ) : ℝ) * (4 * r)) := h
    _ ≤ euclideanUnitBallVolume n * (4 * r) ^ n * Real.exp (4 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hnr)
        (by positivity [euclideanUnitBallVolume_pos n])
    _ = _ := by rw [mul_pow]; ring

private theorem volumeMeasure_real_four_ball_le_power
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w)
    (p : M) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    g.volumeMeasure.real (g.ball p (4 * r)) ≤
      max 1 (euclideanUnitBallVolume n) * 4 ^ n * Real.exp (4 * (n : ℝ)) * r ^ n := by
  let U := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  let gU := g.connectedComponentMetric p
  let pU : U := ⟨p, mem_connectedComponent⟩
  have hvol : gU.volumeMeasure.real (gU.ball pU (4 * r)) =
      g.volumeMeasure.real (g.ball p (4 * r)) :=
    congrArg ENNReal.toReal
      (volumeMeasure_ball_subtype_val isClosed_connectedComponent g gU
        (fun _ _ _ => rfl) pU (4 * r))
  rw [← hvol]
  by_cases hn : n = 0
  · subst n
    let : Subsingleton U := Poincare.subsingleton_of_preconnected_euclidean_zero U
    have hball : gU.ball pU (4 * r) = {pU} := by
      ext x
      have hx : x = pU := Subsingleton.elim _ _
      simp only [hx, ball, Set.mem_ofPred_eq, Set.mem_singleton_iff, edist,
        Manifold.riemannianEDist_self, iff_true]
      exact ENNReal.ofReal_pos.mpr (by positivity)
    have hsingle : gU.volumeMeasure {pU} = 1 := by
      unfold volumeMeasure
      simp only [Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]
    rw [hball]
    simp only [Measure.real, hsingle, ENNReal.toReal_one, Nat.cast_zero, mul_zero,
      Real.exp_zero, pow_zero, mul_one]
    exact le_max_left _ _
  · have hnpos : 1 ≤ n := by omega
    have hsecU (x : U) (v w : TangentSpace (𝓡 n) x) :
        -1 ≤ gU.leviCivitaData.sectionalCurvature x v w := by
      rw [sectionalCurvature_connectedComponentMetric]
      exact hsec _ _ _
    have hb := gU.volumeMeasure_real_ball_le_modelVolume_of_sectional_lower_bound
      pU hnpos (g.metricComplete_connectedComponentMetric hc p) gU.leviCivitaData hsecU
      (show 0 < 4 * r by positivity)
    refine hb.trans ((modelVolume_four_mul_le_power hnpos hr hr1).trans ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
        (Real.exp_pos _).le)
      (pow_nonneg hr.le _)

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RiemannianMetric

private theorem annular_recenter
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {X : Type*} (e : X → M)
    {a : ℝ} (ha : 0 ≤ a) (S : Finset M)
    (hcover : ∀ x, ∃ z ∈ S, g.edist z (e x) < ENNReal.ofReal a) :
    ∃ T : Finset X, T.card ≤ S.card ∧
      ∀ x, ∃ z ∈ T, g.edist (e z) (e x) < ENNReal.ofReal (2 * a) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let A := S.filter (fun z => ∃ x, g.edist z (e x) < ENNReal.ofReal a)
  have hex (z : A) : ∃ x, g.edist z (e x) < ENNReal.ofReal a :=
    (Finset.mem_filter.mp z.2).2
  choose q hq using hex
  refine ⟨Finset.univ.image q, (Finset.card_image_le).trans ?_, ?_⟩
  · simpa using (Finset.card_filter_le (s := S)
      (p := fun z => ∃ x, g.edist z (e x) < ENNReal.ofReal a))
  · intro x
    obtain ⟨z, hz, hzx⟩ := hcover x
    let zA : A := ⟨z, Finset.mem_filter.mpr ⟨hz, x, hzx⟩⟩
    refine ⟨q zA, Finset.mem_image.mpr ⟨zA, Finset.mem_univ _, rfl⟩, ?_⟩
    have hqz : g.edist (e (q zA)) z < ENNReal.ofReal a := by
      simpa only [edist, Manifold.riemannianEDist_comm] using hq zA
    rw [show 2 * a = a + a by ring, ENNReal.ofReal_add ha ha]
    exact lt_of_le_of_lt Manifold.riemannianEDist_triangle (ENNReal.add_lt_add hqz hzx)

end PoincareConjecture.RiemannianMetric



theorem PoincareConjecture.RiemannianMetric.strainer_openFiber_total_volume_le_annular_mul_pow
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m + k) M)
    (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 (m + k)) x), -1 ≤ D.sectionalCurvature x v w)
    (f : Fin k → M → ℝ)
    (w : ∀ x : M, Fin k → TangentSpace (𝓡 (m + k)) x)
    (hf : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (U : Opens M) {δ H η r : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (8 * ((k : ℝ) + 1))) (hHnonneg : 0 ≤ H)
    (hunit : ∀ x ∈ U, ∀ i, g.tangentNorm x (g.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (w x i) ≤ 1)
    (hopposite : ∀ x ∈ U, ∀ i,
      g.inner x (g.gradient (f i) x) (w x i) ≤ -1 + 2 * δ)
    (hcross : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (g.gradient (f i) x) (g.gradient (f j) x) ≤ 0)
    (hH : ∀ x ∈ U, ∀ i v, D.hessian (f i) x v v ≤ (H / r) * g.inner x v v)
    (p : M) (hr : 0 < r) (hr1 : r ≤ 1) (hη : 0 < η) :
    let F := fun y i => f i y
    let hF : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ F :=
      contMDiff_pi_space.mpr hf
    ∃ hreg : ∀ x ∈ U, Surjective
        (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) F x),
      ∀ c : Fin k → ℝ,
        (∀ x ∈ U, F x = c → g.edist p x < ENNReal.ofReal (2 * r)) →
        (∀ x ∈ U, F x = c → ∀ y,
          g.edist x y ≤ ENNReal.ofReal (η * r) → y ∈ U) →
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI := openFiberChartedSpace (m := m) hF U hreg c
        letI := isManifold_openFiber (m := m) hF U hreg c
        let gL := g.openRegularFiberMetric hF U hreg c
        IsCompact (Set.univ : Set (openFiber F U c)) ∧
          gL.volumeMeasure.real Set.univ ≤
            PoincareConjecture.RiemannianMetric.annularCornerVolumeConstant m k H η * r ^ m := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + k)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let F := fun y i => f i y
  let hF : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ F :=
    contMDiff_pi_space.mpr hf
  have hb := Poincare.CurvatureIntegral.strainer_parameter_bounds k hδ hsmall
  let hreg := g.strainer_openFiber_regular f hf U w hδ hb.1 hb.2
    (fun x hx i => (hunit x hx i).2) hopposite hcross
  refine ⟨hreg, ?_⟩
  intro c hbounded hbuffer
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hF U hreg c
  let := isManifold_openFiber (m := m) hF U hreg c
  let gL := g.openRegularFiberMetric hF U hreg c
  let incl := openFiberIncl F U c
  let l : ℝ := min (1 / 4) (η / 4)
  have hl : 0 < l := lt_min (by norm_num) (by positivity)
  have hl1 : l ≤ 1 / 4 := min_le_left _ _
  have hlη : 3 * l ≤ η := by
    have h := min_le_right (1 / 4 : ℝ) (η / 4)
    dsimp only [l]
    linarith
  have hroom : 3 * l * r ≤ η * r := mul_le_mul_of_nonneg_right hlη hr.le
  have hroom' : 2 * l * r ≤ η * r := by nlinarith
  obtain ⟨A, hAcard, hAcover⟩ := PoincareConjecture.RiemannianMetric.annular_cover
    g D hc hsec p hr hr1 hl hl1
  obtain ⟨T, hTcard, hTcover⟩ := PoincareConjecture.RiemannianMetric.annular_recenter
    g incl (show 0 ≤ l * r by positivity) A
    (fun x => hAcover (incl x) (hbounded _ x.1.2 x.2))
  let E (z : openFiber F U c) : Set (openFiber F U c) :=
    {x | g.edist (incl z) (incl x) ≤ ENNReal.ofReal (2 * l * r)}
  have hcompact (z : openFiber F U c) : IsCompact (E z) := by
    apply (isEmbedding_openFiberIncl F U c).isCompact_iff.mpr
    have he : incl '' E z =
        {y | g.edist (incl z) y ≤ ENNReal.ofReal (2 * l * r)} ∩ F ⁻¹' {c} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, x.2⟩
      · rintro ⟨hy, hfy⟩
        have hyU := hbuffer _ z.1.2 z.2 y
          (hy.trans (ENNReal.ofReal_le_ofReal hroom'))
        exact ⟨⟨⟨y, hyU⟩, hfy⟩, hy, rfl⟩
    change IsCompact (incl '' E z)
    rw [he]
    exact (g.isCompact_closedBall_of_metricComplete hc (incl z) (2 * l * r)).inter_right
      (isClosed_singleton.preimage hF.continuous)
  have hcover : (Set.univ : Set (openFiber F U c)) = ⋃ z ∈ T, E z := by
    ext x
    simp only [Set.mem_univ, true_iff]
    obtain ⟨z, hz, hzx⟩ := hTcover x
    exact mem_iUnion₂.mpr ⟨z, hz, by
      change g.edist (incl z) (incl x) ≤ ENNReal.ofReal (2 * l * r)
      simpa only [mul_assoc] using hzx.le⟩
  refine ⟨by rw [hcover]; exact T.isCompact_biUnion (fun z _ => hcompact z), ?_⟩
  let B : ℝ := (2 * ((k : ℝ) + 1) / l) ^ k *
    max 1 (PoincareConjecture.RiemannianMetric.euclideanUnitBallVolume (m + k)) *
      4 ^ (m + k) * Real.exp (((m + k : ℕ) : ℝ) * (H + 4))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlocal (z : openFiber F U c) : gL.volumeMeasure.real (E z) ≤ B * r ^ m := by
    have hbuffer' : ∀ y, g.edist (incl z) y ≤ ENNReal.ofReal (3 * (2 * l * r) / 2) →
        y ∈ U := by
      intro y hy
      apply hbuffer _ z.1.2 z.2 y
      exact hy.trans (ENNReal.ofReal_le_ofReal (by nlinarith : 3 * (2 * l * r) / 2 ≤ η * r))
    obtain ⟨hreg', hb⟩ := g.strainer_openFiber_volume_le_on_ambient_closedBall
      D hc f w hf U hδ hsmall (div_nonneg hHnonneg hr.le)
      hunit hopposite hcross htight hH (incl z)
      (show 0 < 2 * l * r by positivity) hbuffer'
    have hv := hb c
    change gL.volumeMeasure.real (E z) ≤
      (4 * ((k : ℝ) + 1) / (2 * l * r)) ^ k *
        Real.exp (2 * ((m + k : ℕ) : ℝ) * (H / r) * (2 * l * r)) *
        g.volumeMeasure.real {y | g.edist (incl z) y ≤
          ENNReal.ofReal (3 * (2 * l * r) / 2)} at hv
    have hamb : g.volumeMeasure.real {y | g.edist (incl z) y ≤
        ENNReal.ofReal (3 * (2 * l * r) / 2)} ≤
        max 1 (PoincareConjecture.RiemannianMetric.euclideanUnitBallVolume (m + k)) *
          4 ^ (m + k) * Real.exp (4 * ((m + k : ℕ) : ℝ)) * r ^ (m + k) := by
      refine (ENNReal.toReal_mono (g.volumeMeasure_ball_lt_top hc p (4 * r)).ne
        (measure_mono ?_)).trans
          (PoincareConjecture.RiemannianMetric.volumeMeasure_real_four_ball_le_power g D hc hsec p hr hr1)
      intro y hy
      have hz := hbounded _ z.1.2 z.2
      have hy' : g.edist (incl z) y < ENNReal.ofReal (2 * r) :=
        hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr
          (by nlinarith : 3 * (2 * l * r) / 2 < 2 * r))
      change g.edist p y < ENNReal.ofReal (4 * r)
      rw [show 4 * r = 2 * r + 2 * r by ring,
        ENNReal.ofReal_add (by positivity) (by positivity)]
      exact lt_of_le_of_lt Manifold.riemannianEDist_triangle (ENNReal.add_lt_add hz hy')
    have heq : 2 * ((m + k : ℕ) : ℝ) * (H / r) * (2 * l * r) =
        4 * ((m + k : ℕ) : ℝ) * H * l := by field_simp; ring
    have hexp : Real.exp (2 * ((m + k : ℕ) : ℝ) * (H / r) * (2 * l * r)) ≤
        Real.exp (((m + k : ℕ) : ℝ) * H) := by
      apply Real.exp_le_exp.mpr
      rw [heq]
      have hx := mul_le_mul_of_nonneg_left hl1
        (show 0 ≤ 4 * ((m + k : ℕ) : ℝ) * H by positivity)
      nlinarith only [hx]
    have hprod := mul_le_mul
      (mul_le_mul_of_nonneg_left hexp
        (show 0 ≤ (4 * ((k : ℝ) + 1) / (2 * l * r)) ^ k by positivity))
      hamb ENNReal.toReal_nonneg (by positivity)
    refine hv.trans (hprod.trans_eq ?_)
    dsimp only [B]
    rw [show 4 * ((k : ℝ) + 1) / (2 * l * r) =
      (2 * ((k : ℝ) + 1) / l) / r by field_simp; ring]
    rw [show ((m + k : ℕ) : ℝ) * (H + 4) =
      ((m + k : ℕ) : ℝ) * H + 4 * ((m + k : ℕ) : ℝ) by ring,
      Real.exp_add, div_pow, pow_add]
    field_simp
    ring
  have hsum := measureReal_biUnion_finset_le (μ := gL.volumeMeasure) T E
  rw [← hcover] at hsum
  refine hsum.trans ((Finset.sum_le_sum (fun z _ => hlocal z)).trans ?_)
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (T.card : ℝ) ≤
      (⌈(12 / l) ^ (m + k) * Real.exp (6 * ((m + k : ℕ) : ℝ))⌉₊ : ℝ) :=
    by exact_mod_cast hTcard.trans hAcard
  refine (mul_le_mul_of_nonneg_right hcard (mul_nonneg hB (pow_nonneg hr.le m))).trans_eq ?_
  dsimp only [PoincareConjecture.RiemannianMetric.annularCornerVolumeConstant, B, l]
  ring
