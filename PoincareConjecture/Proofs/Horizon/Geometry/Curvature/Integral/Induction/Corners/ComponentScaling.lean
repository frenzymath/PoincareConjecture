import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Scaling
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.WeightedSimilarity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberScaling
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Similarity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology Bundle

private theorem PoincareConjecture.rescaledMetric_closedBall_iff
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {a : ℝ} (ha : 0 < a) (p x : M) (r : ℝ) :
    (rescaledMetric g a ha).edist p x ≤ ENNReal.ofReal (Real.sqrt a * r) ↔
      g.edist p x ≤ ENNReal.ofReal r := by
  rw [rescaledMetric_edist, ENNReal.ofReal_mul (Real.sqrt_nonneg a)]
  rw [mul_comm (ENNReal.ofReal (Real.sqrt a)) (g.edist p x),
    mul_comm (ENNReal.ofReal (Real.sqrt a)) (ENNReal.ofReal r)]
  exact ENNReal.mul_le_mul_iff_left (by positivity) ENNReal.ofReal_ne_top

private theorem PoincareConjecture.LeviCivitaData.scalar_integral_le_of_inverse_square_similarity
    {n : ℕ} (hn : 2 ≤ n) {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N] [T3Space M] [T3Space N]
    [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    {g : PoincareConjecture.RiemannianMetric n M} {h : PoincareConjecture.RiemannianMetric n N}
    (D : PoincareConjecture.LeviCivitaData g) (D' : PoincareConjecture.LeviCivitaData h)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N) {t C : ℝ} (ht : 0 < t)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      h.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w) = (t^2)⁻¹ * g.inner x v w)
    (K : M → ℝ)
    (hbound : (∫ y, max 0 (D'.scalarCurvature y) ∂h.volumeMeasure) ≤
      C*(1+∫ y, t^2*K (e.symm y) ∂h.volumeMeasure)) :
    (∫ x, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      C*(t^(n-2)+∫ x, K x ∂g.volumeMeasure) := by
  have ha : 0 < (t^2)⁻¹ := by positivity
  have hsqrt : Real.sqrt ((t^2)⁻¹) = t⁻¹ := by
    rw [Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos ht]
  have hfactor : (Real.sqrt ((t^2)⁻¹))^n / (t^2)⁻¹ = (t^(n-2))⁻¹ := by
    calc
      _ = (Real.sqrt ((t^2)⁻¹))^(n-2) := by
        rw [pow_sub₀ _ (Real.sqrt_pos.mpr ha).ne' hn, Real.sq_sqrt ha.le, div_eq_mul_inv]
      _ = _ := by rw [hsqrt, inv_pow]
  have hSc := D.setIntegral_pos_scalarCurvature_eq_of_metric_similarity D' e ha hmetric univ
  have hK := g.setIntegral_scaled_weight_eq_of_metric_similarity h e ha hmetric K univ
  have heuniv : e '' (univ : Set M) = univ :=
    Set.image_univ.trans (Set.range_eq_univ.mpr e.surjective)
  simp only [heuniv, MeasureTheory.setIntegral_univ, hfactor, inv_inv] at hSc hK
  rw [hSc, hK] at hbound
  have hp : 0 < t^(n-2) := by positivity
  have hm := mul_le_mul_of_nonneg_left hbound hp.le
  have hi : t^(n-2) * (t^(n-2))⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  calc
    (∫ x, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) =
        t^(n-2)*((t^(n-2))⁻¹*(∫ x, max 0 (D.scalarCurvature x) ∂g.volumeMeasure)) := by
          rw [← mul_assoc, hi, one_mul]
    _ ≤ t^(n-2)*(C*(1+(t^(n-2))⁻¹*∫ x, K x ∂g.volumeMeasure)) := hm
    _ = _ := by rw [mul_add, mul_one]; field_simp

theorem PoincareConjecture.RiemannianMetric.openFiber_scalar_integral_le_of_normalized_corner_bound
    {m k : ℕ} (hm : 2 ≤ m) {M : Type*}
    [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M]
    [IsManifold (𝓡 (m+k)) ∞ M]
    {δ H η Λ C₀ : ℝ} (_hδ : 0 ≤ δ) (_hsmall : δ ≤ 1/(256*((k:ℝ)+1)^2))
    (_hH : 0 ≤ H) (hη : 0 < η) (hΛ : 0 < Λ) (_hC₀ : 0 ≤ C₀)
    (hIH : ∀ (G : PoincareConjecture.RiemannianMetric (m+k) M)
      (DG : PoincareConjecture.LeviCivitaData G),
      PoincareConjecture.MetricComplete G →
      (∀ x (v w : TangentSpace (𝓡 (m+k)) x), -1 ≤ DG.sectionalCurvature x v w) →
      ∀ (f' h' : Fin k → M → ℝ)
        (hf' : ∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ (f' i))
        (_hh' : ∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ (h' i)) (V : Opens M),
      (∀ x ∈ V, ∀ i,
        G.tangentNorm x (DG.gradient (f' i) x) ≤ 1 ∧
        G.tangentNorm x (DG.gradient (h' i) x) ≤ 1) →
      (∀ x ∈ V, ∀ i,
        G.inner x (DG.gradient (f' i) x) (DG.gradient (h' i) x) ≤ -1+2*δ) →
      (∀ x ∈ V, ∀ i j, i ≠ j →
        |G.inner x (DG.gradient (f' i) x) (DG.gradient (f' j) x)| ≤ δ ∧
        |G.inner x (DG.gradient (f' i) x) (DG.gradient (h' j) x)| ≤ δ ∧
        |G.inner x (DG.gradient (h' i) x) (DG.gradient (f' j) x)| ≤ δ ∧
        |G.inner x (DG.gradient (h' i) x) (DG.gradient (h' j) x)| ≤ δ) →
      (∀ x ∈ V, ∀ i j, i ≠ j →
        G.inner x (DG.gradient (f' i) x) (DG.gradient (f' j) x) ≤ 0) →
      (∀ x ∈ V, ∀ i z,
        DG.hessian (f' i) x z z ≤ (Λ*H)*G.inner x z z ∧
        DG.hessian (h' i) x z z ≤ (Λ*H)*G.inner x z z) →
      let F' := fun x i => f' i x
      let hF' : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ F' := contMDiff_pi_space.mpr hf'
      ∀ (hreg' : ∀ x ∈ V, Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) F' x))
        (c' : Fin k → ℝ),
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
        ⟨finrank_euclideanSpace_fin⟩
      letI := openFiberChartedSpace (m := m) hF' V hreg' c'
      letI := isManifold_openFiber (m := m) hF' V hreg' c'
      let L' := openFiber F' V c'
      let incl' := openFiberIncl F' V c'
      let gL' := G.openRegularFiberMetric hF' V hreg' c'
      CompactSpace L' → ConnectedSpace L' → PoincareConjecture.MetricComplete gL' →
      (∀ x y : L', gL'.edist x y ≤ 1) →
      (∀ x : L', ∀ y : M, G.edist (incl' x) y ≤ ENNReal.ofReal (η/Λ) → y ∈ V) →
      ∀ K' : L' → ℝ, Continuous K' → (∀ x, 0 ≤ K' x) →
      (∀ x (v w : TangentSpace (𝓡 m) x),
        -K' x ≤ gL'.leviCivitaData.sectionalCurvature x v w) →
      (∫ x, max 0 (gL'.leviCivitaData.scalarCurvature x) ∂gL'.volumeMeasure) ≤
        C₀*(1+∫ x, K' x ∂gL'.volumeMeasure))
    (g : PoincareConjecture.RiemannianMetric (m+k) M)
    (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 (m+k)) x), -1 ≤ D.sectionalCurvature x v w)
    (f h : Fin k → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ (h i))
    (U : Opens M) {r : ℝ} (hr : 0 < r) (hscale : Λ*r ≤ 1)
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
      D.hessian (f i) x z z ≤ (H/r)*g.inner x z z ∧
      D.hessian (h i) x z z ≤ (H/r)*g.inner x z z) :
    let F := fun x i => f i x
    let hF : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ F := contMDiff_pi_space.mpr hf
    ∀ (hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) F x))
      (c : Fin k → ℝ),
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
        ⟨finrank_euclideanSpace_fin⟩
      letI := openFiberChartedSpace (m := m) hF U hreg c
      letI := isManifold_openFiber (m := m) hF U hreg c
      let L := openFiber F U c
      let incl := openFiberIncl F U c
      let gL := g.openRegularFiberMetric hF U hreg c
      CompactSpace L → ConnectedSpace L →
      (∀ x y : L, gL.edist x y ≤ ENNReal.ofReal (Λ*r)) →
      (∀ x : L, ∀ y : M, g.edist (incl x) y ≤ ENNReal.ofReal (η*r) → y ∈ U) →
      ∀ K : L → ℝ, Continuous K → (∀ x, 0 ≤ K x) →
      (∀ x (v w : TangentSpace (𝓡 m) x),
        -K x ≤ gL.leviCivitaData.sectionalCurvature x v w) →
      (∫ x, max 0 (gL.leviCivitaData.scalarCurvature x) ∂gL.volumeMeasure) ≤
        C₀*((Λ*r)^(m-2)+∫ x, K x ∂gL.volumeMeasure) := by
  classical
  dsimp only
  let F := fun x i => f i x
  let hF : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ F := contMDiff_pi_space.mpr hf
  intro hreg c
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hF U hreg c
  let := isManifold_openFiber (m := m) hF U hreg c
  let L := openFiber F U c
  let incl := openFiberIncl F U c
  let gL := g.openRegularFiberMetric hF U hreg c
  intro hcompact hconnected hdiam hbuffer K hK hKnonneg hKsec
  let : CompactSpace L := hcompact
  let : ConnectedSpace L := hconnected
  let t := Λ*r
  let a := (t^2)⁻¹
  have ht : 0 < t := mul_pos hΛ hr
  have ha : 0 < a := by dsimp [a]; positivity
  have hsqrt : Real.sqrt a = t⁻¹ := by
    dsimp [a]
    rw [Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos ht]
  have ha1 : 1 ≤ a := by
    apply (one_le_inv₀ (by positivity : 0 < t^2)).mpr
    have ht1 : t ≤ 1 := hscale
    nlinarith [sq_nonneg (t-1)]
  let G := PoincareConjecture.rescaledMetric g a ha
  let DG := PoincareConjecture.rescaledMetric_connection g D a ha
  let fs := fun i x => Real.sqrt a*f i x
  let hs := fun i x => Real.sqrt a*h i x
  let Fs := fun x => Real.sqrt a • F x
  let cs := Real.sqrt a • c
  obtain ⟨hFs, hregS, hdata⟩ := g.exists_scaled_openFiber_metric_equivalence hF U hreg c ha
  let := openFiberChartedSpace (m := m) hFs U hregS cs
  let := isManifold_openFiber (m := m) hFs U hregS cs
  let LS := openFiber Fs U cs
  let inclS := openFiberIncl Fs U cs
  let gS := G.openRegularFiberMetric hFs U hregS cs
  obtain ⟨e, hincl, hmetric, hdist, _⟩ := hdata
  let : CompactSpace LS := e.toHomeomorph.compactSpace
  let : ConnectedSpace LS := e.surjective.connectedSpace e.continuous
  have hcS : PoincareConjecture.MetricComplete gS := by
    unfold PoincareConjecture.MetricComplete
    infer_instance
  have hcG : PoincareConjecture.MetricComplete G :=
    PoincareConjecture.metricComplete_rescaledMetric g a ha hc
  have hsecG : ∀ x (v w : TangentSpace (𝓡 (m+k)) x),
      -1 ≤ DG.sectionalCurvature x v w := by
    intro x v w
    change -1 ≤ (PoincareConjecture.rescaledMetric_connection g D a ha).sectionalCurvature x v w
    rw [PoincareConjecture.rescaledMetric_sectionalCurvature]
    have hl := mul_le_mul_of_nonneg_left (hsec x v w) (inv_nonneg.mpr ha.le)
    have hi : a⁻¹ ≤ 1 := (inv_le_one₀ ha).mpr ha1
    nlinarith
  obtain ⟨hfs, hhs, hunitS, hpairS, hcrossS, htightS, hhessS⟩ :=
    D.rescaled_smooth_strainer_pair_bounds f h hf hh hunit hpair hcross htight hhess ha
  have hHscale : (H/r)/Real.sqrt a = Λ*H := by
    rw [hsqrt]
    dsimp [t]
    field_simp
  have hHs : ∀ x ∈ U, ∀ i z,
      DG.hessian (fs i) x z z ≤ (Λ*H)*G.inner x z z ∧
      DG.hessian (hs i) x z z ≤ (Λ*H)*G.inner x z z := by
    intro x hx i z
    have hz := hhessS x hx i z
    rw [hHscale] at hz
    exact hz
  have hdiamS : ∀ x y : LS, gS.edist x y ≤ 1 := by
    intro x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    change gS.edist (e x) (e y) ≤ 1
    rw [hdist]
    have hb : ENNReal.ofReal (Real.sqrt a)*gL.edist x y ≤
        ENNReal.ofReal (Real.sqrt a)*ENNReal.ofReal (Λ*r) := by
      gcongr
      exact hdiam x y
    apply hb.trans
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg a), hsqrt]
    change ENNReal.ofReal (t⁻¹*t) ≤ 1
    rw [inv_mul_cancel₀ ht.ne']
    simp
  have hwidth : Real.sqrt a*(η*r) = η/Λ := by
    rw [hsqrt]
    dsimp [t]
    field_simp
  have hbufferS : ∀ x : LS, ∀ y : M,
      G.edist (inclS x) y ≤ ENNReal.ofReal (η/Λ) → y ∈ U := by
    intro x y hxy
    obtain ⟨x, rfl⟩ := e.surjective x
    change G.edist (inclS (e x)) y ≤ ENNReal.ofReal (η/Λ) at hxy
    have hinc : inclS (e x) = incl x := hincl x
    rw [hinc, ← hwidth] at hxy
    exact hbuffer x y ((PoincareConjecture.rescaledMetric_closedBall_iff g ha (incl x) y (η*r)).mp hxy)
  let KS : LS → ℝ := fun y => t^2*K (e.symm y)
  have hKSc : Continuous KS := continuous_const.mul (hK.comp e.symm.continuous)
  have hKS0 : ∀ y, 0 ≤ KS y := fun y => mul_nonneg (sq_nonneg t) (hKnonneg (e.symm y))
  have hsecS : ∀ x (v w : TangentSpace (𝓡 m) x),
      -KS x ≤ gS.leviCivitaData.sectionalCurvature x v w := by
    simpa only [a, inv_inv] using
      gL.leviCivitaData.sectionalCurvature_lower_bound_of_metric_similarity
        gS.leviCivitaData e ha hmetric hKsec
  have hnormalized := hIH G DG hcG hsecG fs hs hfs hhs U
    hunitS hpairS hcrossS htightS hHs hregS cs
    (inferInstance : CompactSpace LS) (inferInstance : ConnectedSpace LS) hcS
    hdiamS hbufferS KS hKSc hKS0 hsecS
  exact gL.leviCivitaData.scalar_integral_le_of_inverse_square_similarity
    hm gS.leviCivitaData e ht hmetric K hnormalized
