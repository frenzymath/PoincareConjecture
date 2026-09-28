import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.ComponentScaling
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.BufferedComponent
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.StrainerAnnularComponents







open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology Bundle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


set_option linter.unusedVariables false in


theorem PoincareConjecture.RiemannianMetric.strainer_openFiber_component_scalar_bound
    {m k : ℕ} (hm : 2 ≤ m) {M : Type*}
    [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M]
    [IsManifold (𝓡 (m+k)) ∞ M]
    {δ H η C₀ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/(256*((k:ℝ)+1)^2))
    (hH : 0 ≤ H) (hη : 0 < η) (hC₀ : 0 ≤ C₀) :
    let ρ := min 1 (η/80)
    let A := 9*Real.exp (256*H*ρ)
    let q := ρ/(4*A^k)
    let N := ⌈PoincareConjecture.RiemannianMetric.modelVolume (m+k) 1 3 /
      PoincareConjecture.RiemannianMetric.modelVolume (m+k) 1 (q/2)⌉₊
    let Λ := max 1 ((N:ℝ)*ρ)
    let β := min (40*ρ) (q/4)
    ∀(hIH : ∀ (G : PoincareConjecture.RiemannianMetric (m+k) M)
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
      (∀ x : L', ∀ y : M, G.edist (incl' x) y ≤ ENNReal.ofReal (β/Λ) → y ∈ V) →
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
    (U : Opens M) (p : M) {r : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1/2) (hscale : Λ*r ≤ 1)
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
      D.hessian (h i) x z z ≤ (H/r)*g.inner x z z),
    let F := fun x i => f i x
    let hF : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ F := contMDiff_pi_space.mpr hf
    ∃ hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) F x),
      ∀ c : Fin k → ℝ,
      (∀ x ∈ U, F x = c → x ∈ g.ball p (2*r)) →
      (∀ x ∈ U, F x = c → ∀ y : M,
        g.edist x y ≤ ENNReal.ofReal (η*r) → y ∈ U) →
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
        ⟨finrank_euclideanSpace_fin⟩
      letI := openFiberChartedSpace (m := m) hF U hreg c
      letI := isManifold_openFiber (m := m) hF U hreg c
      let L := openFiber F U c
      let gL := g.openRegularFiberMetric hF U hreg c
      IsCompact (univ : Set L) ∧ PoincareConjecture.MetricComplete gL ∧
      Finite (ConnectedComponents L) ∧ Nat.card (ConnectedComponents L) ≤ N ∧
      (∀ x y : L, y ∈ connectedComponent x →
        gL.edist x y ≤ ENNReal.ofReal ((N:ℝ)*ρ*r)) ∧
      ∀ z : L,
        let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin m)) z
        let gC := gL.connectedComponentMetric z
        ∀ K : C → ℝ, Continuous K → (∀ x, 0 ≤ K x) →
        (∀ x (v w : TangentSpace (𝓡 m) x),
          -K x ≤ gC.leviCivitaData.sectionalCurvature x v w) →
        (∫ x, max 0 (gC.leviCivitaData.scalarCurvature x) ∂gC.volumeMeasure) ≤
          C₀*((Λ*r)^(m-2)+∫ x, K x ∂gC.volumeMeasure) := by
  classical
  intro ρ A q N Λ β hIH g D hc hsec f h hf hh U p r hr hrhalf hscale hunit hpair hcross htight hhess F hF
  have hunit₀ : ∀ x ∈ U, ∀ i,
      g.tangentNorm x (g.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (g.gradient (h i) x) ≤ 1 := by
    simpa only [PoincareConjecture.LeviCivitaData.gradient_eq_metric_gradient] using hunit
  have hpair₀ : ∀ x ∈ U, ∀ i,
      g.inner x (g.gradient (f i) x) (g.gradient (h i) x) ≤ -1+2*δ := by
    simpa only [PoincareConjecture.LeviCivitaData.gradient_eq_metric_gradient] using hpair
  have hcross₀ : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ ∧
      |g.inner x (g.gradient (h i) x) (g.gradient (f j) x)| ≤ δ := by
    intro x hx i j hij
    simpa only [PoincareConjecture.LeviCivitaData.gradient_eq_metric_gradient] using
      And.intro (hcross x hx i j hij).1 (hcross x hx i j hij).2.2.1
  have htight₀ : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (g.gradient (f i) x) (g.gradient (f j) x) ≤ 0 := by
    simpa only [PoincareConjecture.LeviCivitaData.gradient_eq_metric_gradient] using htight
  obtain ⟨hreg, hgeo⟩ := g.strainer_openFiber_components_and_diameter_annular D hc
    (by omega) hsec f h hf hh U hδ hsmall hH hunit₀ hpair₀ hcross₀ htight₀
    hr hrhalf hη hhess p
  refine ⟨hreg, ?_⟩
  intro c hinside hbuffer
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hF U hreg c
  let := isManifold_openFiber (m := m) hF U hreg c
  let L := openFiber F U c
  let incl := openFiberIncl F U c
  let gL := g.openRegularFiberMetric hF U hreg c
  obtain ⟨hcompact, hcomplete, hfinite, hcard, hdiam⟩ := hgeo c hinside hbuffer
  refine ⟨hcompact, hcomplete, hfinite, hcard, hdiam, ?_⟩
  let : CompactSpace L := isCompact_univ_iff.mp hcompact
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρη : 80*ρ ≤ η := by
    have hh := min_le_right (1:ℝ) (η/80)
    dsimp only [ρ] at *
    linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hΛ : 0 < Λ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hβ : 0 < β := by dsimp [β]; positivity
  let s := 2*ρ*r
  have hs : 0 < s := by dsimp [s]; positivity
  have hAeq : 9*Real.exp (128*(H/r)*s) = A := by
    congr 2
    dsimp [s]
    field_simp
    ring
  have hqeq : s/(4*(9*Real.exp (128*(H/r)*s))^k) = 2*q*r := by
    rw [hAeq]
    dsimp [s, q]
    ring
  have hwidtheq : min (20*s) ((s/(4*(9*Real.exp (128*(H/r)*s))^k))/8) = β*r := by
    rw [hqeq]
    dsimp only [β]
    rw [min_mul_of_nonneg _ _ hr.le]
    congr 1 <;> ring
  have hbufferS : ∀ x : L, ∀ y : M,
      g.edist (incl x) y ≤ ENNReal.ofReal (40*s) → y ∈ U := by
    intro x y hy
    apply hbuffer (incl x) x.1.2 x.2 y
    apply hy.trans (ENNReal.ofReal_le_ofReal ?_)
    dsimp [s]
    nlinarith [mul_le_mul_of_nonneg_right hρη hr.le]
  obtain ⟨hregB, hcomponents⟩ := g.exists_buffered_strainer_component_restriction
    D hc f h hf hh U hδ hsmall (div_nonneg hH hr.le)
    hunit₀ hpair₀ hcross₀ htight₀ hhess hs
  intro z
  obtain ⟨V, hVU, hVC, hVbuffer, hregV, e, hincl, hconn, hcompactV, hmetric,
    hdist, hmeasure, hscalar, hint⟩ := hcomponents c hbufferS z
  let := openFiberChartedSpace (m := m) hF V hregV c
  let := isManifold_openFiber (m := m) hF V hregV c
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin m)) z
  let gC := gL.connectedComponentMetric z
  let LV := openFiber F V c
  let inclV := openFiberIncl F V c
  let gV := g.openRegularFiberMetric hF V hregV c
  dsimp only
  intro K hK hKnonneg hKsec
  let : ConnectedSpace LV := hconn
  let : CompactSpace LV := hcompactV isClosed_connectedComponent.isCompact
  have hdistC (x y : C) : gC.edist x y = gL.edist x.val y.val :=
    PoincareConjecture.RiemannianMetric.edist_subtype_val
      isClosed_connectedComponent gL gC (fun _ _ _ => rfl) x y
  have hdiamV : ∀ x y : LV, gV.edist x y ≤ ENNReal.ofReal (Λ*r) := by
    intro x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    change gV.edist (e x) (e y) ≤ _
    rw [hdist, hdistC]
    have hy : y.val ∈ connectedComponent x.val := by
      rw [← connectedComponent_eq x.property]
      exact y.property
    apply (hdiam x.val y.val hy).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (le_max_right 1 ((N:ℝ)*ρ)) hr.le
  have hbufferV : ∀ x : LV, ∀ y : M,
      g.edist (inclV x) y ≤ ENNReal.ofReal (β*r) → y ∈ V := by
    intro x y hy
    obtain ⟨x, rfl⟩ := e.surjective x
    have hinc : inclV (e x) = incl x.val := hincl x
    change g.edist (inclV (e x)) y ≤ _ at hy
    rw [hinc, ← hwidtheq] at hy
    exact hVbuffer x.val x.property y hy
  let KV : LV → ℝ := K ∘ e.symm
  have hKV : Continuous KV := hK.comp e.symm.continuous
  have hKV0 : ∀ x, 0 ≤ KV x := fun x => hKnonneg _
  have hKVsec : ∀ x (v w : TangentSpace (𝓡 m) x),
      -KV x ≤ gV.leviCivitaData.sectionalCurvature x v w := by
    have ht := gC.leviCivitaData.sectionalCurvature_lower_bound_of_metric_similarity
      gV.leviCivitaData e (by norm_num : 0 < (1:ℝ))
      (by simpa only [one_mul] using hmetric) hKsec
    intro x v w
    simpa only [KV, Function.comp_apply, inv_one, one_mul] using ht x v w
  have hb := g.openFiber_scalar_integral_le_of_normalized_corner_bound hm
    hδ hsmall hH hβ hΛ hC₀ hIH D hc hsec f h hf hh V hr hscale
    (fun x hx => hunit x (hVU hx)) (fun x hx => hpair x (hVU hx))
    (fun x hx => hcross x (hVU hx)) (fun x hx => htight x (hVU hx))
    (fun x hx => hhess x (hVU hx)) hregV c
    (inferInstance : CompactSpace LV) (inferInstance : ConnectedSpace LV)
    hdiamV hbufferV KV hKV hKV0 hKVsec
  have hSc : (∫ y, max 0 (gV.leviCivitaData.scalarCurvature y) ∂gV.volumeMeasure) =
      ∫ x, max 0 (gC.leviCivitaData.scalarCurvature x) ∂gC.volumeMeasure := by
    rw [← hint (fun y => max 0 (gV.leviCivitaData.scalarCurvature y))]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [← hscalar x]
  have hKi : (∫ y, KV y ∂gV.volumeMeasure) = ∫ x, K x ∂gC.volumeMeasure := by
    rw [← hint KV]
    apply integral_congr_ae
    filter_upwards [] with x
    exact congrArg K (e.symm_apply_apply x)
  rw [hSc, hKi] at hb
  exact hb

set_option linter.unusedVariables false in

theorem PoincareConjecture.RiemannianMetric.strainer_openFiber_component_scalar_bound_of_dimension
    {n m k : ℕ} (hdim : n = m+k) (hm : 2 ≤ m) {M : Type*}
    [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {δ H η C₀ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/(256*((k:ℝ)+1)^2))
    (hH : 0 ≤ H) (hη : 0 < η) (hC₀ : 0 ≤ C₀) :
    let ρ := min 1 (η/80)
    let A := 9*Real.exp (256*H*ρ)
    let q := ρ/(4*A^k)
    let N := ⌈PoincareConjecture.RiemannianMetric.modelVolume n 1 3 /
      PoincareConjecture.RiemannianMetric.modelVolume n 1 (q/2)⌉₊
    let Λ := max 1 ((N:ℝ)*ρ)
    let β := min (40*ρ) (q/4)
    ∀(hIH : ∀ (G : PoincareConjecture.RiemannianMetric n M)
      (DG : PoincareConjecture.LeviCivitaData G),
      PoincareConjecture.MetricComplete G →
      (∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ DG.sectionalCurvature x v w) →
      ∀ (f' h' : Fin k → M → ℝ)
        (hf' : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (f' i))
        (_hh' : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (h' i)) (V : Opens M),
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
      let hF' : ContMDiff (𝓡 n) 𝓘(ℝ,Fin k → ℝ) ∞ F' := contMDiff_pi_space.mpr hf'
      ∀ (hreg' : ∀ x ∈ V, Surjective (mfderiv (𝓡 n) 𝓘(ℝ,Fin k → ℝ) F' x))
        (c' : Fin k → ℝ),
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = m+k) :=
        ⟨by simpa only [hdim] using
        (finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)⟩
      letI := openFiberChartedSpace (m := m) hF' V hreg' c'
      letI := isManifold_openFiber (m := m) hF' V hreg' c'
      let L' := openFiber F' V c'
      let incl' := openFiberIncl F' V c'
      let gL' : PoincareConjecture.RiemannianMetric m L' := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric G
        (openFiberIncl F' V c') (contMDiff_openFiberIncl (m := m) hF' V hreg' c')
        (injective_mfderiv_openFiberIncl (m := m) hF' V hreg' c')
      CompactSpace L' → ConnectedSpace L' → PoincareConjecture.MetricComplete gL' →
      (∀ x y : L', gL'.edist x y ≤ 1) →
      (∀ x : L', ∀ y : M, G.edist (incl' x) y ≤ ENNReal.ofReal (β/Λ) → y ∈ V) →
      ∀ K' : L' → ℝ, Continuous K' → (∀ x, 0 ≤ K' x) →
      (∀ x (v w : TangentSpace (𝓡 m) x),
        -K' x ≤ gL'.leviCivitaData.sectionalCurvature x v w) →
      (∫ x, max 0 (gL'.leviCivitaData.scalarCurvature x) ∂gL'.volumeMeasure) ≤
        C₀*(1+∫ x, K' x ∂gL'.volumeMeasure))
    (g : PoincareConjecture.RiemannianMetric n M)
    (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w)
    (f h : Fin k → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (h i))
    (U : Opens M) (p : M) {r : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1/2) (hscale : Λ*r ≤ 1)
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
      D.hessian (h i) x z z ≤ (H/r)*g.inner x z z),
    let F := fun x i => f i x
    let hF : ContMDiff (𝓡 n) 𝓘(ℝ,Fin k → ℝ) ∞ F := contMDiff_pi_space.mpr hf
    ∃ hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 n) 𝓘(ℝ,Fin k → ℝ) F x),
      ∀ c : Fin k → ℝ,
      (∀ x ∈ U, F x = c → x ∈ g.ball p (2*r)) →
      (∀ x ∈ U, F x = c → ∀ y : M,
        g.edist x y ≤ ENNReal.ofReal (η*r) → y ∈ U) →
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = m+k) :=
        ⟨by simpa only [hdim] using
        (finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)⟩
      letI := openFiberChartedSpace (m := m) hF U hreg c
      letI := isManifold_openFiber (m := m) hF U hreg c
      let L := openFiber F U c
      let gL : PoincareConjecture.RiemannianMetric m L := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
        (openFiberIncl F U c) (contMDiff_openFiberIncl (m := m) hF U hreg c)
        (injective_mfderiv_openFiberIncl (m := m) hF U hreg c)
      IsCompact (univ : Set L) ∧ PoincareConjecture.MetricComplete gL ∧
      Finite (ConnectedComponents L) ∧ Nat.card (ConnectedComponents L) ≤ N ∧
      (∀ x y : L, y ∈ connectedComponent x →
        gL.edist x y ≤ ENNReal.ofReal ((N:ℝ)*ρ*r)) ∧
      ∀ z : L,
        let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin m)) z
        let gC := gL.connectedComponentMetric z
        ∀ K : C → ℝ, Continuous K → (∀ x, 0 ≤ K x) →
        (∀ x (v w : TangentSpace (𝓡 m) x),
          -K x ≤ gC.leviCivitaData.sectionalCurvature x v w) →
        (∫ x, max 0 (gC.leviCivitaData.scalarCurvature x) ∂gC.volumeMeasure) ≤
          C₀*((Λ*r)^(m-2)+∫ x, K x ∂gC.volumeMeasure) := by
  subst n
  exact PoincareConjecture.RiemannianMetric.strainer_openFiber_component_scalar_bound
    hm hδ hsmall hH hη hC₀
