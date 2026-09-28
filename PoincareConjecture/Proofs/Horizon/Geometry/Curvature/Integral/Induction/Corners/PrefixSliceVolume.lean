import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.PrefixBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.PrefixVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.SliceVolume







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology



theorem PoincareConjecture.RiemannianMetric.strainer_prefix_volume_le_on_ambient_closedBall
    {d k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin ((d + 1) + k))) M]
    [IsManifold (𝓡 ((d + 1) + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric ((d + 1) + k) M)
    (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (f : Fin (k + 1) → M → ℝ)
    (w : ∀ x : M, Fin (k + 1) → TangentSpace (𝓡 ((d + 1) + k)) x)
    (hf : ∀ i, ContMDiff (𝓡 ((d + 1) + k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (U : Opens M) {δ C : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (8 * ((k : ℝ) + 1))) (hC : 0 ≤ C)
    (hunit : ∀ x ∈ U, ∀ i, g.tangentNorm x (g.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (w x i) ≤ 1)
    (hopposite : ∀ x ∈ U, ∀ i,
      g.inner x (g.gradient (f i) x) (w x i) ≤ -1 + 2 * δ)
    (hcross : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (g.gradient (f i) x) (g.gradient (f j) x) ≤ 0)
    (hH : ∀ x ∈ U, ∀ i v, D.hessian (f i) x v v ≤ C * g.inner x v v)
    (p : M) {r R T : ℝ} (hr : 0 ≤ r) (hT : 0 < T)
    (hroom : r + 4 * T ≤ R)
    (hball : ∀ y, g.edist p y ≤ ENNReal.ofReal R → y ∈ U) :
    let P := fun y (i : Fin k) => f i.castSucc y
    let hP : ContMDiff (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ P :=
      contMDiff_pi_space.mpr (fun i => hf i.castSucc)
    let F := fun y i => f i y
    let hF : ContMDiff (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) ∞ F :=
      contMDiff_pi_space.mpr hf
    ∃ hprefix : ∀ x ∈ U, Surjective
        (mfderiv (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin k → ℝ) P x),
      ∃ hfull : ∀ x ∈ U, Surjective
          (mfderiv (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) F x),
        ∀ c : Fin (k + 1) → ℝ,
          let cP := fun i : Fin k => c i.castSucc
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + k))) =
            (d + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
          letI := openFiberChartedSpace (m := d + 1) hP U hprefix cP
          letI := isManifold_openFiber (m := d + 1) hP U hprefix cP
          let gP := g.openRegularFiberMetric hP U hprefix cP
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + k))) =
            d + (k + 1)) := ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
          letI := openFiberChartedSpace (m := d) hF U hfull c
          letI := isManifold_openFiber (m := d) hF U hfull c
          let gFull := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
            (openFiberIncl F U c)
            (contMDiff_openFiberIncl (m := d) hF U hfull c)
            (injective_mfderiv_openFiberIncl (m := d) hF U hfull c)
          (PoincareConjecture.RiemannianMetric.volumeMeasure gFull).real
              {y | g.edist p (openFiberIncl F U c y) ≤ ENNReal.ofReal r} ≤
            Real.exp (8 * (d : ℝ) * C * T) / T *
              gP.volumeMeasure.real
                {y | g.edist p (openFiberIncl P U cP y) ≤ ENNReal.ofReal (r + 2 * T)} := by
  classical
  let P := fun y (i : Fin k) => f i.castSucc y
  let hP : ContMDiff (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ P :=
    contMDiff_pi_space.mpr (fun i => hf i.castSucc)
  let F := fun y i => f i y
  let hF : ContMDiff (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin (k + 1) → ℝ) ∞ F :=
    contMDiff_pi_space.mpr hf
  obtain ⟨_, hprefix, hbounds⟩ := g.strainer_prefix_openFiber_bounds D f w hf U
    hδ hsmall hC hunit hopposite hcross htight hH
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + k))) =
    (d + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
  let (c : Fin k → ℝ) := openFiberChartedSpace (m := d + 1) hP U hprefix c
  let (c : Fin k → ℝ) := isManifold_openFiber (m := d + 1) hP U hprefix c
  have hlast : ∀ c : Fin k → ℝ, ∀ x : openFiber P U c,
      mfderiv (𝓡 (d + 1)) 𝓘(ℝ, ℝ)
        (f (Fin.last k) ∘ openFiberIncl P U c) x ≠ 0 := by
    intro c x hx
    let gP := g.openRegularFiberMetric hP U hprefix c
    have hz := (gP.gradient_eq_zero_iff_mfderiv_eq_zero _ x).mpr hx
    have hb := ((hbounds c).2 x).1.1
    rw [hz] at hb
    simp only [PoincareConjecture.RiemannianMetric.tangentNorm, map_zero, Real.sqrt_zero] at hb
    norm_num at hb
  obtain ⟨hfull, hvol⟩ := g.exists_prefix_fiber_volume_identity f hf U hprefix hlast
  refine ⟨hprefix, hfull, ?_⟩
  intro c
  let cP := fun i : Fin k => c i.castSucc
  let gP := g.openRegularFiberMetric hP U hprefix cP
  let φP := f (Fin.last k) ∘ openFiberIncl P U cP
  let hφP := (hf (Fin.last k)).comp
    (contMDiff_openFiberIncl (m := d + 1) hP U hprefix cP)
  obtain ⟨hlevel, hvolc⟩ := hvol c
  obtain ⟨hregφ, hslice⟩ :=
    g.openFiber_sliceVolume_le_on_ambient_closedBall hc hP (hf (Fin.last k))
      U hprefix cP p (l := 1 / 2) (H := 2 * C) (by norm_num)
      (by positivity) hr hT (by norm_num; linarith) hball
      (fun x => ((hbounds cP).2 x).1)
      (fun x v _ => ((hbounds cP).2 x).2 v)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + k))) =
    d + (k + 1)) := ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  let := openFiberChartedSpace (m := d) hF U hfull c
  let := isManifold_openFiber (m := d) hF U hfull c
  dsimp only
  refine (le_of_eq (hvolc {y | g.edist p y ≤ ENNReal.ofReal r}).symm).trans ?_
  have hnum : (d : ℝ) * (2 * C) * T / (1 / 2) ^ 2 = 8 * (d : ℝ) * C * T := by ring
  have hrad : r + T / (1 / 2) = r + 2 * T := by ring
  simpa only [hnum, hrad, Set.mem_ofPred_eq, P, cP] using hslice (c (Fin.last k))
