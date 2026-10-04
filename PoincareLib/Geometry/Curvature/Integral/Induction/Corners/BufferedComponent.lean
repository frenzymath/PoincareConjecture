import PoincareLib.Geometry.Curvature.Integral.Induction.Corners.ComponentRegion
import PoincareLib.Geometry.Curvature.Integral.Induction.Corners.LocalDistance
import PoincareLib.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareLib.Topology.MetricSpace.SeparatedNeighborhood

/-!
# Uniform ambient neighborhoods of strainer fiber components

The actual local-distance estimate separates distinct components. Restricting
to a quantitative neighborhood of one component preserves both its induced
geometry and a uniform ambient buffer for subsequent corner induction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology Bundle

/-- Isolate an actual strainer-fiber component using unchanged equations while
retaining a uniform ambient closed-ball buffer and its full induced geometry. -/
theorem PoincareMT.RiemannianMetric.exists_buffered_strainer_component_restriction
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareMT.RiemannianMetric (m + k) M) (D : PoincareMT.LeviCivitaData g) (hc : PoincareMT.MetricComplete g)
    (f h : Fin k → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (h i))
    (U : Opens M) {δ C : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (256 * ((k : ℝ) + 1) ^ 2)) (hC : 0 ≤ C)
    (hunit : ∀ x ∈ U, ∀ i,
      g.tangentNorm x (g.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (g.gradient (h i) x) ≤ 1)
    (hopposite : ∀ x ∈ U, ∀ i,
      g.inner x (g.gradient (f i) x) (g.gradient (h i) x) ≤ -1 + 2 * δ)
    (hcross : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ ∧
      |g.inner x (g.gradient (h i) x) (g.gradient (f j) x)| ≤ δ)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (g.gradient (f i) x) (g.gradient (f j) x) ≤ 0)
    (hH : ∀ x ∈ U, ∀ i w,
      D.hessian (f i) x w w ≤ C * g.inner x w w ∧
      D.hessian (h i) x w w ≤ C * g.inner x w w) {r : ℝ} (hr : 0 < r) :
    let A := 9 * Real.exp (128*C*r)
    let q := r / (4 * A ^ k)
    let F := fun y i => f i y
    let hF : ContMDiff (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) ∞ F :=
      contMDiff_pi_space.mpr hf
    ∃ hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) F x),
      ∀ c : Fin k → ℝ,
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI := openFiberChartedSpace (m := m) hF U hreg c
        letI := isManifold_openFiber (m := m) hF U hreg c
        let gL := g.openRegularFiberMetric hF U hreg c
        let incl := openFiberIncl F U c
        (∀ x : openFiber F U c, ∀ y : M,
          g.edist (incl x) y ≤ ENNReal.ofReal (40*r) → y ∈ U) →
        ∀ p : openFiber F U c, ∃ V : Opens M,
      (V : Set M) ⊆ U ∧ incl ⁻¹' (V : Set M) = connectedComponent p ∧
      (∀ x ∈ connectedComponent p, ∀ y : M,
        g.edist (incl x) y ≤ ENNReal.ofReal (min (20*r) (q/8)) → y ∈ V) ∧
      ∃ hregV : ∀ x ∈ V, Function.Surjective
        (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) F x),
        letI := openFiberChartedSpace (m := m) hF V hregV c
        letI := isManifold_openFiber (m := m) hF V hregV c
        let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin m)) p
        let gC := gL.connectedComponentMetric p
        let gV := g.openRegularFiberMetric hF V hregV c
        ∃ e : C ≃ₘ⟮𝓡 m, 𝓡 m⟯ openFiber F V c,
          (∀ x : C, openFiberIncl F V c (e x) = incl x.val) ∧
          ConnectedSpace (openFiber F V c) ∧
          (IsCompact (connectedComponent p) → CompactSpace (openFiber F V c)) ∧
          (∀ (x : C) (v w : TangentSpace (𝓡 m) x),
            gV.inner (e x) (mfderiv (𝓡 m) (𝓡 m) e x v)
              (mfderiv (𝓡 m) (𝓡 m) e x w) = gC.inner x v w) ∧
          (∀ x y : C, gV.edist (e x) (e y) = gC.edist x y) ∧
          MeasurePreserving e gC.volumeMeasure gV.volumeMeasure ∧
          (∀ x : C, gC.leviCivitaData.scalarCurvature x =
            gV.leviCivitaData.scalarCurvature (e x)) ∧
          ∀ F : openFiber F V c → ℝ,
            (∫ x, F (e x) ∂gC.volumeMeasure) = ∫ y, F y ∂gV.volumeMeasure := by
  classical
  let A := 9 * Real.exp (128*C*r)
  let q := r / (4*A^k)
  let F := fun y i => f i y
  let hF : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ F := contMDiff_pi_space.mpr hf
  obtain ⟨hreg, hlocal⟩ :=
    g.strainer_openFiber_edist_le_of_ambient_closedBall D hc f h hf hh U
      hδ hsmall hC hunit hopposite hcross htight hH hr
  refine ⟨hreg, ?_⟩
  intro c
  dsimp only
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hF U hreg c
  let := isManifold_openFiber (m := m) hF U hreg c
  let L := openFiber F U c
  let incl := openFiberIncl F U c
  intro hbuffer p
  let := g.toMetricSpace
  let E : Set M := Set.range incl
  let S : Set M := incl '' connectedComponent p
  have hA : 0 < A := by dsimp [A]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hSU : S ⊆ U := by rintro x ⟨y, hy, rfl⟩; exact y.1.2
  have hSE : S ⊆ E := image_subset_range _ _
  have hsep : ∀ x ∈ S, ∀ y ∈ E, dist x y < q → y ∈ S := by
    rintro x ⟨xL, hxL, rfl⟩ y ⟨yL, rfl⟩ hxy
    have hscaled : ENNReal.ofReal (A^k) * g.edist (incl xL) (incl yL) <
        ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_toReal (g.edist_ne_top (incl xL) (incl yL)),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ A^k)]
      apply (ENNReal.ofReal_lt_ofReal_iff hr).mpr
      change A^k * dist (incl xL) (incl yL) < r
      have hb := (lt_div_iff₀ (by positivity : 0 < 4*A^k)).mp hxy
      nlinarith
    have hj := (hlocal c xL yL (hbuffer xL) hscaled).2
    refine ⟨yL, ?_, rfl⟩
    rw [connectedComponent_eq hxL]
    exact pathComponent_subset_component xL hj
  have hb : ∀ x ∈ S, Metric.closedBall x (40*r) ⊆ U := by
    rintro x ⟨xL, hxL, rfl⟩
    rw [g.toMetricSpace_closedBall (incl xL) (by positivity)]
    exact hbuffer xL
  obtain ⟨Vset, hVo, hVU, hVE, hVbuffer⟩ :=
    Metric.exists_open_neighborhood_inter_eq_of_separated U.isOpen hSE hSU
      (by positivity : 0 < 40*r) hq hsep hb
  let V : Opens M := ⟨Vset, hVo⟩
  have hVC : incl ⁻¹' (V : Set M) = connectedComponent p := by
    ext x
    constructor
    · intro hx
      have hxS : incl x ∈ S := by rw [← hVE]; exact ⟨hx, mem_range_self x⟩
      obtain ⟨y, hy, hxy⟩ := hxS
      have hyx := (isEmbedding_openFiberIncl F U c).injective hxy
      exact hyx ▸ hy
    · intro hx
      have hxS : incl x ∈ S := ⟨x, hx, rfl⟩
      rw [← hVE] at hxS
      exact hxS.1
  have hregV : ∀ x ∈ V, Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) F x) :=
    fun x hx => hreg x (hVU hx)
  refine ⟨V, hVU, hVC, ?_, hregV,
    g.exists_openFiber_component_equivalence_of_region hF U hreg c p V hVU hVC hregV⟩
  intro x hx y hy
  have hwidth : min (40*r/2) (q/8) = min (20*r) (q/8) := by congr 1; ring
  have hyball : y ∈ Metric.closedBall (incl x) (min (40*r/2) (q/8)) := by
    rw [hwidth, g.toMetricSpace_closedBall (incl x) (by positivity)]
    exact hy
  exact hVbuffer (incl x) ⟨x, hx, rfl⟩ hyball

