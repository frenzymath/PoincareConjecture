import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.TiltedSlab
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Slab.Summation
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Slab.Coverage
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberCompact
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberOpen

open Set MeasureTheory PoincareConjecture
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem PoincareConjecture.RiemannianMetric.integral_openFiber_pos_scalar_annulus_le_of_tilted_strips
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M] [IsManifold (𝓡 (m+k)) ∞ M]
    (g : RiemannianMetric (m+k) M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (f h : Fin k → M → ℝ) (u : M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ (h i))
    (hu : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ u)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x∈U, Function.Surjective
      (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) (fun y i => f i y) x))
    (c : Fin k → ℝ) (p : openFiber (fun y i => f i y) U c)
    {Δ δ r : ℝ} (hΔ : 0<Δ) (hΔsmall : Δ≤1/(16*((k:ℝ)+1)))
    (hδ : 0≤δ) (hδsmall : δ≤((Δ/(8*((k:ℝ)+1)))/256)^2) (hr : 0<r)
    (hbuffer : ∀ y, g.edist (openFiberIncl (fun y i => f i y) U c p) y≤
      ENNReal.ofReal (4*r) → y∈U)
    (hpair : ∀ i y, y∈U →
      g.tangentNorm y (D.gradient (f i) y)≤1 ∧
      g.tangentNorm y (D.gradient (h i) y)≤1 ∧
      g.inner y (D.gradient (f i) y) (D.gradient (h i) y)≤ -1+2*δ) :
    let ε := Δ/(8*((k:ℝ)+1))
    let σ := ε^2/2048
    let τ := 1/(1+σ^2/8)
    let s := τ*r/1024
    let incl := openFiberIncl (fun y i => f i y) U c
    let p₀ := incl p
    (∀ y, u y∈Ioo (τ*(9*r/8)) (τ*(15*r/8)) →
      r<(g.edist p₀ y).toReal ∧ (g.edist p₀ y).toReal<2*r) →
    (∀ y, (g.edist p₀ y).toReal∈Icc (113*r/96) (19*r/16) →
      |u y-τ*(g.edist p₀ y).toReal|≤τ*(r/65536)) →
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k)))=m+k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) (contMDiff_pi_space.mpr hf) U hreg c
    letI := isManifold_openFiber (m := m) (contMDiff_pi_space.mpr hf) U hreg c
    let L := openFiber (fun y i => f i y) U c
    let gL := g.openRegularFiberMetric (contMDiff_pi_space.mpr hf) U hreg c
    let F := fun y => (1-Δ/4)*u y + ((Δ/4)/((k:ℝ)+1))*∑ i, h i y
    let center := fun t : Icc (7/12:ℝ) (3/5) =>
      (1-Δ/4)*(2*τ*((t:ℝ)*r)) + ((Δ/4)/((k:ℝ)+1))*∑ i, h i p₀
    let S := fun (t : Icc (7/12:ℝ) (3/5)) (b : ℝ) =>
      {x : L | u (incl x)∈Ioo (2*τ*((t:ℝ)*r)-s/4) (2*τ*((t:ℝ)*r)+s/4) ∧
        F (incl x)-center t+s/16∈Icc (3*s/64) b}
    ∀ (K : L → ℝ), Continuous K → (∀ x, 0≤K x) →
    ∀ C : ℝ, 0≤C →
    (∀ t∈Poincare.CurvatureIntegral.normalizedStripCenters,
      (∫ x in S t (5*s/64), max 0 (gL.leviCivitaData.scalarCurvature x)
        ∂gL.volumeMeasure) ≤
        C*(r^(m-2)+∫ x in S t (15*s/128), K x ∂gL.volumeMeasure)) →
    (∫ x in {x : L | (g.edist p₀ (incl x)).toReal∈Icc (113*r/96) (19*r/16)},
      max 0 (gL.leviCivitaData.scalarCurvature x) ∂gL.volumeMeasure) ≤
      (Poincare.CurvatureIntegral.normalizedStripCenters.card:ℝ)*C*
        (r^(m-2)+∫ x in {x : L | (g.edist p₀ (incl x)).toReal∈Icc (r/2) (3*r)},
          K x ∂gL.volumeMeasure) := by
  classical
  dsimp only
  let ε := Δ/(8*((k:ℝ)+1))
  let σ := ε^2/2048
  let τ := 1/(1+σ^2/8)
  let s := τ*r/1024
  let incl := openFiberIncl (fun y i => f i y) U c
  let p₀ := incl p
  intro hband happrox
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k)))=m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) (contMDiff_pi_space.mpr hf) U hreg c
  let := isManifold_openFiber (m := m) (contMDiff_pi_space.mpr hf) U hreg c
  let L := openFiber (fun y i => f i y) U c
  let gL := g.openRegularFiberMetric (contMDiff_pi_space.mpr hf) U hreg c
  let F := fun y => (1-Δ/4)*u y + ((Δ/4)/((k:ℝ)+1))*∑ i, h i y
  let center := fun t : Icc (7/12:ℝ) (3/5) =>
    (1-Δ/4)*(2*τ*((t:ℝ)*r)) + ((Δ/4)/((k:ℝ)+1))*∑ i, h i p₀
  let S := fun (t : Icc (7/12:ℝ) (3/5)) (b : ℝ) =>
    {x : L | u (incl x)∈Ioo (2*τ*((t:ℝ)*r)-s/4) (2*τ*((t:ℝ)*r)+s/4) ∧
      F (incl x)-center t+s/16∈Icc (3*s/64) b}
  intro K hKc hK C hC hbounds
  let : ConnectedSpace M := { toNonempty := ⟨p₀⟩ }
  let := g.toMetricSpace
  let : MetricSpace L :=
    (isEmbedding_openFiberIncl (fun y i => f i y) U c).comapMetricSpace incl
  let d := fun x : L => (g.edist p₀ (incl x)).toReal
  have hd : Continuous d := by
    change Continuous (fun x : L => dist p x)
    fun_prop
  have hτ : 0<τ := by dsimp [τ]; positivity
  have hi : Continuous incl := (isEmbedding_openFiberIncl (fun y i => f i y) U c).continuous
  have hF : Continuous F := by
    dsimp [F]
    exact (continuous_const.mul hu.continuous).add
      (continuous_const.mul (continuous_finsetSum _ (fun i _ => (hh i).continuous)))
  have hSm (t : Icc (7/12:ℝ) (3/5)) (b : ℝ) : MeasurableSet (S t b) := by
    exact ((isOpen_Ioo.preimage (hu.continuous.comp hi)).measurableSet).inter
      (isClosed_Icc.preimage
        (((hF.comp hi).sub continuous_const).add continuous_const)).measurableSet
  have hrad (t : Icc (7/12:ℝ) (3/5)) (b : ℝ) (x : L) (hx : x∈S t b) :
      r<d x ∧ d x<2*r := by
    apply hband (incl x)
    apply Poincare.CurvatureIntegral.normalized_level_strip_subset_slab (t := (t:ℝ)*r) hr hτ
    · constructor <;> nlinarith [mul_le_mul_of_nonneg_right t.property.1 hr.le,
        mul_le_mul_of_nonneg_right t.property.2 hr.le]
    · exact ⟨hx.1.1.le,hx.1.2.le⟩
  have hcompact : IsCompact {x : L | d x≤3*r} := by
    have hh := g.isCompact_openFiber_preimage_closedBall hc
      (contMDiff_pi_space.mpr hf).continuous U c p₀ (3*r)
      (fun y hy => hbuffer y (hy.trans (ENNReal.ofReal_le_ofReal (by linarith))))
    convert hh using 1
    ext x
    change (g.edist p₀ (incl x)).toReal≤3*r ↔
      g.edist p₀ (incl x)≤ENNReal.ofReal (3*r)
    constructor
    · intro hx
      rw [← ENNReal.ofReal_toReal (g.edist_ne_top p₀ (incl x))]
      exact ENNReal.ofReal_le_ofReal hx
    · exact ENNReal.toReal_le_of_le_ofReal (by positivity)
  let R := fun x : L => max 0 (gL.leviCivitaData.scalarCurvature x)
  have hRi : IntegrableOn R {x : L | d x≤3*r} gL.volumeMeasure :=
    (continuous_const.max gL.leviCivitaData.continuous_scalarCurvature).continuousOn.integrableOn_compact hcompact
  apply Poincare.CurvatureIntegral.integral_le_card_mul_weighted_bound_of_finset_cover
    (isClosed_Icc.preimage hd).measurableSet
    Poincare.CurvatureIntegral.normalizedStripCenters
    (fun t => S t (5*s/64)) (fun t => S t (15*s/128))
    (fun t _ => hSm t _) (fun _ => le_max_left _ _) hK
  · exact hRi.mono_set (fun x hx => hx.2.trans (by linarith))
  · intro t _
    exact hRi.mono_set (fun x hx => (hrad t _ x hx).2.le.trans (by linarith))
  · exact (hKc.continuousOn.integrableOn_compact hcompact).mono_set (fun _ hx => hx.2)
  · intro x hx
    obtain ⟨t, ht, _, hstrip, hvalue⟩ :=
      D.exists_tilted_inner_band_covering_radial_point hc f h u hf hh p₀ (incl x)
        hΔ hΔsmall hδ hδsmall hr hx
        (fun i y hy => hpair i y (hbuffer y (hy.trans (by
          rw [← ENNReal.ofReal_toReal (g.edist_ne_top p₀ (incl x))]
          exact ENNReal.ofReal_le_ofReal (by linarith [hx.2])))))
        (fun i => (congrFun x.property i).trans (congrFun p.property i).symm)
        (happrox (incl x) hx)
    exact mem_iUnion₂.mpr ⟨t, ht, hstrip, hvalue⟩
  · intro t _ x hx
    obtain ⟨hl, hu⟩ := hrad t _ x hx
    exact ⟨by linarith, by linarith⟩
  · exact hC
  · exact hbounds
