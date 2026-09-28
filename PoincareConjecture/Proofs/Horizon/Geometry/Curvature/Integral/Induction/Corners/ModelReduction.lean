import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Normalized
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Localization
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.WeightedFiberGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.CornerModels

noncomputable section
open Set Filter Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem PoincareConjecture.normalizedCornerScalarBound_of_pointedCornerModel_bound
    (m k : ℕ) (hm : 2 ≤ m) (δ H η B : ℝ)
    (hH : 0 ≤ H) (hη : 0 < η) (hB : 0 ≤ B)
    (hbound : ∀ A : PointedCornerModel m k δ H, A.weightedRatio ≤ B)
    (M : Type) [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M]
    [IsManifold (𝓡 (m+k)) ∞ M] [ConnectedSpace M] :
    let r := min 1 (η/2)
    let N : ℕ := ⌈RiemannianMetric.modelVolume (m+k) 1 6 /
      RiemannianMetric.modelVolume (m+k) 1 (r/4)⌉₊
    NormalizedCornerScalarBound (m+k) m k rfl M δ H η ((N:ℝ)*B) := by
  classical
  let r : ℝ := min 1 (η/2)
  have hr : 0 < r := lt_min zero_lt_one (half_pos hη)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrη : r ≤ η/2 := min_le_right _ _
  let a := (r⁻¹)^2
  have ha : 1 ≤ a := by
    have hi : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr hr1
    dsimp only [a]
    nlinarith
  have hap : 0 < a := zero_lt_one.trans_le ha
  have hsqrt : Real.sqrt a = r⁻¹ := Real.sqrt_sq (inv_nonneg.mpr hr.le)
  have hsqrtr : Real.sqrt a*r = 1 := by rw [hsqrt, inv_mul_cancel₀ hr.ne']
  have hsqrt2r : Real.sqrt a*(2*r) = 2 := by
    rw [mul_left_comm, hsqrtr, mul_one]
  have hbufferSize : 2 ≤ Real.sqrt a*η := by
    rw [hsqrt, inv_mul_eq_div]
    exact (le_div_iff₀ hr).mpr (by linarith)
  have hHscale : H/Real.sqrt a ≤ H := by
    rw [hsqrt, div_inv_eq_mul]
    exact mul_le_of_le_one_right hH hr1
  dsimp only
  intro g D hc hsec f h hf hh U hunit hpair hcross htight hhess P hP hreg c
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hP U hreg c
  let := isManifold_openFiber (m := m) hP U hreg c
  let L := openFiber P U c
  let incl := openFiberIncl P U c
  let gL := g.openRegularFiberMetric hP U hreg c
  dsimp only
  intro hcompact hconnected hcomplete hdiam hbuffer K hK hKnonneg hKsec
  let : CompactSpace L := hcompact
  let : ConnectedSpace L := hconnected
  have hlocal (p : L) :
      (∫ x in incl ⁻¹' g.ball (incl p) r,
        max 0 (gL.leviCivitaData.scalarCurvature x) ∂gL.volumeMeasure) ≤
      B*(1+∫ x in incl ⁻¹' g.ball (incl p) (2*r), K x ∂gL.volumeMeasure) := by
    obtain ⟨hcG, hsecG, hfs, hhs, hunitS, hpairS, hcrossS, htightS, hhessS,
        hPs, hregS, hdata⟩ :=
      g.exists_scaled_openFiber_weighted_corner_geometry D hc hsec f h hf hh U
        hunit hpair hcross htight hhess c hm ha hreg
    let G := PoincareConjecture.rescaledMetric g a hap
    let DG := PoincareConjecture.rescaledMetric_connection g D a hap
    let fs := fun i x => Real.sqrt a*f i x
    let hs := fun i x => Real.sqrt a*h i x
    let Ps := fun x => Real.sqrt a • P x
    let vs := Real.sqrt a • c
    let := openFiberChartedSpace (m := m) hPs U hregS vs
    let := isManifold_openFiber (m := m) hPs U hregS vs
    let LS := openFiber Ps U vs
    let gS := G.openRegularFiberMetric hPs U hregS vs
    obtain ⟨e, hinc, _, _, _, hbufferS, herror⟩ := hdata
    let Ks : LS → ℝ := fun y => a⁻¹*K (e.symm y)
    obtain ⟨hKs, hKsnonneg, hKssec, hratio⟩ := herror K hK hKnonneg hKsec
    have hhessS' : ∀ x ∈ U, ∀ i v,
        DG.hessian (fs i) x v v ≤ H*G.inner x v v ∧
        DG.hessian (hs i) x v v ≤ H*G.inner x v v := by
      intro x hx i v
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m+k)) : M → Type _) :=
        ⟨G.toRiemannianMetric⟩
      have hv : 0 ≤ G.inner x v v := by
        change 0 ≤ inner ℝ v v
        exact real_inner_self_nonneg
      exact ⟨(hhessS x hx i v).1.trans (mul_le_mul_of_nonneg_right hHscale hv),
        (hhessS x hx i v).2.trans (mul_le_mul_of_nonneg_right hHscale hv)⟩
    let A : PointedCornerModel m k δ H :=
      { carrier := M
        metric := G
        connection := DG
        complete := hcG
        sectional_lower := hsecG
        f := fs
        h := hs
        f_smooth := hfs
        h_smooth := hhs
        domain := U
        unit := hunitS
        opposite := hpairS
        cross := hcrossS
        tight := htightS
        hessian_upper := hhessS'
        regular := hregS
        value := vs
        point := e p
        buffer := by
          intro y hy
          exact hbufferS η hbuffer (e p) y
            (hy.trans (ENNReal.ofReal_le_ofReal hbufferSize))
        error := Ks
        error_continuous := hKs
        error_nonneg := hKsnonneg
        error_sectional_lower := hKssec }
    have hratioB := hbound A
    change G.openFiberWeightedAmbientBallRatio hPs U hregS vs Ks
      (openFiberIncl Ps U vs (e p)) 1 2 ≤ B at hratioB
    rw [hinc] at hratioB
    have hl := hratio (incl p) r (2*r)
    rw [hsqrtr, hsqrt2r] at hl
    have ht := hl.trans hratioB
    change
      (∫ x in incl ⁻¹' g.ball (incl p) r,
        max 0 (gL.leviCivitaData.scalarCurvature x) ∂gL.volumeMeasure) /
      (1+∫ x in incl ⁻¹' g.ball (incl p) (2*r), K x ∂gL.volumeMeasure) ≤ B at ht
    exact (div_le_iff₀ (by
      have hi : 0 ≤ ∫ x in incl ⁻¹' g.ball (incl p) (2*r), K x ∂gL.volumeMeasure :=
        integral_nonneg hKnonneg
      linarith)).mp ht
  exact g.integral_openFiber_pos_scalar_le_of_local_bounds D hc (by omega) hsec
    hP U hreg c hcompact (inferInstance : Nonempty L) hdiam K hK hKnonneg
    r B hr hr1 hB hlocal

theorem PoincareConjecture.exists_normalizedCornerScalarBound_of_pointedCornerModel_bound
    (m k : ℕ) (hm : 2 ≤ m) (δ H η : ℝ) (hH : 0 ≤ H) (hη : 0 < η)
    (hbound : ∃ B : ℝ, ∀ A : PointedCornerModel m k δ H, A.weightedRatio ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : Type) [TopologicalSpace M] [T3Space M]
      [MeasurableSpace M] [BorelSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M]
      [IsManifold (𝓡 (m+k)) ∞ M] [ConnectedSpace M],
      NormalizedCornerScalarBound (m+k) m k rfl M δ H η C := by
  classical
  obtain ⟨B, hbound⟩ := hbound
  let r : ℝ := min 1 (η/2)
  let N : ℕ := ⌈RiemannianMetric.modelVolume (m+k) 1 6 /
    RiemannianMetric.modelVolume (m+k) 1 (r/4)⌉₊
  let B₀ := max 0 B
  have hB₀ : 0 ≤ B₀ := le_max_left _ _
  let C₀ := (N:ℝ)*B₀
  have hC₀ : 0 ≤ C₀ := mul_nonneg (Nat.cast_nonneg _) hB₀
  refine ⟨C₀+1, by linarith, ?_⟩
  intro M _ _ _ _ _ _ _
  have hb := PoincareConjecture.normalizedCornerScalarBound_of_pointedCornerModel_bound
    m k hm δ H η B₀ hH hη hB₀ (fun A => (hbound A).trans (le_max_right _ _)) M
  intro g D hc hsec f h hf hh U hunit hpair hcross htight hhess P hP hreg c
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hP U hreg c
  let := isManifold_openFiber (m := m) hP U hreg c
  dsimp only
  intro hcompact hconnected hcomplete hdiam hbuffer K hK hKnonneg hKsec
  have ht := hb g D hc hsec f h hf hh U hunit hpair hcross htight hhess
    hreg c hcompact hconnected hcomplete hdiam hbuffer K hK hKnonneg hKsec
  let gL := g.openRegularFiberMetric hP U hreg c
  have hi : 0 ≤ ∫ x, K x ∂gL.volumeMeasure := integral_nonneg hKnonneg
  exact ht.trans (mul_le_mul_of_nonneg_right (by dsimp only [C₀, N, r]; linarith)
    (by change 0 ≤ 1+∫ x, K x ∂gL.volumeMeasure; linarith))
