import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryTangent
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FillingAreaCurvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Complex
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Gauss

open M65Branch M65StrictTrace

theorem halfDisk_boundary_connection_curvature {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {Q : ℂ → Fin n → ℂ}
    {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : Even m)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hfactor : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      halfDiskGradient H r z = z ^ m • Q z)
    (hF : ContinuousOn
      (fun z => normalizedResidualFrame (g.euclideanCoefficients (H z)) (Q z))
      (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hunit : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      let T := (normalizedResidualFrame (g.euclideanCoefficients (H z)) (Q z)).1
      g.inner (H z) T T = 1)
    {c : ℝ → EuclideanSpace ℝ (Fin n)} {f : ℝ → ℝ}
    (hc : ContDiffAt ℝ 2 c (f 0)) (hc0 : deriv c (f 0) ≠ 0)
    (hf : ContDiff ℝ 1 f) (hmono : Monotone f ∨ Antitone f)
    (hcurve : ∀ᶠ t : ℝ in 𝓝 0, H (t : ℂ) = c (f t)) :
    let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
    let F := fun z => normalizedResidualFrame (g.euclideanCoefficients (H z)) (Q z)
    let T := fun t : ℝ => (F (t : ℂ)).1
    let V := fun s : ℝ =>
      (Real.sqrt (g.inner (c s) (deriv c s) (deriv c s)))⁻¹ • deriv c s
    ∀ᶠ t : ℝ in 𝓝 0, ContDiffAt ℝ 1 T t ∧
      g.inner (H (t : ℂ))
        (deriv T t + connectionCoefficient D (H (t : ℂ))
          (fderivWithin ℝ H K (t : ℂ) 1) (T t)) (F (t : ℂ)).2 =
        g.inner (H (t : ℂ))
          ((Real.sqrt (g.inner (c (f t)) (deriv c (f t)) (deriv c (f t))))⁻¹ •
            (deriv V (f t) + connectionCoefficient D (c (f t))
              (deriv c (f t)) (V (f t)))) (fderivWithin ℝ H K (t : ℂ) I) := by
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let F := fun z => normalizedResidualFrame (g.euclideanCoefficients (H z)) (Q z)
  let T := fun t : ℝ => (F (t : ℂ)).1
  let V := fun s : ℝ =>
    (Real.sqrt (g.inner (c s) (deriv c s) (deriv c s)))⁻¹ • deriv c s
  obtain ⟨ε, hε, heq, _hT0⟩ :=
    halfDisk_boundary_tangent g hr hm hH hfactor hF hunit hc hc0 hf hmono hcurve
  have hεsq : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ‖(t : ℂ)‖ < r :=
    continuous_ofReal.norm.continuousAt.eventually (gt_mem_nhds (by simpa using hr))
  have hcd : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 c (f t) :=
    hf.continuous.continuousAt.eventually (hc.eventually (by norm_num))
  have hvnear : ∀ᶠ t in 𝓝 (0 : ℝ), deriv c (f t) ≠ 0 := by
    have hv : ContinuousAt (deriv c) (f 0) := by
      simpa only [fderiv_apply_one_eq_deriv] using
        ((hc.fderiv_right (m := 1) (by norm_num)).continuousAt.clm_apply
          (continuousAt_const (x := f 0) (y := (1 : ℝ))))
    exact hf.continuous.continuousAt.eventually (hv.eventually_ne hc0)
  filter_upwards [hnear, hcd, hvnear, heq.eventually_nhds, hcurve.eventually_nhds]
    with t ht hct hcv hTeq hce
  have hKt : (t : ℂ) ∈ K := ⟨mem_closedBall_zero_iff.mpr ht.le, by simp⟩
  have hvalue : H (t : ℂ) = c (f t) := hce.self_of_nhds
  have hV : ContDiffAt ℝ 1 V (f t) :=
    regular_curve_unit_tangent_contDiffAt g hct hcv contDiffAt_id
  have hTeq' : T =ᶠ[𝓝 t] fun s => ε • V (f s) := hTeq
  have hTd : ContDiffAt ℝ 1 T t :=
    ((contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℝ => ε) t).smul
      (hV.comp t hf.contDiffAt)).congr_of_eventuallyEq hTeq'
  refine ⟨hTd, ?_⟩
  let L := fderivWithin ℝ H K (t : ℂ)
  let A := residualRealColumn (Q (t : ℂ))
  let B := residualImagColumn (Q (t : ℂ))
  let tau := Real.sqrt (g.inner (H (t : ℂ)) A A)
  let speed := Real.sqrt (g.inner (c (f t)) (deriv c (f t)) (deriv c (f t)))
  have hA : A ≠ 0 := by
    intro hz
    have hh := hunit (t : ℂ) hKt
    change g.inner (H (t : ℂ)) (tau⁻¹ • A) (tau⁻¹ • A) = 1 at hh
    simp only [hz, smul_zero, map_zero] at hh
    exact zero_ne_one hh
  have htau : 0 < tau := Real.sqrt_pos.mpr (g.pos _ _ hA)
  have hspeed : 0 < speed := Real.sqrt_pos.mpr (g.pos _ _ hcv)
  have hLT : L 1 = (t ^ m * tau) • T t := by
    have hh : residualRealColumn (halfDiskGradient H r (t : ℂ)) = L 1 := by
      simpa only [complexGradient, L.fderiv, L, halfDiskGradient, K] using
        (residual_columns_complexGradient L 0).1
    rw [hfactor (t : ℂ) hKt, (residual_columns_smul _ _).1] at hh
    simp only [← Complex.ofReal_pow, ofReal_re, ofReal_im, zero_smul, add_zero] at hh
    rw [← hh]
    change t ^ m • A = (t ^ m * tau) • (tau⁻¹ • A)
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ htau.ne', mul_one]
  have hLN : L I = (t ^ m * tau) • (F (t : ℂ)).2 := by
    have hh : residualImagColumn (halfDiskGradient H r (t : ℂ)) = L I := by
      simpa only [complexGradient, L.fderiv, L, halfDiskGradient, K] using
        (residual_columns_complexGradient L 0).2
    rw [hfactor (t : ℂ) hKt, (residual_columns_smul _ _).2] at hh
    simp only [← Complex.ofReal_pow, ofReal_re, ofReal_im, neg_zero, zero_smul,
      zero_add] at hh
    rw [← hh]
    change t ^ m • B = (t ^ m * tau) • (tau⁻¹ • B)
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ htau.ne', mul_one]
  have hLcurve : L 1 = deriv f t • deriv c (f t) := by
    have hce' : (fun s : ℝ => H (s : ℂ)) =ᶠ[𝓝 t] c ∘ f := hce
    exact (halfDisk_hasDerivAt_diameter hH ht).unique
      (((hct.differentiableAt (by norm_num)).hasDerivAt.scomp t
        (hf.differentiable one_ne_zero t).hasDerivAt).congr_of_eventuallyEq hce')
  have hunitV : g.inner (c (f t)) (V (f t)) (V (f t)) = 1 := by
    change g.inner (c (f t)) (speed⁻¹ • deriv c (f t))
      (speed⁻¹ • deriv c (f t)) = 1
    simp only [map_smul, smul_apply, smul_eq_mul]
    have hs : speed ^ 2 = g.inner (c (f t)) (deriv c (f t)) (deriv c (f t)) :=
      Real.sq_sqrt (g.pos _ _ hcv).le
    rw [← hs]
    field_simp
  have hvelocity : deriv c (f t) = speed • V (f t) := by
    change deriv c (f t) = speed • (speed⁻¹ • deriv c (f t))
    rw [smul_smul, mul_inv_cancel₀ hspeed.ne', one_smul]
  have hscale : ε * deriv f t = (t ^ m * tau) * speed⁻¹ := by
    have hh := congrArg (fun v => g.inner (c (f t)) v (V (f t)))
      (hLcurve.symm.trans hLT)
    rw [hvelocity, hTeq'.self_of_nhds] at hh
    simp only [smul_smul, map_smul, smul_apply, smul_eq_mul, hunitV, mul_one] at hh
    have h : ε * deriv f t * speed = t ^ m * tau := by
      calc
        _ = ε * (deriv f t * speed) := by ring
        _ = ε * (t ^ m * tau * ε) := by rw [hh]
        _ = (t ^ m * tau) * (ε * ε) := by ring
        _ = _ := by rw [hεsq, mul_one]
    calc
      _ = (ε * deriv f t * speed) * speed⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hspeed.ne', mul_one]
      _ = _ := by rw [h]
  have hderivT : deriv T t = ε • (deriv f t • deriv V (f t)) := by
    have hh := ((hV.differentiableAt one_ne_zero).hasDerivAt.scomp t
      (hf.differentiable one_ne_zero t).hasDerivAt).const_smul ε
    exact (hh.congr_of_eventuallyEq hTeq').deriv
  change g.inner (H (t : ℂ))
    (deriv T t + connectionCoefficient D (H (t : ℂ)) (L 1) (T t)) (F (t : ℂ)).2 =
      g.inner (H (t : ℂ))
        (speed⁻¹ • (deriv V (f t) + connectionCoefficient D (c (f t))
          (deriv c (f t)) (V (f t)))) (L I)
  rw [hderivT, hLcurve, hTeq'.self_of_nhds, hvalue, hLN]
  simp only [map_smul, smul_apply, smul_smul, map_add, add_apply, smul_eq_mul]
  rw [hscale]
  ring

end PoincareConjecture.M65Gauss

namespace PoincareConjecture.M65Gauss

open Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem regular_curve_curvature_chart
    (D : LeviCivitaData g) (DE : LeviCivitaData gE) (p : M)
    {eta : ℝ → M} (heta : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ eta)
    (hregular : ∀ s, curveVelocity (n := n) eta s ≠ 0) {t : ℝ}
    (hsource : eta t ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hmetric : ∀ᶠ y in 𝓝 ((chartAt (EuclideanSpace ℝ (Fin n)) p) (eta t)),
      ∀ a b : EuclideanSpace ℝ (Fin n),
        gE.inner y a b = g.inner ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y)
          (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm y a)
          (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm y b)) :
    let q := (chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ eta
    let V := fun s : ℝ =>
      (Real.sqrt (gE.inner (q s) (deriv q s) (deriv q s)))⁻¹ • deriv q s
    (g.tangentNorm (eta t) (curveVelocity (n := n) eta t))⁻¹ •
        rampHorizontalCovariantDerivative D eta
          (fun s => (g.tangentNorm (eta s) (curveVelocity (n := n) eta s))⁻¹ •
            curveVelocity (n := n) eta s) t =
      mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm (q t)
        ((Real.sqrt (gE.inner (q t) (deriv q t) (deriv q t)))⁻¹ •
          (deriv V t + connectionCoefficient DE (q t) (deriv q t) (V t))) := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) p
  let q := c ∘ eta
  let U := eta ⁻¹' c.source
  let V := fun s : ℝ =>
    (Real.sqrt (gE.inner (q s) (deriv q s) (deriv q s)))⁻¹ • deriv q s
  have hU : IsOpen U := c.open_source.preimage heta.continuous
  have hq : ContDiffOn ℝ ∞ q U :=
    (contMDiffOn_chart.comp heta.contMDiffOn (fun _ hs => hs)).contDiffOn
  have hqd : ContDiffOn ℝ ∞ (deriv q) U := by
    simpa only [fderiv_apply_one_eq_deriv] using
      (hq.fderiv_of_isOpen hU (by simp)).clm_apply (contDiffOn_const (c := (1 : ℝ)))
  have hfields (s : ℝ) (hs : s ∈ U) :
      chartVectorField p (deriv q s) (eta s) = curveVelocity (n := n) eta s :=
    chartVectorField_coordinate_velocity p eta s (deriv q s) hs
      ((heta s).mdifferentiableAt (by simp))
      ((hq.contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt
  have hpush (s : ℝ) (hs : s ∈ U) (a : EuclideanSpace ℝ (Fin n)) :
      chartVectorField p a (eta s) = mfderiv (𝓡 n) (𝓡 n) c.symm (q s) a := by
    have hh := chartVectorField_at_inverse p a (c (eta s)) (c.map_source hs)
    rw [c.left_inv hs] at hh
    exact hh
  have hdf (s : ℝ) (hs : s ∈ U) :
      curveVelocity (n := n) eta s = mfderiv (𝓡 n) (𝓡 n) c.symm (q s) (deriv q s) :=
    (hfields s hs).symm.trans (hpush s hs _)
  have hqne (s : ℝ) (hs : s ∈ U) : deriv q s ≠ 0 := by
    intro hz
    apply hregular s
    rw [hdf s hs, hz, map_zero]
  have hV : ContDiffOn ℝ ∞ V U := by
    have hG : ContDiffOn ℝ ∞ (fun s => gE.euclideanCoefficients (q s)) U :=
      (contDiff_iff_contDiffAt.mpr gE.contDiffAt_euclideanCoefficients).comp_contDiffOn hq
    have hpos (s : ℝ) (hs : s ∈ U) : 0 < gE.inner (q s) (deriv q s) (deriv q s) :=
      gE.pos _ _ (hqne s hs)
    exact ((((hG.clm_apply hqd).clm_apply hqd).sqrt (fun s hs => (hpos s hs).ne')).inv
      (fun s hs => (Real.sqrt_pos.mpr (hpos s hs)).ne')).smul hqd
  have hmet : ∀ᶠ s in 𝓝 t, ∀ a b : EuclideanSpace ℝ (Fin n),
      gE.inner (q s) a b = g.inner (c.symm (q s))
        (mfderiv (𝓡 n) (𝓡 n) c.symm (q s) a)
        (mfderiv (𝓡 n) (𝓡 n) c.symm (q s) b) :=
    (hq.continuousOn.continuousAt (hU.mem_nhds hsource)).eventually hmetric
  have hspeed : ∀ᶠ s in 𝓝 t,
      g.tangentNorm (eta s) (curveVelocity (n := n) eta s) =
        Real.sqrt (gE.inner (q s) (deriv q s) (deriv q s)) := by
    filter_upwards [hU.mem_nhds hsource, hmet] with s hs hm
    have hh := hm (deriv q s) (deriv q s)
    have hinv : c.symm (q s) = eta s := c.left_inv hs
    rw [hinv] at hh
    simpa +instances only [RiemannianMetric.tangentNorm, hdf s hs]
      using! congrArg Real.sqrt hh.symm
  have hunit : (fun s => (g.tangentNorm (eta s) (curveVelocity (n := n) eta s))⁻¹ •
      curveVelocity (n := n) eta s) =ᶠ[𝓝 t]
      fun s => chartVectorField p (V s) (eta s) := by
    filter_upwards [hU.mem_nhds hsource, hspeed] with s hs hsp
    rw [hsp, hpush s hs, hdf s hs, map_smul]
  have hpull := M62.pullback_chart_field D p ((heta t).mdifferentiableAt (by simp))
    hsource hU hsource V hV
  have hconn : D.connection (chartVectorField p (V t)) (eta t)
      (mfderiv (𝓡 n) (𝓡 n) c.symm (q t) (deriv q t)) =
        mfderiv (𝓡 n) (𝓡 n) c.symm (q t)
          (connectionCoefficient DE (q t) (deriv q t) (V t)) := by
    have hh := connection_chartVectorField D DE p (c.map_source hsource) hmetric
      (deriv q t) (V t)
    rw [c.left_inv hsource] at hh
    exact hh
  have hramp := (M62.pullback_congr D hunit).trans hpull
  rw [hpush t hsource, hdf t hsource, hconn] at hramp
  change (g.tangentNorm (eta t) (curveVelocity (n := n) eta t))⁻¹ •
    rampHorizontalCovariantDerivative D eta
      (fun s => (g.tangentNorm (eta s) (curveVelocity (n := n) eta s))⁻¹ •
        curveVelocity (n := n) eta s) t =
      mfderiv (𝓡 n) (𝓡 n) c.symm (q t)
        ((Real.sqrt (gE.inner (q t) (deriv q t) (deriv q t)))⁻¹ •
          (deriv V t + connectionCoefficient DE (q t) (deriv q t) (V t)))
  have hh := congrArg (fun w : TangentSpace (𝓡 n) (eta t) =>
    (Real.sqrt (gE.inner (q t) (deriv q t) (deriv q t)))⁻¹ • w) hramp
  simpa +instances only [hspeed.self_of_nhds, map_smul, map_add, smul_add] using! hh

end PoincareConjecture.M65Gauss

namespace PoincareConjecture.M65MinimalDisk

open M65Branch M65StrictTrace M65Gauss Proofs.M09

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}

theorem boundary_connection_curvature_of_frame (S : M65MinimalDisk g connection gamma)
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (periodicFreeLoop gamma))
    (hregular : ∀ t : ℝ, curveVelocity (n := 3) (periodicFreeLoop gamma) t ≠ 0)
    {x : LoopPlane} (hx : ‖x‖ = 1)
    (gE : RiemannianMetric 3 LoopAmbient) (DE : LeviCivitaData gE)
    {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : Even m) (Q : ℂ → Fin 3 → ℂ)
    (W : (p : M) → TangentSpace (𝓡 3) p)
    (hW : ∀ s, W (periodicFreeLoop gamma s) = M65Filling.loopCurvature connection gamma s) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let chart := chartAt LoopAmbient (S.disk.map x)
    let P := e ∘ boundaryCoordinate (e.symm x)
    let H := chart ∘ S.disk.map ∘ P
    let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
    let F := fun z => normalizedResidualFrame (gE.euclideanCoefficients (H z)) (Q z)
    let T := fun t : ℝ => (F (t : ℂ)).1
    MapsTo P K loopDiskSet → MapsTo (S.disk.map ∘ P) K chart.source →
      ContDiffOn ℝ 1 H K →
      (∀ z ∈ K, ∀ᶠ y in 𝓝 (H z), ∀ a b : LoopAmbient,
        gE.inner y a b = g.inner (chart.symm y)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y a)
          (mfderiv (𝓡 3) (𝓡 3) chart.symm y b)) →
      (∀ z ∈ K, halfDiskGradient H r z = z ^ m • Q z) → ContinuousOn F K →
      (∀ z ∈ K, gE.inner (H z) (F z).1 (F z).1 = 1) →
      ∀ᶠ t : ℝ in 𝓝 0, ContDiffAt ℝ 1 T t ∧
        gE.inner (H (t : ℂ))
          (deriv T t + connectionCoefficient DE (H (t : ℂ))
            (fderivWithin ℝ H K (t : ℂ) 1) (T t)) (F (t : ℂ)).2 =
          -g.inner (S.disk.map (P (t : ℂ))) (W (S.disk.map (P (t : ℂ))))
            (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
              (P (t : ℂ)) (P (t : ℂ))) := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let p := e.symm x
  let chart := chartAt LoopAmbient (S.disk.map x)
  let P := e ∘ boundaryCoordinate p
  let H := chart ∘ S.disk.map ∘ P
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let F := fun z => normalizedResidualFrame (gE.euclideanCoefficients (H z)) (Q z)
  let T := fun t : ℝ => (F (t : ℂ)).1
  change MapsTo P K loopDiskSet → MapsTo (S.disk.map ∘ P) K chart.source →
    ContDiffOn ℝ 1 H K → _
  intro hP hsource hH hmetric hfactor hF hunit
  have hp : ‖p‖ = 1 := by
    change ‖orthonormalBasisOneI.repr.symm x‖ = 1
    rw [orthonormalBasisOneI.repr.symm.norm_map, hx]
  let a := Complex.arg p
  have hexp : Complex.exp ((a : ℂ) * I) = p := by
    simpa only [hp, ofReal_one, one_mul, a] using Complex.norm_mul_exp_arg_mul_I p
  have hangular (t : ℝ) : e.symm (Proofs.M58.angularPoint t) =
      Complex.exp ((t : ℂ) * I) := by
    rw [Complex.exp_ofReal_mul_I]
    rfl
  have hPangle (t : ℝ) : P (t : ℂ) = Proofs.M58.angularPoint (t + a) := by
    apply e.symm.injective
    change e.symm (e (boundaryCoordinate p (t : ℂ))) = _
    rw [e.symm_apply_apply, hangular, ofReal_add, add_mul, Complex.exp_add, hexp]
    simp only [boundaryCoordinate, mul_comm I (t : ℂ), mul_comm p]
  have hP0 : P (0 : ℂ) = x := by
    simp only [P, Function.comp_apply, boundaryCoordinate, mul_zero, Complex.exp_zero,
      mul_one, p, e.apply_symm_apply]
  obtain ⟨h, hh, hlift, horient⟩ := M65Filling.boundary_lift S hsmooth hregular
  let f := fun t : ℝ => h (t + a)
  let c := chart ∘ periodicFreeLoop gamma
  let V := fun s : ℝ =>
    (Real.sqrt (gE.inner (c s) (deriv c s) (deriv c s)))⁻¹ • deriv c s
  let kappa := fun s : ℝ =>
    (Real.sqrt (gE.inner (c s) (deriv c s) (deriv c s)))⁻¹ •
      (deriv V s + connectionCoefficient DE (c s) (deriv c s) (V s))
  have hloop (t : ℝ) : periodicFreeLoop gamma (f t) = S.disk.map (P (t : ℂ)) := by
    rw [hPangle]
    exact (hlift (t + a)).symm
  have hf : ContDiff ℝ 1 f := hh.comp (contDiff_id.add contDiff_const)
  have hmono : Monotone f ∨ Antitone f := by
    rcases horient with ⟨hm, _⟩ | ⟨hm, _⟩
    · exact Or.inl (fun s t hst => hm.monotone (show s + a ≤ t + a by linarith))
    · exact Or.inr (fun s t hst => hm.antitone (show s + a ≤ t + a by linarith))
  have hsource0 : periodicFreeLoop gamma (f 0) ∈ chart.source := by
    rw [hloop, ofReal_zero, hP0]
    exact mem_chart_source LoopAmbient _
  let J := periodicFreeLoop gamma ⁻¹' chart.source
  have hJ : IsOpen J := chart.open_source.preimage hsmooth.continuous
  have hc : ContDiffOn ℝ ∞ c J :=
    (contMDiffOn_chart.comp hsmooth.contMDiffOn (fun _ ht => ht)).contDiffOn
  have hcAt : ContDiffAt ℝ 2 c (f 0) :=
    (hc.contDiffAt (hJ.mem_nhds hsource0)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hvelocity : deriv c (f 0) = mfderiv (𝓡 3) (𝓡 3) chart
      (periodicFreeLoop gamma (f 0)) (curveVelocity (periodicFreeLoop gamma) (f 0)) :=
    (hasDerivAt_chart_curve (S.disk.map x) (periodicFreeLoop gamma) (f 0) hsource0
      ((hsmooth (f 0)).mdifferentiableAt (by simp))).deriv
  have hc0 : deriv c (f 0) ≠ 0 := by
    intro hz
    apply hregular (f 0)
    apply ((mdifferentiable_chart (I := 𝓡 3) (S.disk.map x)).mfderiv hsource0).injective
    change mfderiv (𝓡 3) (𝓡 3) chart (periodicFreeLoop gamma (f 0))
      (curveVelocity (periodicFreeLoop gamma) (f 0)) =
        mfderiv (𝓡 3) (𝓡 3) chart (periodicFreeLoop gamma (f 0)) 0
    rw [← hvelocity, hz, map_zero]
  have hcurve : ∀ᶠ t : ℝ in 𝓝 0, H (t : ℂ) = c (f t) := by
    filter_upwards with t
    exact congrArg chart (hloop t).symm
  have hlocal := halfDisk_boundary_connection_curvature DE hr hm hH hfactor hF hunit
    hcAt hc0 hf hmono hcurve
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ‖(t : ℂ)‖ < r :=
    continuous_ofReal.norm.continuousAt.eventually (gt_mem_nhds (by simpa using hr))
  filter_upwards [hlocal, hnear] with t ht htball
  have hKt : (t : ℂ) ∈ K := ⟨mem_closedBall_zero_iff.mpr htball.le, by simp⟩
  have hsrc : S.disk.map (P (t : ℂ)) ∈ chart.source := hsource hKt
  have hsrcLoop : periodicFreeLoop gamma (f t) ∈ chart.source := by rw [hloop]; exact hsrc
  have hmetLoop : ∀ᶠ y in 𝓝 (c (f t)), ∀ v w : LoopAmbient,
      gE.inner y v w = g.inner (chart.symm y)
        (mfderiv (𝓡 3) (𝓡 3) chart.symm y v)
        (mfderiv (𝓡 3) (𝓡 3) chart.symm y w) := by
    change ∀ᶠ y in 𝓝 (chart (periodicFreeLoop gamma (f t))), _
    rw [hloop]
    exact hmetric (t : ℂ) hKt
  have htransport := regular_curve_curvature_chart connection DE (S.disk.map x)
    hsmooth hregular hsrcLoop hmetLoop
  have hpushK : (mfderiv (𝓡 3) (𝓡 3) chart.symm (H (t : ℂ))
      (kappa (f t)) : LoopAmbient) = W (S.disk.map (P (t : ℂ))) := by
    have hh : (M65Filling.loopCurvature connection gamma (f t) : LoopAmbient) =
        mfderiv (𝓡 3) (𝓡 3) chart.symm (H (t : ℂ)) (kappa (f t)) := by
      change (M65Filling.loopCurvature connection gamma (f t) : LoopAmbient) =
        mfderiv (𝓡 3) (𝓡 3) chart.symm (c (f t)) (kappa (f t)) at htransport
      have hvalue : c (f t) = H (t : ℂ) := congrArg chart (hloop t)
      exact htransport.trans (congrArg (fun y : LoopAmbient =>
        (mfderiv (𝓡 3) (𝓡 3) chart.symm y (kappa (f t)) : LoopAmbient)) hvalue)
    exact hh.symm.trans ((hW (f t)).symm.trans
      (congrArg (fun y => (W y : LoopAmbient)) (hloop t)))
  let L := fderivWithin ℝ H K (t : ℂ)
  let R := mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
    (P (t : ℂ)) (P (t : ℂ))
  have hchain := complex_parameter_within_chart (S.disk.map x) S.boundary_regular
    ((halfDisk_differential_domain hr).2.2.1 (t : ℂ) hKt) hKt
    (hasDerivAt_boundaryCoordinate p (t : ℂ)) hP hsrc I
  have hPI : orthonormalBasisOneI.repr (I * (I * boundaryCoordinate p (t : ℂ))) =
      -P (t : ℂ) := by
    rw [← mul_assoc, I_mul_I, neg_one_mul, map_neg]
    rfl
  change L I = mfderiv (𝓡 3) (𝓡 3) chart (S.disk.map (P (t : ℂ)))
    (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet (P (t : ℂ))
      (orthonormalBasisOneI.repr (I * (I * boundaryCoordinate p (t : ℂ))))) at hchain
  rw [hPI, map_neg, map_neg] at hchain
  have hcancel (v : TangentSpace (𝓡 3) (S.disk.map (P (t : ℂ)))) :
      mfderiv (𝓡 3) (𝓡 3) chart.symm (H (t : ℂ))
        (mfderiv (𝓡 3) (𝓡 3) chart (S.disk.map (P (t : ℂ))) v) = v :=
    congrArg (fun A : TangentSpace (𝓡 3) (S.disk.map (P (t : ℂ))) →L[ℝ]
      TangentSpace (𝓡 3) (S.disk.map (P (t : ℂ))) => A v)
      ((mdifferentiable_chart (I := 𝓡 3) (S.disk.map x)).symm_comp_deriv hsrc)
  have hpushI : (mfderiv (𝓡 3) (𝓡 3) chart.symm (H (t : ℂ)) (L I) : LoopAmbient) =
      -R := by
    have hh := congrArg (fun v : LoopAmbient =>
      mfderiv (𝓡 3) (𝓡 3) chart.symm (H (t : ℂ)) v) hchain
    simpa +instances only [map_neg, hcancel] using! hh
  have hpair := (hmetric (t : ℂ) hKt).self_of_nhds (kappa (f t)) (L I)
  have hinv : chart.symm (H (t : ℂ)) = S.disk.map (P (t : ℂ)) := chart.left_inv hsrc
  rw [hinv] at hpair
  change gE.inner (H (t : ℂ)) (kappa (f t)) (L I) =
    g.inner (S.disk.map (P (t : ℂ)))
      (mfderiv (𝓡 3) (𝓡 3) chart.symm (H (t : ℂ)) (kappa (f t)))
      (mfderiv (𝓡 3) (𝓡 3) chart.symm (H (t : ℂ)) (L I)) at hpair
  have hpair' : gE.inner (H (t : ℂ)) (kappa (f t)) (L I) =
      -g.inner (S.disk.map (P (t : ℂ))) (W (S.disk.map (P (t : ℂ)))) R := by
    have hh := hpair.trans (congrArg₂ (fun v w : LoopAmbient =>
      g.inner (S.disk.map (P (t : ℂ))) v w) hpushK hpushI)
    simpa +instances only [map_neg] using! hh
  exact ⟨ht.1, ht.2.trans hpair'⟩

end PoincareConjecture.M65MinimalDisk
