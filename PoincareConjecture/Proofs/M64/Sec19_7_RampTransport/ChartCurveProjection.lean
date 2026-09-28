import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.ImmersionCurveProjection
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Charts
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Intrinsic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture

open Proofs.M09 ConjugateVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem m64_chart_field_norm (g : RiemannianMetric n M) (p : M)
    {q : M} (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (v : EuclideanSpace ℝ (Fin n)) :
    g.tangentNorm q (chartVectorField p v q) =
      Real.sqrt (g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) q) v v) := by
  have hv := chartVectorField_at_inverse p v ((chartAt (EuclideanSpace ℝ (Fin n)) p) q)
    ((chartAt (EuclideanSpace ℝ (Fin n)) p).map_source hq)
  rw [(chartAt (EuclideanSpace ℝ (Fin n)) p).left_inv hq] at hv
  unfold RiemannianMetric.tangentNorm
  rw [hv]
  change _ = Real.sqrt (g.inner
    ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) q)) _ _)
  rw [(chartAt (EuclideanSpace ℝ (Fin n)) p).left_inv hq]
  rfl

theorem m64_pullback_norm_chart_metric
    (D : LeviCivitaData g) (p : M)
    {gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (DE : LeviCivitaData gE)
    {c : ℝ → M} {x : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) c x)
    (hsource : c x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    {Y : (s : ℝ) → TangentSpace (𝓡 n) (c s)}
    {v : ℝ → EuclideanSpace ℝ (Fin n)} (hv : ContDiffAt ℝ 1 v x)
    (hfield : ∀ᶠ s in 𝓝 x, Y s = chartVectorField p (v s) (c s))
    (hmetric : gE.euclideanCoefficients =ᶠ[𝓝 ((chartAt (EuclideanSpace ℝ (Fin n)) p) (c x))]
      g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) p).symm) :
    g.tangentNorm (c x) (rampHorizontalCovariantDerivative D c Y x) =
      gE.tangentNorm ((chartAt (EuclideanSpace ℝ (Fin n)) p) (c x))
        (deriv v x + DE.connectionCoefficient
          ((chartAt (EuclideanSpace ℝ (Fin n)) p) (c x))
          (deriv ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ c) x) (v x)) := by
  have hGamma (a b : EuclideanSpace ℝ (Fin n)) :
      DE.connectionCoefficient ((chartAt (EuclideanSpace ℝ (Fin n)) p) (c x)) a b =
      coordinateChristoffel (g.pullbackCoefficients
        (chartAt (EuclideanSpace ℝ (Fin n)) p).symm)
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) (c x)) a b := by
    rw [DE.connectionCoefficient_eq_coordinateChristoffel]
    simp only [coordinateChristoffel, hmetric.self_of_nhds, hmetric.fderiv_eq]
  rw [m64_pullback_chart_expression D p hc hsource hv hfield,
    m64_chart_field_norm g p hsource, hGamma]
  change Real.sqrt (g.pullbackCoefficients
      (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) (c x)) _ _) =
    Real.sqrt (gE.euclideanCoefficients _ _ _)
  rw [hmetric.self_of_nhds]

theorem m64_induced_manifold_curve_connection_norm_le
    (D : LeviCivitaData g)
    {h : RiemannianMetric m (EuclideanSpace ℝ (Fin m))} (Dh : LeviCivitaData h)
    {j : EuclideanSpace ℝ (Fin m) → M}
    {c W : ℝ → EuclideanSpace ℝ (Fin m)} {x : ℝ}
    (hj : ∀ᶠ q in 𝓝 (c x), ContMDiffAt (𝓡 m) (𝓡 n) ∞ j q)
    (hc : ContDiffAt ℝ 1 c x) (hW : ContDiffAt ℝ 1 W x)
    (hmetric : ∀ᶠ q in 𝓝 (c x), ∀ a b, h.inner q a b =
      g.inner (j q) (mfderiv (𝓡 m) (𝓡 n) j q a) (mfderiv (𝓡 m) (𝓡 n) j q b)) :
    h.tangentNorm (c x) (rampHorizontalCovariantDerivative Dh c W x) ≤
      g.tangentNorm (j (c x))
        (rampHorizontalCovariantDerivative D (j ∘ c)
          (fun s => mfderiv (𝓡 m) (𝓡 n) j (c s) (W s)) x) := by
  let p := j (c x)
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  let f := e ∘ j
  let B := g.pullbackCoefficients e.symm
  have he (q : EuclideanSpace ℝ (Fin m)) (hq : j q ∈ e.source) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ e (j q) :=
    contMDiffOn_chart.contMDiffAt (e.open_source.mem_nhds hq)
  have hchart : ∀ᶠ q in 𝓝 (c x), j q ∈ e.source :=
    hj.self_of_nhds.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds (mem_chart_source _ p))
  have hf : ∀ᶠ q in 𝓝 (c x), ContDiffAt ℝ ∞ f q := by
    filter_upwards [hj, hchart] with q hq hqc
    exact contMDiffAt_iff_contDiffAt.mp ((he q hqc).comp q hq)
  have hdu (q : EuclideanSpace ℝ (Fin m))
      (hq : ContMDiffAt (𝓡 m) (𝓡 n) ∞ j q) (hqc : j q ∈ e.source)
      (v : EuclideanSpace ℝ (Fin m)) :
      fderiv ℝ f q v = mfderiv (𝓡 n) (𝓡 n) e (j q)
        (mfderiv (𝓡 m) (𝓡 n) j q v) := by
    have hd := mfderiv_comp q ((he q hqc).mdifferentiableAt (by simp))
      (hq.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hd
    exact congrArg (fun L => L v) hd
  obtain ⟨gE, DE, hgE⟩ := LeviCivitaData.exists_chart_metric g p
  have hB : gE.euclideanCoefficients =ᶠ[𝓝 (f (c x))] B := by
    filter_upwards [hgE] with y hy
    ext a b
    exact hy a b
  have hmetricE : ∀ᶠ q in 𝓝 (c x), ∀ a b, h.inner q a b =
      gE.inner (f q) (fderiv ℝ f q a) (fderiv ℝ f q b) := by
    filter_upwards [hmetric, hj, hchart, hf.self_of_nhds.continuousAt.eventually hB]
      with q hq hqj hqe hqB a b
    change h.inner q a b = gE.euclideanCoefficients (f q)
      (fderiv ℝ f q a) (fderiv ℝ f q b)
    rw [hqB, hdu q hqj hqe a, hdu q hqj hqe b]
    exact (hq a b).trans (chartCoefficients_apply g p
      (by simpa only [extChartAt_source, e] using hqe) _ _).symm
  let v := fun s => fderiv ℝ f (c s) (W s)
  have hv : ContDiffAt ℝ 1 v x :=
    (((hf.self_of_nhds.fderiv_right (m := 1) (by norm_cast)).comp x hc).clm_apply hW)
  have hfield : ∀ᶠ s in 𝓝 x,
      mfderiv (𝓡 m) (𝓡 n) j (c s) (W s) =
        chartVectorField p (v s) (j (c s)) := by
    filter_upwards [hc.continuousAt.eventually hj, hc.continuousAt.eventually hchart]
      with s hs hse
    rw [show v s = mfderiv (𝓡 n) (𝓡 n) e (j (c s))
      (mfderiv (𝓡 m) (𝓡 n) j (c s) (W s)) from hdu (c s) hs hse (W s)]
    have hi : (mfderiv (𝓡 n) (𝓡 n) e (j (c s))).IsInvertible :=
      ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv hse, rfl⟩
    exact (hi.inverse_apply_self _).symm
  have hcj : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (j ∘ c) x :=
    (hj.self_of_nhds.mdifferentiableAt (by simp)).comp x hc.differentiableAt_one.mdifferentiableAt
  have hnorm := m64_pullback_norm_chart_metric D p DE hcj
    hchart.self_of_nhds hv hfield hB
  calc
    _ = h.tangentNorm (c x)
        (deriv W x + Dh.connectionCoefficient (c x) (deriv c x) (W x)) :=
      congrArg (h.tangentNorm (c x))
        (m64_model_pullback_expression Dh hc.differentiableAt_one hW)
    _ ≤ gE.tangentNorm (f (c x))
        (deriv v x + DE.connectionCoefficient (f (c x))
          (deriv (f ∘ c) x) (v x)) :=
      m64_induced_curve_connection_norm_le DE Dh hf.self_of_nhds
        hc.differentiableAt_one hW.differentiableAt_one hmetricE
    _ = _ := hnorm.symm

end PoincareConjecture
