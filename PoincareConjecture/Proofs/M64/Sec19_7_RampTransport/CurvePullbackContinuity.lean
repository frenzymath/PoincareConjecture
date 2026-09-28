import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.ChartCurveProjection





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture

open Proofs.M09

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}





theorem m64_pullback_norm_continuousAt_of_chart
    (D : LeviCivitaData g) {c : ℝ → M} {x : ℝ}
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ c x)
    {Y : (s : ℝ) → TangentSpace (𝓡 n) (c s)}
    {v : ℝ → EuclideanSpace ℝ (Fin n)} (hv : ContDiffAt ℝ ∞ v x)
    (hfield : ∀ᶠ s in 𝓝 x, Y s = chartVectorField (c x) (v s) (c s)) :
    ContinuousAt (fun s => g.tangentNorm (c s)
      (rampHorizontalCovariantDerivative D c Y s)) x := by
  let p := c x
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  let z := e ∘ c
  have hsource : ∀ᶠ s in 𝓝 x, c s ∈ e.source :=
    hc.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds (mem_chart_source _ p))
  have hz : ContDiffAt ℝ ∞ z x :=
    ((contMDiffOn_chart.contMDiffAt (e.open_source.mem_nhds hsource.self_of_nhds)).comp x
      hc).contDiffAt
  obtain ⟨gE, DE, hgE⟩ := LeviCivitaData.exists_chart_metric g p
  have hB : gE.euclideanCoefficients =ᶠ[𝓝 (z x)] g.pullbackCoefficients e.symm := by
    filter_upwards [hgE] with y hy
    ext a b
    exact hy a b
  let A := fun s => deriv v s + DE.connectionCoefficient (z s) (deriv z s) (v s)
  have hA : ContinuousAt A x :=
    (hv.derivWithin (m := 0) (by simp)).continuousAt.add
      (((DE.contDiff_connectionCoefficient.continuous.continuousAt.comp hz.continuousAt).clm_apply
        (hz.derivWithin (m := 0) (by simp)).continuousAt).clm_apply hv.continuousAt)
  have hnorm : ContinuousAt (fun s => gE.tangentNorm (z s) (A s)) x := by
    exact ((((gE.contDiffAt_euclideanCoefficients (z x)).continuousAt.comp
      hz.continuousAt).clm_apply hA).clm_apply hA).sqrt
  have hc1 : ∀ᶠ s in 𝓝 x, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) 1 c s :=
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp (hc.of_le (by simp))
  have hv1 : ∀ᶠ s in 𝓝 x, ContDiffAt ℝ 1 v s :=
    (hv.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num)
  apply hnorm.congr_of_eventuallyEq
  filter_upwards [hc1, hv1, hsource, hfield.eventually_nhds,
    hz.continuousAt.eventually hB.eventually_nhds] with s hcs hvs hss hfs hBs
  exact (m64_pullback_norm_chart_metric D p DE (hcs.mdifferentiableAt (by norm_num))
    hss hvs hfs hBs)





theorem m64_pushforward_pullback_norm_continuous
    (D : LeviCivitaData g) {j : EuclideanSpace ℝ (Fin m) → M}
    {c W : ℝ → EuclideanSpace ℝ (Fin m)}
    (hj : ∀ x, ∀ᶠ q in 𝓝 (c x), ContMDiffAt (𝓡 m) (𝓡 n) ∞ j q)
    (hc : ContDiff ℝ ∞ c) (hW : ContDiff ℝ ∞ W) :
    Continuous (fun x => g.tangentNorm (j (c x))
      (rampHorizontalCovariantDerivative D (j ∘ c)
        (fun s => mfderiv (𝓡 m) (𝓡 n) j (c s) (W s)) x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let p := j (c x)
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  let f := e ∘ j
  have hchart : ∀ᶠ q in 𝓝 (c x), j q ∈ e.source :=
    (hj x).self_of_nhds.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds (mem_chart_source _ p))
  have he (q : EuclideanSpace ℝ (Fin m)) (hq : j q ∈ e.source) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ e (j q) :=
    contMDiffOn_chart.contMDiffAt (e.open_source.mem_nhds hq)
  have hf : ContDiffAt ℝ ∞ f (c x) :=
    contMDiffAt_iff_contDiffAt.mp
      ((he (c x) hchart.self_of_nhds).comp (c x) (hj x).self_of_nhds)
  let v := fun s => fderiv ℝ f (c s) (W s)
  have hv : ContDiffAt ℝ ∞ v x :=
    (((hf.fderiv_right (m := ∞) (by simp)).comp x hc.contDiffAt).clm_apply hW.contDiffAt)
  have hfield : ∀ᶠ s in 𝓝 x,
      mfderiv (𝓡 m) (𝓡 n) j (c s) (W s) =
        chartVectorField p (v s) (j (c s)) := by
    filter_upwards [hc.continuous.continuousAt.eventually (hj x),
      hc.continuous.continuousAt.eventually hchart] with s hs hse
    have hd := mfderiv_comp (c s) ((he (c s) hse).mdifferentiableAt (by simp))
      (hs.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hd
    have hv' : v s = mfderiv (𝓡 n) (𝓡 n) e (j (c s))
        (mfderiv (𝓡 m) (𝓡 n) j (c s) (W s)) := congrArg (fun L => L (W s)) hd
    rw [hv']
    have hi : (mfderiv (𝓡 n) (𝓡 n) e (j (c s))).IsInvertible :=
      ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv hse, rfl⟩
    exact (hi.inverse_apply_self _).symm
  exact m64_pullback_norm_continuousAt_of_chart D
    ((hj x).self_of_nhds.comp x hc.contDiffAt.contMDiffAt) hv hfield

end PoincareConjecture
