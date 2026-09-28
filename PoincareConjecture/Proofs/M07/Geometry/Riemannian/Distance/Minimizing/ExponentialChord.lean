import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.GeodesicCorner
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.NormalChart
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.FrozenMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.ChartComparison












noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal Bundle

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_exponential_chord_bound
    (g : RiemannianMetric n M) (p : M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ e.source) (he0 : e 0 = p)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (he' : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (hd : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v))
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) 0)
    {θ : ℝ} (hθ : 1 < θ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v w : EuclideanSpace ℝ (Fin n),
      ‖v‖ < ρ → ‖w‖ < ρ →
      g.edist (e v) (e w) ≤ ENNReal.ofReal (θ * g.tangentNorm p (w - v)) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  have hde : ∀ v : EuclideanSpace ℝ (Fin n),
      mfderiv (𝓡 n) (𝓡 n) e 0 v = v := by
    intro v
    have hchart : MDifferentiableAt (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (e 0) := by
      rw [he0]
      exact (contMDiffAt_extChartAt' (n := ∞) (mem_chart_source _ p)).mdifferentiableAt
        (by simp)
    have hcomp := mfderiv_comp (0 : EuclideanSpace ℝ (Fin n)) hchart
      ((he.contMDiffAt (e.open_source.mem_nhds h0)).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hcomp
    change fderiv ℝ (fun v => extChartAt (𝓡 n) p (e v)) 0 = _ at hcomp
    rw [hd.fderiv] at hcomp
    have hv := congr($hcomp v)
    have hchartid (u : EuclideanSpace ℝ (Fin n)) :
        mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (e 0) u = u := by
      rw [he0]
      exact congrArg (fun L => L u) (mfderiv_extChartAt_self (I := 𝓡 n) (x := p))
    simpa only [ContinuousLinearMap.comp_apply, hchartid,
      ContinuousLinearMap.id_apply] using hv.symm
  obtain ⟨A, hA, _⟩ := g.exists_frozenPullbackEquiv (f := e) (x := 0)
    (by intro v w hvw; simpa only [hde] using hvw)
  have hAnorm (v : EuclideanSpace ℝ (Fin n)) : ‖A v‖ = g.tangentNorm p v := by
    calc
      ‖A v‖ = g.tangentNorm (e 0) v := by simpa only [hde] using hA v
      _ = g.tangentNorm p v := by unfold tangentNorm; rw [he0]
  let K : ℝ≥0 := ⟨θ, (zero_lt_one.trans hθ).le⟩
  have hK : 1 < K := hθ
  obtain ⟨U, hU, h0U, _, hdist⟩ := g.exists_open_distortion_of_tangentNorm_comparison
    e he he' h0 A hK
    (g.eventually_pullbackNorm_comparison (he.contMDiffAt (e.open_source.mem_nhds h0))
      A hA hK)
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  refine ⟨ρ, hρ, ?_⟩
  intro v w hv hw
  have hvU : v ∈ U := hρU (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
  have hwU : w ∈ U := hρU (by simpa only [Metric.mem_ball, dist_zero_right] using hw)
  have hh := (hdist v hvU w hwU).1
  rw [edist_dist, dist_eq_norm', ← map_sub, hAnorm] at hh
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg] at hh
  exact hh



theorem normalized_initial_eq_neg_of_minimizing_broken_geodesics
    (g : RiemannianMetric n M) (p : M)
    {α β : ℝ → M}
    (hα : g.IsGeodesicOn α (Icc (0 : ℝ) 1))
    (hβ : g.IsGeodesicOn β (Icc (0 : ℝ) 1))
    (hα0 : α 0 = p) (hβ0 : β 0 = p)
    {w₁ w₂ : EuclideanSpace ℝ (Fin n)}
    (hαv : HasDerivAt (fun t => extChartAt (𝓡 n) p (α t)) w₁ 0)
    (hβv : HasDerivAt (fun t => extChartAt (𝓡 n) p (β t)) w₂ 0)
    (hA : 0 < g.tangentNorm p w₁) (hB : 0 < g.tangentNorm p w₂)
    (hαupper : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (α s) (α t) ≤ ENNReal.ofReal (|s - t| * g.tangentNorm p w₁))
    (hβupper : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (β s) (β t) ≤ ENNReal.ofReal (|s - t| * g.tangentNorm p w₂))
    (hdist : g.edist (α 1) (β 1) =
      ENNReal.ofReal (g.tangentNorm p w₁ + g.tangentNorm p w₂)) :
    (g.tangentNorm p w₂)⁻¹ • w₂ = -((g.tangentNorm p w₁)⁻¹ • w₁) := by
  obtain ⟨e, h0, he0, he, he', hd, Γ, _, hΓ⟩ := g.exists_exponential_chart p
  obtain ⟨r, hr, hrs⟩ := g.exists_tangentBall_subset_nhds p
    (e.open_source.mem_nhds h0)
  apply g.normalized_initial_eq_neg_of_minimizing_broken_geodesics_of_exponential
    p e hr ?_ (fun θ hθ => g.exists_exponential_chord_bound p e h0 he0 he he' hd hθ)
    hα hβ hα0 hβ0 hαv hβv hA hB hαupper hβupper hdist
  intro v hv
  obtain ⟨hinit, hend, _, hcurve⟩ := hΓ v (hrs hv)
  obtain ⟨hgeod, hstart, hvel⟩ := g.geodesic_of_coordinate_exponential p
    (fun t => Γ (v, t)) v hinit (fun t ht => ⟨(hcurve t ht).1, (hcurve t ht).2.1⟩)
  refine ⟨_, ?_, hstart, hvel, hend⟩
  intro t ht
  exact hgeod t ⟨by linarith [ht.1], by linarith [ht.2]⟩

end PoincareConjecture.RiemannianMetric
