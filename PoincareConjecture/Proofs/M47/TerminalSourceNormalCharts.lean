import PoincareConjecture.Proofs.M47.TerminalSourceCharts
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.Uniform









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M]

private theorem normalChart_radial_speed
    (g : RiemannianMetric 3 M) (Phi : E → M) (p : M) (L : E ≃L[ℝ] E)
    {R ρ : ℝ} (hρR : ρ < R) (hzero : Phi 0 = p)
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 3) p).symm
      (extChartAt (𝓡 3) p p) (L v) (L w) = inner ℝ v w)
    (hd : HasFDerivAt (fun w => extChartAt (𝓡 3) p (Phi w)) L.toContinuousLinearMap 0)
    (hgeo : ∀ w ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => Phi (t • w)) {t | t • w ∈ Metric.ball 0 R})
    {w : E} (hw : w ∈ Metric.ball 0 ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    g.tangentNorm (Phi (t • w))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s : ℝ => Phi (s • w)) t 1) = ‖w‖ := by
  by_cases hw0 : w = 0
  · subst w
    have heq : (fun s : ℝ => Phi (s • (0 : E))) = fun _ : ℝ => Phi 0 := by
      funext s
      congr 1
      exact smul_zero s
    rw [heq, mfderiv_const]
    simp [RiemannianMetric.tangentNorm]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hwρ : ‖w‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hw
  let d := ρ / ‖w‖
  have hd1 : 1 < d := (lt_div_iff₀ hn).mpr (by simpa using hwρ)
  have hγ : g.IsGeodesicOn (fun s : ℝ => Phi (s • w)) (Ioo (-d) d) := by
    intro s hs
    apply hgeo w (Metric.ball_subset_ball hρR.le hw) s
    have habs : |s| < d := abs_lt.mpr hs
    have hmul := mul_lt_mul_of_pos_right habs hn
    have hdw : d * ‖w‖ = ρ := div_mul_cancel₀ ρ hn.ne'
    rw [hdw] at hmul
    simpa only [mem_ofPred_eq, Metric.mem_ball, dist_zero_right, norm_smul,
      Real.norm_eq_abs] using! hmul.trans hρR
  have h0 : (0 : ℝ) ∈ Ioo (-d) d := by constructor <;> linarith
  have ht' : t ∈ Ioo (-d) d := by constructor <;> linarith [ht.1, ht.2]
  have hstart : Phi ((0 : ℝ) • w) = p := by simpa only [zero_smul] using hzero
  have hderiv : HasDerivAt (fun s : ℝ => extChartAt (𝓡 3) p (Phi (s • w))) (L w) 0 := by
    simpa only [Function.comp_def, one_smul, id_eq] using!
      hd.comp_hasDerivAt_of_eq 0 ((hasDerivAt_id 0).smul_const w) (by simp)
  obtain ⟨c, hc⟩ := hγ.exists_constant_tangentNorm (h0.1.trans h0.2)
  have hc0 := hc 0 h0
  rw [hγ.tangentNorm_initial h0 hstart hderiv, hL,
    real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg w)] at hc0
  exact (hc t ht').trans hc0.symm

variable [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]



theorem terminalSourceNormal_of_center
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (p0 p : M)
    {A R r K v : ℝ} (hK : 0 ≤ K) (hA : 0 < A) (hr : 0 < r) (hv : 0 < v)
    (hAR : A ≤ R) (hAr : A + r ≤ R) (hp : p ∈ g.ball p0 A)
    (hcompact : IsCompact (closure (g.ball p0 (5 * R))))
    (hcurv : ∀ x ∈ g.ball p0 (5 * R), D.curvatureTensorNorm x ≤ K)
    (hvol : ENNReal.ofReal v ≤ g.volumeMeasure (g.ball p0 r)) :
    let ρ := RiemannianMetric.localInjectivityRadius 3 K R v
    0 < ρ ∧ ρ < R ∧ ∃ C : TerminalSourceChart g ρ, C.centre = p := by
  obtain ⟨hρ, hρR, L, Phi, hs, ht, hzero, hL, hd, hgeo, hdist⟩ :=
    g.exists_uniform_precompact_exponential_diffeomorph_of_center D p0 p
      (by norm_num) hK hA hr hv hAR hAr hp hcompact hcurv hvol
  refine ⟨hρ, hρR, {
    chart := Phi
    centre := p
    source := hs
    target := ht
    zero := hzero
    normalized := ?_
    radial := ?_
    speed := ?_
    distance := hdist
  }, rfl⟩
  · apply g.pullbackCoefficients_zero_of_normalized_chart _ hzero hd hL
    exact Phi.contMDiffOn.contMDiffAt (Phi.open_source.mem_nhds
      (hs.symm ▸ Metric.mem_ball_self hρ))
  · intro w hw t ht'
    exact hgeo w (Metric.ball_subset_ball hρR.le hw) t
      (Metric.ball_subset_ball hρR.le ht')
  · intro w hw t ht'
    exact normalChart_radial_speed g Phi p L hρR hzero hL hd hgeo hw ht'

end PoincareConjecture.M47
