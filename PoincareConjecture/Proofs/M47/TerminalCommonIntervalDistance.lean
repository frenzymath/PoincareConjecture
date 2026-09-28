import PoincareConjecture.Proofs.M47.TerminalCommonIntervalCapture

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M47

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [T3Space M] [T2Space N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]

theorem terminalCommonInterval_buffered_distance
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (hg : MetricComplete g) (e : OpenPartialHomeomorph M N)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target)
    (p : M) {R lambda : ℝ} (hR : 0 < R) (hlambda : 0 < lambda)
    (hsource : {z | g.edist p z ≤ ENNReal.ofReal (4 * (R + 1))} ⊆ e.source)
    (hbound : ∀ z, g.edist p z ≤ ENNReal.ofReal (4 * (R + 1)) →
      ∀ v : TangentSpace (𝓡 3) z,
        lambda * g.tangentNorm z v ≤
          h.tangentNorm (e z) (mfderiv (𝓡 3) (𝓡 3) e z v) ∧
        h.tangentNorm (e z) (mfderiv (𝓡 3) (𝓡 3) e z v) ≤
          lambda⁻¹ * g.tangentNorm z v) :
    ∀ x, g.edist p x ≤ ENNReal.ofReal R →
      ∀ y, g.edist p y ≤ ENNReal.ofReal R →
        ENNReal.ofReal lambda * g.edist x y ≤ h.edist (e x) (e y) ∧
        h.edist (e x) (e y) ≤ ENNReal.ofReal lambda⁻¹ * g.edist x y := by
  let : EMetricSpace M := g.toEMetricSpace
  intro x hx y hy
  let b := 2 * R + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hcenter (z : M) (hz : g.edist x z ≤ ENNReal.ofReal b) :
      g.edist p z ≤ ENNReal.ofReal (4 * (R + 1)) := by
    calc
      _ ≤ g.edist p x + g.edist x z := edist_triangle p x z
      _ ≤ ENNReal.ofReal R + ENNReal.ofReal b := add_le_add hx hz
      _ = ENNReal.ofReal (R + b) := (ENNReal.ofReal_add hR.le hb.le).symm
      _ ≤ ENNReal.ofReal (4 * (R + 1)) := ENNReal.ofReal_le_ofReal (by dsimp [b]; linarith)
  have hxy : g.edist x y ≤ ENNReal.ofReal (2 * R) := by
    calc
      _ ≤ g.edist x p + g.edist p y := edist_triangle x p y
      _ = g.edist p x + g.edist p y := by rw [show g.edist x p = g.edist p x from edist_comm x p]
      _ ≤ ENNReal.ofReal R + ENNReal.ofReal R := add_le_add hx hy
      _ = ENNReal.ofReal (2 * R) := by rw [← ENNReal.ofReal_add hR.le hR.le]; congr 1; ring
  have hfinite : g.edist x y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxy
  let d := (g.edist x y).toReal
  have hd : ENNReal.ofReal d = g.edist x y := ENNReal.ofReal_toReal hfinite
  have hdR : d ≤ 2 * R := by
    simpa only [d, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * R)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hxy
  have hdb : d < b := by dsimp [b]; linarith
  have hinv : 0 < lambda⁻¹ := inv_pos.mpr hlambda
  have hreverse (z : M) (hz : g.edist x z ≤ ENNReal.ofReal b)
      (v : TangentSpace (𝓡 3) z) :
      g.tangentNorm z v ≤ lambda⁻¹ * h.tangentNorm (e z)
        (mfderiv (𝓡 3) (𝓡 3) e z v) := by
    have hc := (le_div_iff₀ hlambda).mpr
      (by simpa only [mul_comm] using (hbound z (hcenter z hz) v).1)
    simpa only [div_eq_mul_inv, mul_comm] using hc
  constructor
  · by_contra hnot
    have hlt := lt_of_not_ge hnot
    have hrad : lambda⁻¹ * (lambda * d) = d := by field_simp
    have hey : e y ∈ h.ball (e x) (lambda * d) := by
      change h.edist (e x) (e y) < ENNReal.ofReal (lambda * d)
      rwa [ENNReal.ofReal_mul hlambda.le, hd]
    obtain ⟨z, hz, hzy⟩ := terminalCommonInterval_capture_of_closed_buffer
      g h hg e hf hi x hb hinv (by simpa only [hrad] using hdb)
      (fun z hz => hsource (hcenter z hz)) hreverse hey
    have hz' : g.edist x z < g.edist x y := by
      simpa only [RiemannianMetric.ball, mem_ofPred_eq, hrad, hd] using hz
    have htwo : ENNReal.ofReal (2 * R) ≤ ENNReal.ofReal b :=
      ENNReal.ofReal_le_ofReal (by dsimp [b]; linarith)
    have hzs : z ∈ e.source := hsource (hcenter z (hz'.le.trans (hxy.trans htwo)))
    have hys : y ∈ e.source := hsource (hcenter y (hxy.trans htwo))
    have hzeq := e.injOn hzs hys hzy
    subst z
    exact (lt_irrefl _) hz'
  · have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (lambda⁻¹ * r)) (𝓝[>] d)
        (𝓝 (ENNReal.ofReal (lambda⁻¹ * d))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        (((continuous_const.mul continuous_id).tendsto d).mono_left nhdsWithin_le_nhds)
    rw [← hd, ← ENNReal.ofReal_mul hinv.le]
    apply ge_of_tendsto hlim
    have hsmall : ∀ᶠ r : ℝ in 𝓝[>] d, r < b :=
      (gt_mem_nhds hdb).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrb
    have hyball : y ∈ g.ball x r := by
      change g.edist x y < ENNReal.ofReal r
      rw [← hd]
      exact ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt ENNReal.toReal_nonneg hr) |>.mpr hr
    have hball : g.ball x r ⊆ e.source := by
      intro z hz
      exact hsource (hcenter z (hz.le.trans (ENNReal.ofReal_le_ofReal hrb.le)))
    have himage := g.image_ball_subset_ball_of_tangentNorm_le h e x hinv hball
      (fun z hz => (hf z hz).contMDiffAt (e.open_source.mem_nhds hz))
      (fun z hz v => (hbound z (hcenter z
        (hz.le.trans (ENNReal.ofReal_le_ofReal hrb.le))) v).2)
    exact le_of_lt (himage (mem_image_of_mem e hyball))

end PoincareConjecture.M47
