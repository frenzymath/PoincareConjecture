import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.GeodesicLength
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.ExponentialRays
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.NormalBall
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.RadialCurve
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Gauss.Manifold














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem geodesic_endpoint_eq_of_initial_data
    {g : RiemannianMetric n M} {p : M} {γ η : ℝ → M}
    (hγ : g.IsGeodesicOn γ (Icc (0 : ℝ) 1))
    (hη : g.IsGeodesicOn η (Icc (0 : ℝ) 1))
    (hγ0 : γ 0 = p) (hη0 : η 0 = p)
    {v : EuclideanSpace ℝ (Fin n)}
    (hγv : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0)
    (hηv : HasDerivAt (fun t => extChartAt (𝓡 n) p (η t)) v 0) :
    γ 1 = η 1 := by
  have heq := hγ.eq_nhds_of_initial_data hη (t₀ := 0) (by simp) p
    (by simpa only [hγ0] using mem_extChartAt_source p)
    (hγ0.trans hη0.symm) (hγv.deriv.trans hηv.deriv.symm)
  exact hγ.eqOn_of_eq_nhds hη (convex_Icc (0 : ℝ) 1).isPreconnected
    (by simp) heq (by simp)

omit [T2Space M] in
private theorem tangentNorm_smul_nonneg (g : RiemannianMetric n M)
    (p : M) (v : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 ≤ t) :
    g.tangentNorm p (t • v) = t * g.tangentNorm p v := by
  simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]

omit [T2Space M] in


theorem IsGeodesicOn.pathELength_eq_initial_tangentNorm
    {g : RiemannianMetric n M} {p : M} {γ : ℝ → M} {ε : ℝ}
    (hγ : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε))) (hε : 0 < ε)
    (hγ0 : γ 0 = p) {v : EuclideanSpace ℝ (Fin n)}
    (hγv : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0) :
    g.pathELength γ 0 1 = ENNReal.ofReal (g.tangentNorm p v) := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm (by linarith)
  have hC0 : g.tangentNorm p v = C := by
    have h := (hγ.tangentNorm_initial h0 hγ0 hγv).symm.trans (hC 0 h0)
    simpa only [chartCoefficients_self, tangentNorm] using h
  have hlength := g.pathELength_eq_of_tangentNorm_eq (C := (C : ℝ))
    (fun t (ht : t ∈ Icc (0 : ℝ) 1) =>
      hC t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  simpa only [sub_zero, ENNReal.ofReal_one, mul_one, hC0] using hlength

private theorem initial_tangentNorm_eq_of_local_exponential
    (g : RiemannianMetric n M) {p q : M} {γ : ℝ → M}
    {ε : ℝ} (hε : 0 < ε)
    (hγ : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε))) (hγ0 : γ 0 = p)
    {v : EuclideanSpace ℝ (Fin n)}
    (hγv : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p q)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : V ∈ 𝓝 0)
    (e : EuclideanSpace ℝ (Fin n) → M)
    (hexp : ∀ w ∈ V, ∃ η : ℝ → M,
      g.IsGeodesicOn η (Icc (0 : ℝ) 1) ∧ η 0 = p ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (η t)) w 0 ∧ η 1 = e w)
    (hedist : ∀ w ∈ V, g.edist p (e w) = ENNReal.ofReal (g.tangentNorm p w)) :
    ENNReal.ofReal (g.tangentNorm p v) = g.edist p q := by
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, t • v ∈ V :=
    (show ContinuousAt (fun t : ℝ => t • v) 0 by fun_prop).preimage_mem_nhds
      (by simpa only [zero_smul] using hV)
  obtain ⟨a, b, h0ab, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hsmall
  let t : ℝ := min b 1 / 2
  have hb : 0 < b := h0ab.2
  have ht : 0 < t := by dsimp [t]; positivity
  have htb : t < b := by dsimp [t]; have := min_le_left b 1; linarith
  have ht1 : t ≤ 1 := by dsimp [t]; have := min_le_right b 1; linarith
  have htv : t • v ∈ V := hab ⟨by linarith [h0ab.1], htb⟩
  obtain ⟨η, hη, hη0, hηv, hη1⟩ := hexp (t • v) htv
  have hscale : g.IsGeodesicOn (fun u => γ (t * u)) (Icc (0 : ℝ) 1) := by
    intro u hu
    apply hγ.comp_mul t u
    change t * u ∈ Ioo (-ε) (1 + ε)
    have hnonneg := mul_nonneg ht.le hu.1
    have hone := mul_le_one₀ ht1 hu.1 hu.2
    constructor <;> linarith
  have hd : HasDerivAt (fun u => extChartAt (𝓡 n) p (γ (t * u)))
      (t • v) 0 := by
    have hd0 : HasDerivAt (fun u => extChartAt (𝓡 n) p (γ u)) v (t * 0) := by
      simpa only [mul_zero] using hγv
    simpa only [mul_one, Function.comp_def] using
      hd0.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul t)
  have heq : γ t = e (t • v) := by
    have h := geodesic_endpoint_eq_of_initial_data hscale hη
      (by simpa only [mul_zero] using hγ0) hη0 hd hηv
    simpa only [mul_one, hη1] using h
  have hdist := hmin 0 (by simp) t ⟨ht.le, ht1⟩
  rw [hγ0, heq, hedist _ htv, tangentNorm_smul_nonneg g p v ht.le,
    ENNReal.ofReal_mul ht.le] at hdist
  simp only [zero_sub, abs_neg, abs_of_pos ht] at hdist
  exact (ENNReal.mul_right_inj (by positivity : ENNReal.ofReal t ≠ 0)
    ENNReal.ofReal_ne_top).mp hdist



theorem IsGeodesicOn.initial_tangentNorm_eq_of_edist_segment
    {g : RiemannianMetric n M} {p q : M} {γ : ℝ → M} {ε : ℝ}
    (hγ : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε))) (hε : 0 < ε)
    (hγ0 : γ 0 = p) {v : EuclideanSpace ℝ (Fin n)}
    (hγv : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p q) :
    ENNReal.ofReal (g.tangentNorm p v) = g.edist p q := by
  obtain ⟨e, he0, hep, he, he', hgauss, _, Γ, _, hΓ⟩ :=
    g.exists_exponential_chart_gauss p
  obtain ⟨r, hr, hsource, hedist⟩ :=
    g.exists_tangentBall_edist_eq_of_gauss p e he0 hep he he' hgauss
  have hV : {w : EuclideanSpace ℝ (Fin n) | g.tangentNorm p w < r} ∈ 𝓝 0 := by
    have hc : Continuous (fun w : EuclideanSpace ℝ (Fin n) => g.tangentNorm p w) := by
      unfold tangentNorm
      exact Real.continuous_sqrt.comp
        ((continuous_const.clm_apply continuous_id).clm_apply continuous_id)
    apply (isOpen_lt hc continuous_const).mem_nhds
    simpa only [mem_ofPred_eq, tangentNorm, map_zero, Real.sqrt_zero] using hr
  apply initial_tangentNorm_eq_of_local_exponential g hε hγ hγ0 hγv hmin hV e
  · intro w hw
    obtain ⟨hinit, hend, hode⟩ := hΓ w (hsource hw)
    obtain ⟨hη, hη0, hηv⟩ := g.geodesic_of_coordinate_exponential p
      (fun t => Γ (w, t)) w hinit hode
    refine ⟨fun t => (extChartAt (𝓡 n) p).symm (Γ (w, t)).1,
      ?_, hη0, hηv, hend⟩
    intro t ht
    exact hη t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · exact hedist



theorem IsGeodesicOn.pathELength_eq_of_edist_segment
    {g : RiemannianMetric n M} {p q : M} {γ : ℝ → M} {ε : ℝ}
    (hγ : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε))) (hε : 0 < ε)
    (hγ0 : γ 0 = p)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p q) :
    g.pathELength γ 0 1 = g.edist p q := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  have hv := (hγ.hasDerivAt_chart_at h0 p
    (by simpa only [hγ0] using mem_extChartAt_source p)).1
  exact (hγ.pathELength_eq_initial_tangentNorm hε hγ0 hv).trans
    (hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hv hmin)

end PoincareConjecture.RiemannianMetric
