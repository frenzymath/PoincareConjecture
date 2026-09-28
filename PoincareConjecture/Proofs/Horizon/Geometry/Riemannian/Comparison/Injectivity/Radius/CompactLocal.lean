import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.LowerSemicontinuity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.TwoGeodesics








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_pos_eventually_le_truncatedInjectivityRadius
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    {C : ℝ} (hC : 0 < C) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ q in 𝓝 p, r ≤ g.truncatedInjectivityRadius hc C q := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p
  have hinj : Function.Injective
      (mfderiv (𝓡 n) (𝓡 n) (fun v => g.chartGlobalExponential hc p (c p, v)) 0) := by
    rw [g.chartGlobalExponential_center hc p]
    obtain ⟨e, he0, _, he, he', _, heq⟩ :=
      g.exists_exponential_chart_eq_globalExponential_nhds hc p
    rw [heq.mfderiv_eq]
    exact (show e.MDifferentiable (𝓡 n) (𝓡 n) from
      ⟨he.mdifferentiableOn (by simp), he'.mdifferentiableOn (by simp)⟩).mfderiv_injective he0
  obtain ⟨W, hW, hinjW⟩ := Poincare.exists_injOn_total_map_of_injective_fiber_mfderiv
    (g.contMDiffAt_chartGlobalExponential hc p (z := (c p, (0 : E)))
      (mem_extChartAt_target p)) hinj
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨s, hs, hsV⟩ := g.exists_tangentBall_subset_nhds p hV
  obtain ⟨L, hL⟩ := g.exists_orthonormal_coordinate_frame p
  have hnorm (v : E) : g.tangentNorm p v = ‖L.symm v‖ := by
    simpa only [L.apply_symm_apply] using g.tangentNorm_orthonormal_frame p L hL (L.symm v)
  have hcSmooth : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm (c p) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds (mem_extChartAt_target p))
  have hframe (v : E) : ‖L.symm v‖ =
      g.tangentNorm (c.symm (c p)) (mfderiv (𝓡 n) (𝓡 n) c.symm (c p) v) := by
    have hd := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := p)
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hd
    have hvec : mfderiv (𝓡 n) (𝓡 n) c.symm (c p) v = v :=
      congrArg (fun A => A v) hd
    rw [hvec, c.left_inv (mem_extChartAt_source p)]
    exact (hnorm v).symm
  have hcomparison := g.eventually_pullbackNorm_comparison hcSmooth L.symm hframe
    (by norm_num : (1 : ℝ≥0) < 2)
  let r := min (s / 2) C
  have hr : 0 < r := lt_min (half_pos hs) hC
  have hnear : ∀ᶠ x in 𝓝 (c p), r ≤ g.truncatedInjectivityRadius hc C (c.symm x) := by
    filter_upwards [hU, hcomparison,
      (isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds (mem_extChartAt_target p)]
      with x hxU hxnorm hx
    apply g.le_truncatedInjectivityRadius hc (c.symm x) hr.le (min_le_right _ _)
    let A : E →L[ℝ] E := mfderiv (𝓡 n) (𝓡 n) c (c.symm x)
    have hinverse (v : E) : mfderiv (𝓡 n) (𝓡 n) c.symm x (A v) = v := by
      have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓡 n) hx
      simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
      exact congrArg (fun B => B v) h
    have hmem (v : E) (hv : g.tangentNorm (c.symm x) v < r) : A v ∈ V := by
      apply hsV
      change g.tangentNorm p (A v) < s
      rw [hnorm]
      have h := (hxnorm (A v)).1
      rw [hinverse] at h
      have hrsmall : r ≤ s / 2 := min_le_left _ _
      norm_num only [NNReal.coe_ofNat] at h
      linarith
    intro v hv w hw heq
    have hco : A v = A w := congrArg Prod.snd
      (hinjW (x₁ := (x, A v)) (x₂ := (x, A w))
        (hUV ⟨hxU, hmem v hv⟩) (hUV ⟨hxU, hmem w hw⟩) (by
        refine Prod.ext (by rfl) ?_
        change g.globalExponential hc (c.symm x)
          (mfderiv (𝓡 n) (𝓡 n) c.symm x (A v)) =
          g.globalExponential hc (c.symm x) (mfderiv (𝓡 n) (𝓡 n) c.symm x (A w))
        rwa [hinverse, hinverse]))
    have h := congrArg (fun u => mfderiv (𝓡 n) (𝓡 n) c.symm x u) hco
    simpa only [hinverse] using h
  refine ⟨r, hr, ?_⟩
  filter_upwards [(continuousAt_extChartAt p).preimage_mem_nhds hnear,
    (isOpen_extChartAt_source (I := 𝓡 n) p).mem_nhds (mem_extChartAt_source p)]
    with q hq hqc
  change r ≤ g.truncatedInjectivityRadius hc C (c.symm (c q)) at hq
  simpa only [c.left_inv hqc] using hq



theorem exists_pos_le_truncatedInjectivityRadius_on_isCompact_of_complete
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    {C : ℝ} (hC : 0 < C) {S : Set M} (hS : IsCompact S) :
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ S, r ≤ g.truncatedInjectivityRadius hc C p := by
  classical
  choose r hr hlocal using fun p => g.exists_pos_eventually_le_truncatedInjectivityRadius hc hC p
  let U : M → Set M := fun p => {q | r p ≤ g.truncatedInjectivityRadius hc C q}
  obtain ⟨s, _, hs⟩ := hS.elim_nhds_subcover U (fun p _ => hlocal p)
  refine ⟨s.fold min 1 r, (Finset.lt_fold_min (0 : ℝ)).mpr
    ⟨zero_lt_one, fun p _ => hr p⟩, ?_⟩
  intro p hp
  obtain ⟨q, hq, hpq⟩ := Set.mem_iUnion₂.mp (hs hp)
  exact ((Finset.fold_min_le (r q)).mpr (Or.inr ⟨q, hq, le_rfl⟩)).trans hpq



theorem exists_local_distance_ascent_of_lt_truncatedInjectivityRadius
    [PreconnectedSpace M] (g : RiemannianMetric n M) (hc : MetricComplete g)
    {C c : ℝ} (hC : 0 ≤ C) (hcrate : c < 1) (p y : M)
    (hypos : 0 < (g.edist p y).toReal)
    (hy : (g.edist p y).toReal < g.truncatedInjectivityRadius hc C p) :
    ∀ s : ℝ, 0 < s → ∃ z : M, (g.edist y z).toReal < s ∧
      c * (g.edist y z).toReal < (g.edist p z).toReal - (g.edist p y).toReal := by
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hc p y
  let v := deriv (fun t => extChartAt (𝓡 n) p (γ t)) 0
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  have hvder : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 :=
    (hγ.hasDerivAt_chart_at h0 p
      (by simpa only [hγ0] using mem_extChartAt_source p)).1
  have hvnorm : g.tangentNorm p v = (g.edist p y).toReal := by
    have h := congrArg ENNReal.toReal
      (hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hvder hmin)
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ g.tangentNorm p v from
      Real.sqrt_nonneg _)] using h
  have hvy : g.globalExponential hc p v = y := by
    rw [← hγ1]
    apply g.globalExponential_eq_endpoint hc p v _ hγ0 hvder
    intro t ht
    exact hγ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let a := (g.edist p y).toReal
  have ha : 0 < a := hypos
  have hnorm (t : ℝ) (ht : 0 ≤ t) : g.tangentNorm p (t • v) = t * a := by
    simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
    exact congrArg (t * ·) hvnorm
  intro s hs
  let δ := min s (g.truncatedInjectivityRadius hc C p - a) / 2
  have hδ : 0 < δ := half_pos (lt_min hs (sub_pos.mpr hy))
  have hδs : δ < s := by
    dsimp only [δ]
    linarith [min_le_left s (g.truncatedInjectivityRadius hc C p - a)]
  have haδ : a + δ < g.truncatedInjectivityRadius hc C p := by
    dsimp only [δ]
    linarith [min_le_right s (g.truncatedInjectivityRadius hc C p - a)]
  let w := ((a + δ) / a) • v
  have hw : g.tangentNorm p w = a + δ := by
    rw [hnorm _ (div_nonneg (by linarith) ha.le), div_mul_cancel₀ _ ha.ne']
  let z := g.globalExponential hc p w
  have hpz : (g.edist p z).toReal = a + δ := by
    rw [g.edist_globalExponential_eq_tangentNorm_of_lt_truncatedInjectivityRadius
      hc hC p (by rw [hw]; exact haδ), hw, ENNReal.toReal_ofReal (by linarith)]
  have ht : a / (a + δ) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ha.le (by linarith), (div_le_one (by linarith)).mpr (by linarith)⟩
  have hscaled : (a / (a + δ)) • w = v := by
    dsimp only [w]
    rw [smul_smul]
    have hcancel : a / (a + δ) * ((a + δ) / a) = 1 := by
      field_simp
    rw [hcancel, one_smul]
  have hleft : g.globalGeodesic hc p w (a / (a + δ)) = y := by
    rw [← g.globalExponential_smul_eq_globalGeodesic, hscaled, hvy]
  have hyzle : (g.edist y z).toReal ≤ δ := by
    have hd := g.edist_globalGeodesic_le_tangentNorm hc p w ht
      (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    have heq : |a / (a + δ) - 1| * g.tangentNorm p w = δ := by
      rw [abs_of_nonpos (by linarith [ht.2]), hw]
      field_simp
      ring
    rw [hleft, heq] at hd
    change g.edist y z ≤ ENNReal.ofReal δ at hd
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hd).trans_eq
      (ENNReal.toReal_ofReal hδ.le)
  have hyzge : δ ≤ (g.edist y z).toReal := by
    have h := (abs_le.mp (g.abs_toReal_edist_sub_le p y z)).1
    rw [hpz] at h
    change - (g.edist y z).toReal ≤ a - (a + δ) at h
    linarith
  have hyz : (g.edist y z).toReal = δ := le_antisymm hyzle hyzge
  refine ⟨z, hyz ▸ hδs, ?_⟩
  rw [hyz, hpz]
  change c * δ < a + δ - a
  nlinarith

end PoincareConjecture.RiemannianMetric
