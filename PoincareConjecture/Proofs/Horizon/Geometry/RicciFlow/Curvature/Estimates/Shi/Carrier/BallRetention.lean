import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricComparison.LocalCurvature

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Set

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem metric_edist_le_pathELength_local
    (g : RiemannianMetric n M) {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b))
    (hab : a ≤ b) :
    g.edist (γ a) (γ b) ≤ g.pathELength γ a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist (𝓡 n) (γ a) (γ b) ≤
    Manifold.pathELength (𝓡 n) γ a b
  exact Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab

private theorem metric_edist_triangle_local
    (g : RiemannianMetric n M) (x y z : M) :
    g.edist x z ≤ g.edist x y + g.edist y z := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_triangle

private theorem exists_contMDiff_path_length_lt_local
    (g : RiemannianMetric n M) {x y : M} {L : ℝ≥0∞}
    (hxy : g.edist x y < L) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ ∧ g.pathELength γ 0 1 < L := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨γ, h0, h1, hγ, hL, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hxy zero_lt_one
  exact ⟨γ, h0, h1, hγ, hL⟩

private theorem continuous_metric_edist_local [T2Space M]
    (g : RiemannianMetric n M) (p : M) :
    Continuous (fun x => g.edist p x) := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric (𝓡 n) M
  exact continuous_const.edist continuous_id

theorem ball_subset_of_local_tangentNorm_comparison [T2Space M]
    (g0 g1 : RiemannianMetric n M) (p x : M) {r q C L : ℝ}
    (hq : 0 ≤ q) (hC : 0 < C) (hL : 0 < L)
    (hmargin : q + C * L < r)
    (hcomp : ∀ y, y ∈ g0.ball p r → ∀ v : TangentSpace (𝓡 n) y,
      g0.tangentNorm y v ≤ C * g1.tangentNorm y v)
    (hx : x ∈ g0.ball p q) :
    g1.ball x L ⊆ g0.ball p (q + C * L) := by
  intro y hy
  change g1.edist x y < ENNReal.ofReal L at hy
  obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlen⟩ :=
    exists_contMDiff_path_length_lt_local g1 hy
  let Q : ℝ := q + C * L
  let A : Set ℝ := {s | g0.edist p (γ s) ≤ ENNReal.ofReal Q}
  have hQpos : 0 < Q := by
    dsimp [Q]
    nlinarith [mul_pos hC hL]
  have hQr : Q < r := by simpa [Q] using hmargin
  have hAclosed : IsClosed (A ∩ Icc 0 1) := by
    have hcont : Continuous (fun s => g0.edist p (γ s)) :=
      (continuous_metric_edist_local g0 p).comp hγsmooth.continuous
    exact (isClosed_le hcont continuous_const).inter isClosed_Icc
  have hAzero : (0 : ℝ) ∈ A := by
    have hx' : g0.edist p x < ENNReal.ofReal q := hx
    have hqQ : ENNReal.ofReal q ≤ ENNReal.ofReal Q := by
      exact ENNReal.ofReal_le_ofReal (le_of_lt (by
        dsimp [Q]
        nlinarith [mul_pos hC hL]))
    change g0.edist p (γ 0) ≤ ENNReal.ofReal Q
    rw [hγ0]
    exact (hx'.le.trans hqQ)
  have hstep : ∀ t ∈ Ico (0 : ℝ) 1, Icc 0 t ⊆ A → A ∈ 𝓝[>] t := by
    intro t ht hprefix
    have hprefixMap : MapsTo γ (Icc 0 t) (g0.ball p r) := by
      intro s hs
      have hsA : s ∈ A := hprefix hs
      change g0.edist p (γ s) < ENNReal.ofReal r
      exact (show g0.edist p (γ s) ≤ ENNReal.ofReal Q from hsA).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hQr)
    have hlenCmp := pathELength_le_of_tangentNorm_le g0 g1
      (C := C) hC.le hcomp γ hprefixMap
    have hlenMono : g1.pathELength γ 0 t ≤ g1.pathELength γ 0 1 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g1.toRiemannianMetric⟩
      exact Manifold.pathELength_mono le_rfl ht.2.le
    have hprefixShort : g1.pathELength γ 0 t < ENNReal.ofReal L :=
      hlenMono.trans_lt hγlen
    have hscaled :
        ENNReal.ofReal C * g1.pathELength γ 0 t <
          ENNReal.ofReal C * ENNReal.ofReal L := by
      simpa [mul_comm] using ENNReal.mul_lt_mul_left
        (a := ENNReal.ofReal C) (b := g1.pathELength γ 0 t)
        (c := ENNReal.ofReal L) (ne_of_gt (by positivity))
        ENNReal.ofReal_ne_top hprefixShort
    have hdist : g0.edist (γ 0) (γ t) ≤
        ENNReal.ofReal C * g1.pathELength γ 0 t := by
      exact (metric_edist_le_pathELength_local g0 hγsmooth.contMDiffOn ht.1).trans
        hlenCmp
    have htri := metric_edist_triangle_local g0 p (γ 0) (γ t)
    rw [hγ0] at htri
    have hstrict : g0.edist p (γ t) < ENNReal.ofReal Q := by
      have hsum : g0.edist p x + g0.edist x (γ t) <
          ENNReal.ofReal q + ENNReal.ofReal (C * L) := by
        have hxd : g0.edist p x < ENNReal.ofReal q := hx
        have hpath : g0.edist x (γ t) ≤
            ENNReal.ofReal C * g1.pathELength γ 0 t := by
          simpa [hγ0] using hdist
        have hscaled' : ENNReal.ofReal C * g1.pathELength γ 0 t <
            ENNReal.ofReal (C * L) := by
          calc
            _ < ENNReal.ofReal C * ENNReal.ofReal L := hscaled
            _ = ENNReal.ofReal (C * L) := (ENNReal.ofReal_mul hC.le).symm
        have hpath' : g0.edist x (γ t) < ENNReal.ofReal (C * L) :=
          hpath.trans_lt hscaled'
        exact (ENNReal.add_lt_add_right (a := g0.edist x (γ t))
            (b := g0.edist p x) (c := ENNReal.ofReal q)
            (ne_top_of_lt hpath') hxd).trans
          (ENNReal.add_lt_add_left (a := ENNReal.ofReal q)
            (b := g0.edist x (γ t)) (c := ENNReal.ofReal (C * L))
            ENNReal.ofReal_ne_top hpath')
      have hadd : ENNReal.ofReal q + ENNReal.ofReal (C * L) =
          ENNReal.ofReal Q := by
        rw [← ENNReal.ofReal_add hq (mul_nonneg hC.le hL.le)]
      rw [hadd] at hsum
      exact htri.trans_lt hsum
    have hcont : Continuous (fun s => g0.edist p (γ s)) :=
      (continuous_metric_edist_local g0 p).comp hγsmooth.continuous
    have hnhds : {s : ℝ | g0.edist p (γ s) < ENNReal.ofReal Q} ∈ 𝓝 t := by
      exact hcont.continuousAt (Iio_mem_nhds hstrict)
    exact Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds hnhds) (by
      intro s hs
      change g0.edist p (γ s) < ENNReal.ofReal Q at hs
      exact hs.le)
  have hAall : Icc (0 : ℝ) 1 ⊆ A := by
    apply hAclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hAzero
    exact hstep
  have hfullMap : MapsTo γ (Icc (0 : ℝ) 1) (g0.ball p r) := by
    intro s hs
    have hsA : s ∈ A := hAall hs
    change g0.edist p (γ s) < ENNReal.ofReal r
    exact hsA.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hQr)
  have hlenCmp := pathELength_le_of_tangentNorm_le g0 g1
    (C := C) hC.le hcomp γ hfullMap
  have hscaled :
      ENNReal.ofReal C * g1.pathELength γ 0 1 <
        ENNReal.ofReal C * ENNReal.ofReal L := by
    simpa [mul_comm] using ENNReal.mul_lt_mul_left
      (a := ENNReal.ofReal C) (b := g1.pathELength γ 0 1)
      (c := ENNReal.ofReal L) (ne_of_gt (by positivity))
      ENNReal.ofReal_ne_top hγlen
  have hdist : g0.edist (γ 0) (γ 1) ≤
      ENNReal.ofReal C * g1.pathELength γ 0 1 := by
    exact (metric_edist_le_pathELength_local g0 hγsmooth.contMDiffOn zero_le_one).trans
      hlenCmp
  have htri := metric_edist_triangle_local g0 p (γ 0) (γ 1)
  rw [hγ0, hγ1] at htri
  have hsum : g0.edist p x + g0.edist x y <
      ENNReal.ofReal q + ENNReal.ofReal (C * L) := by
    have hpath : g0.edist x y ≤
        ENNReal.ofReal C * g1.pathELength γ 0 1 := by
      simpa [hγ0, hγ1] using hdist
    have hscaled' : ENNReal.ofReal C * g1.pathELength γ 0 1 <
        ENNReal.ofReal (C * L) := by
      calc
        _ < ENNReal.ofReal C * ENNReal.ofReal L := hscaled
        _ = ENNReal.ofReal (C * L) := (ENNReal.ofReal_mul hC.le).symm
    have hpath' : g0.edist x y < ENNReal.ofReal (C * L) :=
      hpath.trans_lt hscaled'
    have hxd : g0.edist p x < ENNReal.ofReal q := hx
    exact (ENNReal.add_lt_add_right (a := g0.edist x y)
        (b := g0.edist p x) (c := ENNReal.ofReal q)
        (ne_top_of_lt hpath') hxd).trans
      (ENNReal.add_lt_add_left (a := ENNReal.ofReal q)
        (b := g0.edist x y) (c := ENNReal.ofReal (C * L))
        ENNReal.ofReal_ne_top hpath')
  have hadd : ENNReal.ofReal q + ENNReal.ofReal (C * L) =
      ENNReal.ofReal Q := by
    rw [← ENNReal.ofReal_add hq (mul_nonneg hC.le hL.le)]
  rw [hadd] at hsum
  change g0.edist p y < ENNReal.ofReal Q
  exact htri.trans_lt hsum

theorem exists_compact_carrier_for_flow_balls [T2Space M]
    {T K α r : ℝ} (F : RicciFlow n M (Icc 0 T))
    (hK : 0 < K) (hr : 0 < r) (hT0 : 0 ≤ T)
    (hT : T ≤ α / K) (p : M)
    (hcompact : IsCompact (closure ((F.metric 0).ball p r)))
    (hRm : ∀ t ∈ Icc 0 T, ∀ y ∈ (F.metric 0).ball p r,
      (F.connection t).curvatureTensorNorm y ≤ K)
    (x : M) (hx : x ∈ (F.metric 0).ball p (r / 2)) :
    ∃ R : ℝ, 0 < R ∧ R < 3 * r / 4 ∧
      IsCompact {y | (F.metric 0).edist p y ≤ ENNReal.ofReal R} ∧
      {y | (F.metric 0).edist p y ≤ ENNReal.ofReal R} ⊆
        (F.metric 0).ball p (3 * r / 4) ∧
      ∀ t ∈ Icc 0 T,
        closure ((F.metric t).ball x (Real.exp (-(n : ℝ) * α) * r / 4)) ⊆
          {y | (F.metric 0).edist p y ≤ ENNReal.ofReal R} := by
  have hx' : (F.metric 0).edist p x < ENNReal.ofReal (r / 2) := hx
  have hd : ((F.metric 0).edist p x).toReal < r / 2 :=
    ENNReal.toReal_lt_of_lt_ofReal hx'
  obtain ⟨q, hdq, hqr⟩ := exists_between hd
  have hq : 0 < q := (ENNReal.toReal_nonneg).trans_lt hdq
  have hxq : x ∈ (F.metric 0).ball p q := by
    change (F.metric 0).edist p x < ENNReal.ofReal q
    calc
      _ = ENNReal.ofReal ((F.metric 0).edist p x).toReal :=
        (ENNReal.ofReal_toReal (ne_top_of_lt hx')).symm
      _ < ENNReal.ofReal q := (ENNReal.ofReal_lt_ofReal_iff hq).2 hdq
  let R : ℝ := q + r / 4
  have hRpos : 0 < R := by dsimp [R]; linarith
  have hRlt : R < 3 * r / 4 := by dsimp [R]; linarith
  have hRr : R < r := by linarith
  have hclosed : IsClosed {y | (F.metric 0).edist p y ≤ ENNReal.ofReal R} :=
    isClosed_le (continuous_metric_edist_local (F.metric 0) p) continuous_const
  have hsub : {y | (F.metric 0).edist p y ≤ ENNReal.ofReal R} ⊆
      (F.metric 0).ball p (3 * r / 4) := by
    intro y hy
    change (F.metric 0).edist p y < ENNReal.ofReal (3 * r / 4)
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hRlt)
  have hsubOuter : {y | (F.metric 0).edist p y ≤ ENNReal.ofReal R} ⊆
      closure ((F.metric 0).ball p r) := by
    intro y hy
    apply subset_closure
    change (F.metric 0).edist p y < ENNReal.ofReal r
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).2 hRr)
  refine ⟨R, hRpos, hRlt, hcompact.of_isClosed_subset hclosed hsubOuter, hsub, ?_⟩
  intro t ht
  have hscale : Real.exp ((n : ℝ) * α) *
      (Real.exp (-(n : ℝ) * α) * r / 4) = r / 4 := by
    rw [mul_div_assoc, ← mul_assoc, ← Real.exp_add]
    simp
  have hretain :
      (F.metric t).ball x (Real.exp (-(n : ℝ) * α) * r / 4) ⊆
        (F.metric 0).ball p R := by
    have h := ball_subset_of_local_tangentNorm_comparison (F.metric 0) (F.metric t)
      p x hq.le (Real.exp_pos ((n : ℝ) * α))
      (by positivity : 0 < Real.exp (-(n : ℝ) * α) * r / 4)
      (show q + Real.exp ((n : ℝ) * α) *
          (Real.exp (-(n : ℝ) * α) * r / 4) < r by
        rw [hscale]
        exact hRr)
      (fun y hy v => (tangentNorm_comparison_on_initial_ball F hK hT0 hT p hRm
        ht hy v).1) hxq
    simpa only [hscale, R] using h
  apply closure_minimal _ hclosed
  intro y hy
  have hy' := hretain hy
  change (F.metric 0).edist p y < ENNReal.ofReal R at hy'
  exact hy'.le

end PoincareConjecture.RicciFlowAnalysis
