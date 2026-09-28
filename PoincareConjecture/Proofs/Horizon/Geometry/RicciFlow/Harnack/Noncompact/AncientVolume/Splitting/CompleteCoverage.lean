import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.GeometricLine
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.PointedGeometricConvergence

private theorem exists_first_exit_of_closed_superset
    {X : Type*} [TopologicalSpace X] {γ : ℝ → X} {O K : Set X}
    (hO : IsOpen O) (hK : IsClosed K) (hOK : O ⊆ K)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1)) (h0 : γ 0 ∈ O) (h1 : γ 1 ∉ O) :
    ∃ t ∈ Ioc (0 : ℝ) 1, γ t ∈ K ∧ γ t ∉ O ∧
      ∀ s ∈ Ico (0 : ℝ) t, γ s ∈ O := by
  let S : Set ℝ := {t ∈ Icc (0 : ℝ) 1 | γ t ∉ O}
  have hS : IsClosed S :=
    hγ.preimage_isClosed_of_isClosed isClosed_Icc hO.isClosed_compl
  have hSne : S.Nonempty := ⟨1, ⟨by norm_num, h1⟩⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  have htS : sInf S ∈ S := hS.csInf_mem hSne hSbdd
  have htpos : 0 < sInf S :=
    lt_of_le_of_ne htS.1.1 (fun h => (h ▸ htS).2 h0)
  have hbelow : ∀ s ∈ Ico (0 : ℝ) (sInf S), γ s ∈ O := by
    intro s hs
    by_contra hnot
    exact (not_le.mpr hs.2) (csInf_le hSbdd ⟨⟨hs.1, hs.2.le.trans htS.1.2⟩, hnot⟩)
  have hclosed : IsClosed (Icc (0 : ℝ) 1 ∩ γ ⁻¹' K) :=
    hγ.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hsub : Ico (0 : ℝ) (sInf S) ⊆ Icc (0 : ℝ) 1 ∩ γ ⁻¹' K := by
    intro s hs
    exact ⟨⟨hs.1, hs.2.le.trans htS.1.2⟩, hOK (hbelow s hs)⟩
  have htK : sInf S ∈ Icc (0 : ℝ) 1 ∩ γ ⁻¹' K := by
    apply hclosed.closure_subset_iff.mpr hsub
    rw [closure_Ico htpos.ne]
    exact ⟨htpos.le, le_rfl⟩
  exact ⟨sInf S, ⟨htpos, htS.1.2⟩, htK.2, htS.2, hbelow⟩

private theorem pathELength_comp_le_on_interval
    {n : ℕ} {M N : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : M → N) {γ : ℝ → M} {a b C : ℝ} (hC : 0 ≤ C)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ)
    (hf : ∀ t ∈ Icc a b, MDifferentiableAt (𝓡 n) (𝓡 n) f (γ t))
    (hbound : ∀ t ∈ Icc a b, ∀ v : TangentSpace (𝓡 n) (γ t),
      h.tangentNorm (f (γ t)) (mfderiv (𝓡 n) (𝓡 n) f (γ t) v) ≤
        C * g.tangentNorm (γ t) v) :
    h.pathELength (f ∘ γ) a b ≤ ENNReal.ofReal C * g.pathELength γ a b := by
  rw [RiemannianMetric.pathELength_eq_lintegral_tangentNorm,
    RiemannianMetric.pathELength_eq_lintegral_tangentNorm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  have hchain : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (f ∘ γ) t 1 =
      mfderiv (𝓡 n) (𝓡 n) f (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) :=
    mfderiv_comp_apply t (hf t ht) (hγ.mdifferentiable (by simp) t) 1
  exact (ENNReal.ofReal_le_ofReal (by rw [hchain]; exact hbound t ht _)).trans_eq
    (ENNReal.ofReal_mul hC)

theorem source_ball_coverage_of_metricComplete_zero
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0)) :
    ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
      (S.flow (G.subsequence k)).zeroBall A ⊆
        (fun x => ((G.embedding k).toFun (0, x)).2) '' G.exhaustion j := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let : T3Space G.limitCarrier.carrier := G.limitCarrier.t3Space
  let gL := G.limitFlow.metricAt 0
  let pL := G.limitFlow.base
  intro A hA
  let K := {x | gL.edist pL x ≤ ENNReal.ofReal (4 * A)}
  let V := gL.ball pL (4 * A)
  have hK : IsCompact K := gL.isCompact_closedBall_of_metricComplete hcomplete pL (4 * A)
  have hVK : V ⊆ K := by
    intro x hx
    change gL.edist pL x < ENNReal.ofReal (4 * A) at hx
    exact hx.le
  have hV : IsOpen V := by
    let : EMetricSpace G.limitCarrier.carrier := G.limitCarrier.metricEMetricSpace gL
    have heq : V = Metric.eball pL (ENNReal.ofReal (4 * A)) := by
      ext x
      change gL.edist pL x < ENNReal.ofReal (4 * A) ↔
        gL.edist x pL < ENNReal.ofReal (4 * A)
      rw [show gL.edist pL x = gL.edist x pL from edist_comm pL x]
    rw [heq]
    exact Metric.isOpen_eball
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hK
  obtain ⟨N, hjN, hN⟩ := G.pullback_metric_converges j K {0} hK hj
    isCompact_singleton (singleton_subset_iff.mpr hT) (1 / 2) (by norm_num)
  refine ⟨j, ?_⟩
  filter_upwards [eventually_ge_atTop N] with k hk
  let Q := S.carrier (G.subsequence k)
  let : TopologicalSpace Q.carrier := Q.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) Q.carrier := Q.chartedSpace
  let : IsManifold (𝓡 n) ∞ Q.carrier := Q.isManifold
  let : T2Space Q.carrier := Q.t2Space
  let gS := (S.flow (G.subsequence k)).metricAt 0
  let pS := (S.flow (G.subsequence k)).base
  let f := fun x => ((G.embedding k).toFun (0, x)).2
  let inv := fun y => ((G.embedding k).inverse (0, y)).2
  have hKk : K ⊆ G.exhaustion k := hj.trans (G.exhaustion_monotone (hjN.trans hk))
  have hleft (x : G.limitCarrier.carrier) (hx : x ∈ K) : inv (f x) = x :=
    (G.embedding k).spatialInverse_comp_spatialMap hT (hKk hx)
  have hnorm (x : G.limitCarrier.carrier) (hx : x ∈ K)
      (v : TangentSpace (𝓡 n) x) :
      gL.tangentNorm x v ≤ 2 * gS.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) := by
    apply (gL.tangentNorm_pullback_bounds_of_unit_error gS f (by norm_num : (1 : ℝ) < 2)
      (fun u hu => ?_) v).2
    convert (hN k hk 0 (mem_singleton 0) x hx u u hu hu).le using 1 <;>
      first | rfl | norm_num
  have hinvsmooth : ∀ y ∈ f '' K, ContMDiffAt (𝓡 n) (𝓡 n) 1 inv y := by
    rintro _ ⟨x, hx, rfl⟩
    exact ((G.embedding k).spatialInverse_contMDiffAt (G.exhaustion_open k) hT
      (hKk hx)).of_le (by simp)
  have hinvbound : ∀ y ∈ f '' K, ∀ v : TangentSpace (𝓡 n) y,
      gL.tangentNorm (inv y) (mfderiv (𝓡 n) (𝓡 n) inv y v) ≤ 2 * gS.tangentNorm y v := by
    rintro _ ⟨x, hx, rfl⟩ v
    obtain ⟨w, hw⟩ := ((G.embedding k).spatialMap_mfderiv_bijective
      (G.exhaustion_open k) hT (hKk hx)).2 v
    rw [← hw, (G.embedding k).spatialInverse_mfderiv_comp (G.exhaustion_open k) hT (hKk hx)]
    rw [hleft x hx]
    exact hnorm x hx w
  have hopen : IsOpen (f '' V) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨x, hx, rfl⟩
    rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective
      ((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hT (hKk (hVK hx)))
      ((G.embedding k).spatialMap_mfderiv_bijective (G.exhaustion_open k) hT (hKk (hVK hx)))]
    exact image_mem_map (hV.mem_nhds hx)
  have hclosed : IsClosed (f '' K) :=
    (hK.image_of_continuousOn (fun x hx =>
      ((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hT
        (hKk hx)).continuousAt.continuousWithinAt)).isClosed
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : G.limitCarrier.carrier → Type _) :=
    ⟨gL.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : Q.carrier → Type _) :=
    ⟨gS.toRiemannianMetric⟩
  have hpV : pL ∈ V := by
    change Manifold.riemannianEDist (𝓡 n) pL pL < ENNReal.ofReal (4 * A)
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hfp : f pL = pS := congrArg Prod.snd (G.base_preserving k)
  have hip : inv pS = pL := by rw [← hfp, hleft pL (hVK hpV)]
  intro y hy
  suffices hyV : y ∈ f '' V by
    exact image_mono (hVK.trans hj) hyV
  by_contra hyV
  obtain ⟨γ, hγ0, hγ1, hγ, hlength, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hy
      (zero_lt_one : (0 : ℝ) < 1)
  change γ 0 = pS at hγ0
  obtain ⟨t, ht, htK, htV, hbelow⟩ := exists_first_exit_of_closed_superset
    hopen hclosed (image_mono hVK) hγ.continuous.continuousOn
    (by rw [hγ0, ← hfp]; exact mem_image_of_mem f hpV) (by rwa [hγ1])
  have hpath : ∀ s ∈ Icc (0 : ℝ) t, γ s ∈ f '' K := by
    intro s hs
    rcases hs.2.eq_or_lt with hst | hst
    · simpa only [hst] using htK
    · exact image_mono hVK (hbelow s ⟨hs.1, hst⟩)
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 (inv ∘ γ) (Icc 0 t) := by
    intro s hs
    exact ((hinvsmooth _ (hpath s hs)).comp s hγ.contMDiffAt).contMDiffWithinAt
  have hlen := pathELength_comp_le_on_interval gS gL inv (by norm_num : (0 : ℝ) ≤ 2) hγ
    (fun s hs => (hinvsmooth _ (hpath s hs)).mdifferentiableAt (by simp))
    (fun s hs => hinvbound _ (hpath s hs))
  have hdist : gL.edist pL (inv (γ t)) ≤ ENNReal.ofReal 2 * gS.pathELength γ 0 1 := by
    have hd := Manifold.riemannianEDist_le_pathELength hsmooth
      (show (inv ∘ γ) 0 = pL by simp only [Function.comp_apply, hγ0, hip]) rfl ht.1.le
    exact hd.trans (hlen.trans (mul_le_mul_right (Manifold.pathELength_mono le_rfl ht.2) _))
  have hsmall : inv (γ t) ∈ V := by
    apply hdist.trans_lt
    calc
      ENNReal.ofReal 2 * gS.pathELength γ 0 1 < ENNReal.ofReal 2 * ENNReal.ofReal A :=
        (ENNReal.mul_lt_mul_right (by norm_num) ENNReal.ofReal_ne_top) hlength
      _ ≤ ENNReal.ofReal (4 * A) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
  apply htV
  obtain ⟨x, hx, heq⟩ := htK
  rw [← heq, hleft x hx] at hsmall
  exact ⟨x, hsmall, heq⟩

theorem exists_isometric_line_of_opposite_segments_of_metricComplete_zero
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (minus plus : ∀ k, ℝ → (S.carrier (G.subsequence k)).carrier)
    (hminus0 : ∀ k, minus k 0 = (S.flow (G.subsequence k)).base)
    (hplus0 : ∀ k, plus k 0 = (S.flow (G.subsequence k)).base)
    {a b : ℕ → ℝ} (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop) :
    letI : ∀ k, MetricSpace (S.carrier (G.subsequence k)).carrier :=
      fun k => (S.carrier (G.subsequence k)).metricSpaceOf
        ((S.flow (G.subsequence k)).metricAt 0)
    (∀ k, ∀ s ∈ Icc (0 : ℝ) (a k), ∀ t ∈ Icc (0 : ℝ) (a k),
      dist (minus k s) (minus k t) = |s - t|) →
    (∀ k, ∀ s ∈ Icc (0 : ℝ) (b k), ∀ t ∈ Icc (0 : ℝ) (b k),
      dist (plus k s) (plus k t) = |s - t|) →
    Tendsto (fun k => Poincare.AncientVolume.Splitting.segmentComparisonCosine
      (minus k) (plus k) (a k) (b k)) atTop (𝓝 (-1)) →
    (∀ k, ∀ s ∈ Icc (0 : ℝ) (a k), ∀ t ∈ Icc (0 : ℝ) (b k),
      s ^ 2 + t ^ 2 - 2 * s * t *
        Poincare.AncientVolume.Splitting.segmentComparisonCosine
          (minus k) (plus k) (a k) (b k) ≤ dist (minus k s) (plus k t) ^ 2) →
    letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metricAt 0)
    ∃ gamma : ℝ → G.limitCarrier.carrier,
      Isometry gamma ∧ gamma 0 = G.limitFlow.base :=
  G.exists_isometric_line_of_opposite_segments hT
    (G.source_ball_coverage_of_metricComplete_zero hT hcomplete)
    minus plus hminus0 hplus0 ha hb

end PoincareConjecture.PointedGeometricConvergence
