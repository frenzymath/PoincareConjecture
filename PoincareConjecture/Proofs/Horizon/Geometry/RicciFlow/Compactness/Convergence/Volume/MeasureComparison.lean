import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.PathComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.HausdorffDensity.MeasureComparison











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]



private theorem edist_image_le_mul_edist_of_tangentNorm_le_on_ball
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    {f : M → N} {p : M} {r C : ℝ} (hr : 0 < r) (hC : 0 < C)
    (hf : ∀ z ∈ g.ball p (3 * r), ContMDiffAt (𝓡 n) (𝓡 n) 1 f z)
    (hbound : ∀ z ∈ g.ball p (3 * r), ∀ v : TangentSpace (𝓡 n) z,
      h.tangentNorm (f z) (mfderiv (𝓡 n) (𝓡 n) f z v) ≤
        C * g.tangentNorm z v)
    {x y : M} (hx : x ∈ g.ball p r) (hy : y ∈ g.ball p r) :
    h.edist (f x) (f y) ≤ ENNReal.ofReal C * g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hxy : g.edist x y < ENNReal.ofReal (2 * r) := by
    calc
      g.edist x y ≤ g.edist x p + g.edist p y := Manifold.riemannianEDist_triangle
      _ < ENNReal.ofReal r + ENNReal.ofReal r :=
        ENNReal.add_lt_add (by simpa [ball, edist, Manifold.riemannianEDist_comm] using hx) hy
      _ = ENNReal.ofReal (2 * r) := by rw [← ENNReal.ofReal_add hr.le hr.le]; congr 1; ring
  have hdiv : h.edist (f x) (f y) / ENNReal.ofReal C ≤ g.edist x y := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlength, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt (lt_min hb hxy) zero_lt_one
    have hγball : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ g.ball p (3 * r) := by
      intro u hu
      have hxu : g.edist x (γ u) < ENNReal.ofReal (2 * r) := by
        exact ((Manifold.riemannianEDist_le_pathELength
          hγsmooth.contMDiffOn hγ0 rfl hu.1).trans
          (Manifold.pathELength_mono le_rfl hu.2)).trans_lt
          (hγlength.trans_le (min_le_right _ _))
      calc
        g.edist p (γ u) ≤ g.edist p x + g.edist x (γ u) :=
          Manifold.riemannianEDist_triangle
        _ < ENNReal.ofReal r + ENNReal.ofReal (2 * r) := ENNReal.add_lt_add hx hxu
        _ = ENNReal.ofReal (3 * r) := by
          rw [← ENNReal.ofReal_add hr.le (by positivity : 0 ≤ 2 * r)]; congr 1; ring
    have hlength := g.pathELength_comp_le_of_tangentNorm_le_on_Icc h hC.le hγsmooth
      (fun u hu ↦ hf (γ u) (hγball u hu))
      (fun u hu ↦ hbound (γ u) (hγball u hu))
    have hdist : h.edist (f x) (f y) ≤ h.pathELength (f ∘ γ) 0 1 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
        ⟨h.toRiemannianMetric⟩
      apply Manifold.riemannianEDist_le_pathELength _ (congrArg f hγ0)
        (congrArg f hγ1) zero_le_one
      exact (show ContMDiffOn (𝓡 n) (𝓡 n) 1 f (g.ball p (3 * r)) from
        fun z hz ↦ (hf z hz).contMDiffWithinAt).comp hγsmooth.contMDiffOn hγball
    apply (ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hC))
      ENNReal.ofReal_ne_top).mpr
    calc
      h.edist (f x) (f y) ≤ ENNReal.ofReal C * g.pathELength γ 0 1 := hdist.trans hlength
      _ ≤ b * ENNReal.ofReal C := by
        rw [mul_comm b]
        exact mul_le_mul_right (hγlength.le.trans (min_le_left _ _)) _
  simpa only [mul_comm] using (ENNReal.div_le_iff
    (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) ENNReal.ofReal_ne_top).mp hdiv

variable [T3Space M]



theorem exists_open_edist_image_le_of_tangentNorm_le
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    {f : M → N} {s : Set M} {p : M} (hs : s ∈ 𝓝 p)
    (hf : ∀ z ∈ s, ContMDiffAt (𝓡 n) (𝓡 n) 1 f z)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ z ∈ s, ∀ v : TangentSpace (𝓡 n) z,
      h.tangentNorm (f z) (mfderiv (𝓡 n) (𝓡 n) f z v) ≤
        C * g.tangentNorm z v) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ⊆ s ∧
      ∀ x ∈ U, ∀ y ∈ U, h.edist (f x) (f y) ≤ ENNReal.ofReal C * g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  obtain ⟨c, hc, hcs⟩ := setOfPred_riemannianEDist_lt_subset_nhds (𝓡 n) hs
  let r : ℝ := (c : ℝ) / 3
  have hr : 0 < r := by dsimp [r]; positivity
  have h3r : ENNReal.ofReal (3 * r) = c := by
    dsimp [r]
    rw [mul_div_cancel₀ _ (by norm_num), ENNReal.ofReal_coe_nnreal]
  have hball : g.ball p (3 * r) ⊆ s := by
    simpa only [ball, edist, h3r] using hcs
  have hsmall : g.ball p r ⊆ g.ball p (3 * r) := by
    intro z hz
    exact hz.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  refine ⟨g.ball p r, ?_, ?_, hsmall.trans hball, ?_⟩
  · have hb : g.ball p r = Metric.eball p (ENNReal.ofReal r) := by
      ext z
      change Manifold.riemannianEDist (𝓡 n) p z < ENNReal.ofReal r ↔
        Manifold.riemannianEDist (𝓡 n) z p < ENNReal.ofReal r
      rw [Manifold.riemannianEDist_comm]
    rw [hb]
    exact Metric.isOpen_eball
  · change g.edist p p < ENNReal.ofReal r
    simp only [edist, Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr hr
  · intro x hx y hy
    exact g.edist_image_le_mul_edist_of_tangentNorm_le_on_ball h hr hC
      (fun z hz ↦ hf z (hball hz)) (fun z hz ↦ hbound z (hball hz)) hx hy

variable [T3Space N] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [MeasurableSpace N] [BorelSpace N]



theorem volumeMeasure_image_le_of_tangentNorm_le
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : OpenPartialHomeomorph M N) {V : Set M} (hV : IsOpen V)
    (hVe : V ⊆ e.source)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ z ∈ V, ∀ v : TangentSpace (𝓡 n) z,
      h.tangentNorm (e z) (mfderiv (𝓡 n) (𝓡 n) e z v) ≤
        C * g.tangentNorm z v)
    {s : Set M} (hs : MeasurableSet s) (hsV : s ⊆ V) :
    h.volumeMeasure (e '' s) ≤ ENNReal.ofReal C ^ n * g.volumeMeasure s := by
  let μ := (h.volumeMeasure.restrict e.target).map e.symm
  have hμ : ∀ t : Set M, MeasurableSet t → t ⊆ e.source →
      μ t = h.volumeMeasure (e '' t) := by
    intro t ht hte
    have hm : AEMeasurable e.symm (h.volumeMeasure.restrict e.target) :=
      e.symm.continuousOn.aemeasurable e.open_target.measurableSet
    have hset : e.symm ⁻¹' t ∩ e.target = e '' t := by
      ext y
      constructor
      · intro hy
        exact ⟨e.symm y, hy.1, e.right_inv hy.2⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨by simpa only [mem_preimage, e.left_inv (hte hx)], e.map_source (hte hx)⟩
    dsimp only [μ]
    rw [Measure.map_apply_of_aemeasurable hm ht,
      Measure.restrict_apply' e.open_target.measurableSet, hset]
  rw [← hμ s hs (hsV.trans hVe)]
  change μ s ≤ (ENNReal.ofReal C ^ n • g.volumeMeasure) s
  apply Poincare.HausdorffDensity.measure_le_of_locally_le hs
  intro p hp
  obtain ⟨U, hU, hpU, hUV, hdist⟩ :=
    g.exists_open_edist_image_le_of_tangentNorm_le h (hV.mem_nhds (hsV hp))
      (fun z hz ↦ he.contMDiffAt (e.open_source.mem_nhds (hVe hz))) hC hbound
  refine ⟨U, hU, hpU, fun t ht hts ↦ ?_⟩
  rw [hμ t ht ((hts.trans inter_subset_left).trans (hUV.trans hVe))]
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨⟨h.inner, h.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 n) N
  let K : ℝ≥0 := ⟨C, hC.le⟩
  have hK : (K : ℝ≥0∞) = ENNReal.ofReal C := ENNReal.coe_nnreal_eq K
  have hLip : LipschitzOnWith K e t := by
    intro x hx y hy
    change h.edist (e x) (e y) ≤ (K : ℝ≥0∞) * g.edist x y
    rw [hK]
    exact hdist x (hts hx).1 y (hts hy).1
  change Measure.euclideanHausdorffMeasure n (e '' t) ≤
    (ENNReal.ofReal C ^ n • Measure.euclideanHausdorffMeasure n) t
  simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    hK] using
    Poincare.HausdorffDensity.euclideanHausdorffMeasure_image_le hLip n

end PoincareConjecture.RiemannianMetric
