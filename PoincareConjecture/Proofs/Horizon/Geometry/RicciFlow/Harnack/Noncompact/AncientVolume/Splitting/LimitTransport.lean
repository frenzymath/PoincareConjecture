import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.SourceBallCoverage
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Embedding.LocalDiffeomorphism
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.SourceMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]

theorem pathELength_comp_le_of_tangentNorm_le
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : M → N) {γ : ℝ → M} {C : ℝ} (hC : 0 ≤ C)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, MDifferentiableAt (𝓡 n) (𝓡 n) f (γ t))
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 n) (γ t),
      h.tangentNorm (f (γ t)) (mfderiv (𝓡 n) (𝓡 n) f (γ t) v) ≤
        C * g.tangentNorm (γ t) v) :
    h.pathELength (f ∘ γ) 0 1 ≤ ENNReal.ofReal C * g.pathELength γ 0 1 := by
  rw [pathELength_eq_lintegral_tangentNorm, pathELength_eq_lintegral_tangentNorm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  have hchain' : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (f ∘ γ) t 1 =
      mfderiv (𝓡 n) (𝓡 n) f (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) := by
    exact mfderiv_comp_apply t (hf t ht) (hγ.mdifferentiable (by simp) t) 1
  exact (ENNReal.ofReal_le_ofReal (by rw [hchain']; exact hbound t ht _)).trans_eq
    (ENNReal.ofReal_mul hC)

theorem edist_image_le_mul_edist_of_tangentNorm_le_on_ball
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : M → N) (p : M) {r C : ℝ} (hr : 0 < r) (hC : 0 < C)
    (hf : ∀ z ∈ g.ball p (3 * r), ContMDiffAt (𝓡 n) (𝓡 n) 1 f z)
    (hbound : ∀ z ∈ g.ball p (3 * r), ∀ v : TangentSpace (𝓡 n) z,
      h.tangentNorm (f z) (mfderiv (𝓡 n) (𝓡 n) f z v) ≤ C * g.tangentNorm z v)
    {x y : M} (hx : x ∈ g.ball p r) (hy : y ∈ g.ball p r) :
    h.edist (f x) (f y) ≤ ENNReal.ofReal C * g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hxy : g.edist x y < ENNReal.ofReal (2 * r) := by
    calc
      g.edist x y ≤ g.edist x p + g.edist p y := Manifold.riemannianEDist_triangle
      _ < ENNReal.ofReal r + ENNReal.ofReal r :=
        ENNReal.add_lt_add (by simpa [ball, edist, Manifold.riemannianEDist_comm] using hx) hy
      _ = ENNReal.ofReal (2 * r) := by
        rw [← ENNReal.ofReal_add hr.le hr.le]
        congr 1
        ring
  have hdiv : h.edist (f x) (f y) / ENNReal.ofReal C ≤ g.edist x y := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    obtain ⟨γ, hγ0, hγ1, hγ, hlength, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt (lt_min hb hxy)
        (zero_lt_one : (0 : ℝ) < 1)
    have hball : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ g.ball p (3 * r) := by
      intro t ht
      have hxt : g.edist x (γ t) < ENNReal.ofReal (2 * r) := by
        exact ((Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn hγ0 rfl ht.1).trans
          (Manifold.pathELength_mono le_rfl ht.2)).trans_lt
          (hlength.trans_le (min_le_right _ _))
      calc
        g.edist p (γ t) ≤ g.edist p x + g.edist x (γ t) :=
          Manifold.riemannianEDist_triangle
        _ < ENNReal.ofReal r + ENNReal.ofReal (2 * r) := ENNReal.add_lt_add hx hxt
        _ = ENNReal.ofReal (3 * r) := by
          rw [← ENNReal.ofReal_add hr.le (by positivity : 0 ≤ 2 * r)]
          congr 1
          ring
    have hlength' := g.pathELength_comp_le_of_tangentNorm_le h f hC.le hγ
      (fun t ht => (hf _ (hball t ht)).mdifferentiableAt (by simp))
      (fun t ht => hbound _ (hball t ht))
    have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 (f ∘ γ) (Icc 0 1) := by
      intro t ht
      exact ((hf _ (hball t ht)).comp t hγ.contMDiffAt).contMDiffWithinAt
    have hdist : h.edist (f x) (f y) ≤ h.pathELength (f ∘ γ) 0 1 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
        ⟨h.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_le_pathELength hsmooth
        (congrArg f hγ0) (congrArg f hγ1) zero_le_one
    apply (ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hC))
      ENNReal.ofReal_ne_top).mpr
    calc
      h.edist (f x) (f y) ≤ ENNReal.ofReal C * g.pathELength γ 0 1 :=
        hdist.trans hlength'
      _ ≤ b * ENNReal.ofReal C := by
        rw [mul_comm b]
        exact mul_le_mul_right (hlength.le.trans (min_le_left _ _)) _
  simpa only [mul_comm] using (ENNReal.div_le_iff
    (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) ENNReal.ofReal_ne_top).mp hdiv

theorem abs_pullback_inner_sub_le_mul_of_unit_bound
    (g : RiemannianMetric n M) (h : RiemannianMetric n N) (f : M → N)
    {x : M} {δ : ℝ}
    (hclose : ∀ u : TangentSpace (𝓡 n) x, g.tangentNorm x u ≤ 1 →
      |h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x u) -
        g.inner x u u| ≤ δ) (v : TangentSpace (𝓡 n) x) :
    |h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x v) -
      g.inner x v v| ≤ δ * g.inner x v v := by
  by_cases hv : v = 0
  · subst v
    simp
  let a := g.tangentNorm x v
  have ha : 0 < a := Real.sqrt_pos.mpr (g.pos x v hv)
  have ha2 : a ^ 2 = g.inner x v v := Real.sq_sqrt (g.pos x v hv).le
  let u : TangentSpace (𝓡 n) x := a⁻¹ • v
  have hu : g.tangentNorm x u = 1 := by
    simp only [u, tangentNorm, map_smul, smul_apply, smul_eq_mul]
    rw [show a⁻¹ * (a⁻¹ * g.inner x v v) = 1 by rw [← ha2]; field_simp]
    exact Real.sqrt_one
  have hvu : a • u = v := by simp [u, smul_smul, ha.ne']
  have hc := mul_le_mul_of_nonneg_left (hclose u hu.le) (sq_nonneg a)
  have hid :
      |h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x v) -
        g.inner x v v| = a ^ 2 *
      |h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x u) -
        g.inner x u u| := by
    conv_lhs => rw [← hvu]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [show a * (a * h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
        (mfderiv (𝓡 n) (𝓡 n) f x u)) - a * (a * g.inner x u u) =
      a ^ 2 * (h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
        (mfderiv (𝓡 n) (𝓡 n) f x u) - g.inner x u u) by ring,
      abs_mul, abs_of_nonneg (sq_nonneg a)]
  rw [hid]
  simpa only [ha2, mul_comm] using hc

theorem tangentNorm_pullback_bounds_of_unit_error
    (g : RiemannianMetric n M) (h : RiemannianMetric n N) (f : M → N)
    {x : M} {C : ℝ} (hC : 1 < C)
    (hclose : ∀ u : TangentSpace (𝓡 n) x, g.tangentNorm x u ≤ 1 →
      |h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x u) -
        g.inner x u u| ≤ (C - 1) / C) (v : TangentSpace (𝓡 n) x) :
    h.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) ≤ C * g.tangentNorm x v ∧
      g.tangentNorm x v ≤ C * h.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) := by
  have hC0 : 0 < C := zero_lt_one.trans hC
  have hC2 : C ≤ C ^ 2 := by nlinarith
  let A := g.inner x v v
  let B := h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x v)
  have hA : 0 ≤ A := by
    by_cases hv : v = 0
    · simp [A, hv]
    · exact (g.pos x v hv).le
  have hB : 0 ≤ B := by
    by_cases hv : mfderiv (𝓡 n) (𝓡 n) f x v = 0
    · simp [B, hv]
    · exact (h.pos _ _ hv).le
  have herr := abs_le.mp (g.abs_pullback_inner_sub_le_mul_of_unit_bound h f hclose v)
  change -((C - 1) / C * A) ≤ B - A ∧ B - A ≤ (C - 1) / C * A at herr
  have hδ : C * ((C - 1) / C) = C - 1 := by field_simp
  have hδC : 1 + (C - 1) / C ≤ C := by
    apply (le_sub_iff_add_le').mp
    apply (div_le_iff₀ hC0).mpr
    nlinarith [sq_nonneg (C - 1)]
  have hBA : B ≤ C * A := by
    have hm := mul_le_mul_of_nonneg_right hδC hA
    nlinarith [herr.2]
  have hAB : A ≤ C * B := by
    have hm := mul_le_mul_of_nonneg_left herr.1 hC0.le
    have heq : C * ((C - 1) / C * A) = (C - 1) * A := by rw [← mul_assoc, hδ]
    nlinarith
  have hBA2 := hBA.trans (mul_le_mul_of_nonneg_right hC2 hA)
  have hAB2 := hAB.trans (mul_le_mul_of_nonneg_right hC2 hB)
  constructor
  · have hh := Real.sqrt_le_sqrt hBA2
    rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC0.le] at hh
    exact hh
  · have hh := Real.sqrt_le_sqrt hAB2
    rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC0.le] at hh
    exact hh

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.SmoothSpacetimeEmbedding

variable {n : ℕ} {T' T : ℝ} {L C : FlowCarrier n}
  {F : BasedFlow n T' T L} {G : BasedFlow n T' T C} {U : Set L.carrier}

theorem spatialInverse_comp_spatialMap
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    {s : ℝ} (hs : s ∈ Ioo T' T) {x : L.carrier} (hx : x ∈ U) :
    (e.inverse (s, (e.toFun (s, x)).2)).2 = x := by
  have hp : e.toFun (s, x) = (s, (e.toFun (s, x)).2) :=
    Prod.ext (e.time_preserving s x) rfl
  have hh := e.left_inverse (s, x) ⟨hs, hx⟩
  rw [hp] at hh
  exact congrArg Prod.snd hh

theorem spatialInverse_mfderiv_comp
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    (hU : @IsOpen L.carrier L.topologicalSpace U)
    {s : ℝ} (hs : s ∈ Ioo T' T) {x : L.carrier} (hx : x ∈ U) :
    letI : TopologicalSpace L.carrier := L.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier := L.chartedSpace
    letI : IsManifold (𝓡 n) ∞ L.carrier := L.isManifold
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    ∀ v : TangentSpace (𝓡 n) x,
      mfderiv (𝓡 n) (𝓡 n) (fun y => (e.inverse (s, y)).2) (e.toFun (s, x)).2
        (mfderiv (𝓡 n) (𝓡 n) (fun y => (e.toFun (s, y)).2) x v) = v := by
  let : TopologicalSpace L.carrier := L.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier := L.chartedSpace
  let : IsManifold (𝓡 n) ∞ L.carrier := L.isManifold
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let f := fun y => (e.toFun (s, y)).2
  let inv := fun y => (e.inverse (s, y)).2
  have heq : (inv ∘ f) =ᶠ[𝓝 x] id := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact e.spatialInverse_comp_spatialMap hs hy
  have hcomp := mfderiv_comp x
    ((e.spatialInverse_contMDiffAt hU hs hx).mdifferentiableAt (by simp))
    ((e.spatialMap_contMDiffAt hU hs hx).mdifferentiableAt (by simp))
  have hid := heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓡 n)
  rw [hcomp, mfderiv_id] at hid
  intro v
  exact congrArg (fun A => A v) hid

end PoincareConjecture.SmoothSpacetimeEmbedding

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

theorem eventually_inverse_edist_bounds_of_source_ball_coverage
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcover : ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
      (S.flow (G.subsequence k)).zeroBall A ⊆
        (fun x => ((G.embedding k).toFun (0, x)).2) '' G.exhaustion j)
    {A C : ℝ} (hA : 0 < A) (hC : 1 < C) (hC2 : C < 2) :
    ∀ᶠ k in atTop, ∀ x ∈ (S.flow (G.subsequence k)).zeroBall A,
      ∀ y ∈ (S.flow (G.subsequence k)).zeroBall A,
      let dL := G.limitCarrier.metricEMetricSpace (G.limitFlow.metricAt 0)
      let dS := (S.carrier (G.subsequence k)).metricEMetricSpace
        ((S.flow (G.subsequence k)).metricAt 0)
      let inv := fun z => ((G.embedding k).inverse (0, z)).2
      dL.edist (inv x) (inv y) ≤ ENNReal.ofReal C * dS.edist x y ∧
        dS.edist x y ≤ ENNReal.ofReal C * dL.edist (inv x) (inv y) := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  have hC0 : 0 < C := zero_lt_one.trans hC
  obtain ⟨j, hj⟩ := hcover (3 * A) (by positivity)
  let K := closure (G.exhaustion j) ∪ closure (G.limitFlow.zeroBall (6 * A))
  have hK : IsCompact K := (G.exhaustion_compactClosure j).union
    (G.isCompact_closure_zeroBall_of_source_ball_coverage hT hcover (6 * A) (by positivity))
  obtain ⟨l, hl⟩ := G.exists_exhaustion_superset hK
  obtain ⟨N, hlN, hN⟩ := G.pullback_metric_converges l K {0} hK hl
    isCompact_singleton (singleton_subset_iff.mpr hT) ((C - 1) / C)
    (div_pos (sub_pos.mpr hC) hC0)
  filter_upwards [hj, eventually_ge_atTop N, eventually_ge_atTop j] with k hkcover hkN hkj
  let Q := S.carrier (G.subsequence k)
  let : TopologicalSpace Q.carrier := Q.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) Q.carrier := Q.chartedSpace
  let : IsManifold (𝓡 n) ∞ Q.carrier := Q.isManifold
  let gL := G.limitFlow.metricAt 0
  let gS := (S.flow (G.subsequence k)).metricAt 0
  let pL := G.limitFlow.base
  let pS := (S.flow (G.subsequence k)).base
  let f := fun z => ((G.embedding k).toFun (0, z)).2
  let inv := fun z => ((G.embedding k).inverse (0, z)).2
  have hKstage : K ⊆ G.exhaustion k := hl.trans (G.exhaustion_monotone (hlN.trans hkN))
  have hleft (z : G.limitCarrier.carrier) (hz : z ∈ G.exhaustion k) : inv (f z) = z :=
    (G.embedding k).spatialInverse_comp_spatialMap hT hz
  have hnorm (z : G.limitCarrier.carrier) (hz : z ∈ K)
      (v : TangentSpace (𝓡 n) z) :
      gS.tangentNorm (f z) (mfderiv (𝓡 n) (𝓡 n) f z v) ≤ C * gL.tangentNorm z v ∧
        gL.tangentNorm z v ≤ C * gS.tangentNorm (f z) (mfderiv (𝓡 n) (𝓡 n) f z v) := by
    apply gL.tangentNorm_pullback_bounds_of_unit_error gS f hC
    intro u hu
    exact (hN k hkN 0 (mem_singleton 0) z hz u u hu hu).le
  have hinvsmooth : ∀ z ∈ gS.ball pS (3 * A),
      ContMDiffAt (𝓡 n) (𝓡 n) 1 inv z := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hkcover hz
    exact ((G.embedding k).spatialInverse_contMDiffAt (G.exhaustion_open k) hT
      (G.exhaustion_monotone hkj hw)).of_le (by simp)
  have hinvbound : ∀ z ∈ gS.ball pS (3 * A), ∀ v : TangentSpace (𝓡 n) z,
      gL.tangentNorm (inv z) (mfderiv (𝓡 n) (𝓡 n) inv z v) ≤ C * gS.tangentNorm z v := by
    intro z hz v
    obtain ⟨w, hw, heq⟩ := hkcover hz
    have hwk := G.exhaustion_monotone hkj hw
    subst z
    obtain ⟨v', hv'⟩ := ((G.embedding k).spatialMap_mfderiv_bijective
      (G.exhaustion_open k) hT hwk).2 v
    rw [← hv', (G.embedding k).spatialInverse_mfderiv_comp (G.exhaustion_open k) hT hwk]
    change gL.tangentNorm (inv (f w)) v' ≤ _
    rw [hleft w hwk]
    exact (hnorm w (Or.inl (subset_closure hw)) v').2
  have hback {x y : Q.carrier} (hx : x ∈ gS.ball pS A) (hy : y ∈ gS.ball pS A) :
      gL.edist (inv x) (inv y) ≤ ENNReal.ofReal C * gS.edist x y :=
    gS.edist_image_le_mul_edist_of_tangentNorm_le_on_ball gL inv pS hA hC0
      hinvsmooth hinvbound hx hy
  have hfp : f pL = pS := congrArg Prod.snd (G.base_preserving k)
  have hip : inv pS = pL := by rw [← hfp, hleft pL (G.base_in_exhaustion k)]
  have hpS : pS ∈ gS.ball pS A := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : Q.carrier → Type _) :=
      ⟨gS.toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 n) pS pS < ENNReal.ofReal A
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr hA
  have hinvball {x : Q.carrier} (hx : x ∈ gS.ball pS A) :
      inv x ∈ gL.ball pL (2 * A) := by
    have hh := hback hpS hx
    rw [hip] at hh
    have hm : ENNReal.ofReal C * gS.edist pS x <
        ENNReal.ofReal C * ENNReal.ofReal A :=
      (ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hC0))
        ENNReal.ofReal_ne_top) hx
    have hCA : ENNReal.ofReal C * ENNReal.ofReal A < ENNReal.ofReal (2 * A) := by
      rw [← ENNReal.ofReal_mul hC0.le]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2 * A)).mpr
        (mul_lt_mul_of_pos_right hC2 hA)
    exact hh.trans_lt (hm.trans hCA)
  have hforward {x y : G.limitCarrier.carrier}
      (hx : x ∈ gL.ball pL (2 * A)) (hy : y ∈ gL.ball pL (2 * A)) :
      gS.edist (f x) (f y) ≤ ENNReal.ofReal C * gL.edist x y := by
    apply gL.edist_image_le_mul_edist_of_tangentNorm_le_on_ball gS f pL
      (by positivity : 0 < 2 * A) hC0 _ _ hx hy
    · intro z hz
      have hzK : z ∈ K := Or.inr (subset_closure (by
        change z ∈ gL.ball pL (6 * A)
        simpa only [show 3 * (2 * A) = 6 * A by ring] using hz))
      exact ((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hT
        (hKstage hzK)).of_le (by simp)
    · intro z hz v
      have hzK : z ∈ K := Or.inr (subset_closure (by
        change z ∈ gL.ball pL (6 * A)
        simpa only [show 3 * (2 * A) = 6 * A by ring] using hz))
      exact (hnorm z hzK v).1
  have hright {x : Q.carrier} (hx : x ∈ gS.ball pS A) : f (inv x) = x := by
    have hx3 : x ∈ gS.ball pS (3 * A) :=
      hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
    obtain ⟨z, hz, rfl⟩ := hkcover hx3
    rw [hleft z (G.exhaustion_monotone hkj hz)]
  intro x hx y hy
  change gL.edist (inv x) (inv y) ≤ ENNReal.ofReal C * gS.edist x y ∧
    gS.edist x y ≤ ENNReal.ofReal C * gL.edist (inv x) (inv y)
  refine ⟨hback hx hy, ?_⟩
  have hh := hforward (hinvball hx) (hinvball hy)
  rwa [hright hx, hright hy] at hh

theorem eventually_inverse_distortion_lt_of_source_ball_coverage
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcover : ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
      (S.flow (G.subsequence k)).zeroBall A ⊆
        (fun x => ((G.embedding k).toFun (0, x)).2) '' G.exhaustion j)
    {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ (S.flow (G.subsequence k)).zeroBall A,
      ∀ y ∈ (S.flow (G.subsequence k)).zeroBall A,
      let dL := G.limitCarrier.metricEMetricSpace (G.limitFlow.metricAt 0)
      let dS := (S.carrier (G.subsequence k)).metricEMetricSpace
        ((S.flow (G.subsequence k)).metricAt 0)
      let inv := fun z => ((G.embedding k).inverse (0, z)).2
      |(dL.edist (inv x) (inv y)).toReal - (dS.edist x y).toReal| < ε := by
  let C := 1 + min (1 / 2) (ε / (4 * A))
  have hC : 1 < C := by
    have hh : 0 < min (1 / 2) (ε / (4 * A)) := lt_min (by norm_num) (by positivity)
    dsimp [C]
    linarith
  have hC2 : C < 2 := by
    have hh := min_le_left (1 / 2 : ℝ) (ε / (4 * A))
    dsimp [C]
    linarith
  have herror : (C - 1) * (2 * A) < ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * A)).mp
      (min_le_right (1 / 2 : ℝ) (ε / (4 * A)))
    dsimp [C]
    nlinarith
  filter_upwards [G.eventually_inverse_edist_bounds_of_source_ball_coverage hT hcover hA hC hC2]
    with k hk
  intro x hx y hy
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let : T3Space G.limitCarrier.carrier := G.limitCarrier.t3Space
  let : PreconnectedSpace G.limitCarrier.carrier := ⟨G.limitCarrier.connected.isPreconnected⟩
  let Q := S.carrier (G.subsequence k)
  let : TopologicalSpace Q.carrier := Q.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) Q.carrier := Q.chartedSpace
  let : IsManifold (𝓡 n) ∞ Q.carrier := Q.isManifold
  let : T3Space Q.carrier := Q.t3Space
  let : PreconnectedSpace Q.carrier := ⟨Q.connected.isPreconnected⟩
  let gL := G.limitFlow.metricAt 0
  let gS := (S.flow (G.subsequence k)).metricAt 0
  let inv := fun z => ((G.embedding k).inverse (0, z)).2
  let pS := (S.flow (G.subsequence k)).base
  have hneL := gL.edist_ne_top (inv x) (inv y)
  have hneS := gS.edist_ne_top x y
  have hh := hk x hx y hy
  change gL.edist (inv x) (inv y) ≤ ENNReal.ofReal C * gS.edist x y ∧
    gS.edist x y ≤ ENNReal.ofReal C * gL.edist (inv x) (inv y) at hh
  have hLS := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hneS) hh.1
  have hSL := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hneL) hh.2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (zero_le_one.trans hC.le)] at hLS hSL
  have hsource : (gS.edist x y).toReal < 2 * A := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : Q.carrier → Type _) :=
      ⟨gS.toRiemannianMetric⟩
    apply (ENNReal.lt_ofReal_iff_toReal_lt hneS).mp
    calc
      gS.edist x y ≤ gS.edist x pS + gS.edist pS y := Manifold.riemannianEDist_triangle
      _ < ENNReal.ofReal A + ENNReal.ofReal A :=
        ENNReal.add_lt_add (by
          have hx' : gS.edist pS x < ENNReal.ofReal A := hx
          simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hx') hy
      _ = ENNReal.ofReal (2 * A) := by
        rw [← ENNReal.ofReal_add hA.le hA.le]
        congr 1
        ring
  change |(gL.edist (inv x) (inv y)).toReal - (gS.edist x y).toReal| < ε
  have hprod := mul_le_mul_of_nonneg_left hsource.le (sub_pos.mpr hC).le
  apply abs_lt.mpr
  constructor
  · by_cases hab : (gL.edist (inv x) (inv y)).toReal ≤ (gS.edist x y).toReal
    · have ha := mul_le_mul_of_nonneg_left hab (sub_pos.mpr hC).le
      nlinarith
    · linarith
  · nlinarith

theorem tendsto_inverse_dist_of_source_ball_coverage
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcover : ∀ A : ℝ, 0 < A → ∃ j : ℕ, ∀ᶠ k in atTop,
      (S.flow (G.subsequence k)).zeroBall A ⊆
        (fun x => ((G.embedding k).toFun (0, x)).2) '' G.exhaustion j)
    (x y : ∀ k, (S.carrier (G.subsequence k)).carrier)
    {A D : ℝ} (hA : 0 < A)
    (hx : ∀ᶠ k in atTop, x k ∈ (S.flow (G.subsequence k)).zeroBall A)
    (hy : ∀ᶠ k in atTop, y k ∈ (S.flow (G.subsequence k)).zeroBall A)
    (hd : Tendsto (fun k =>
      (((S.carrier (G.subsequence k)).metricEMetricSpace
        ((S.flow (G.subsequence k)).metricAt 0)).edist (x k) (y k)).toReal)
      atTop (𝓝 D)) :
    Tendsto (fun k =>
      ((G.limitCarrier.metricEMetricSpace (G.limitFlow.metricAt 0)).edist
        ((G.embedding k).inverse (0, x k)).2
        ((G.embedding k).inverse (0, y k)).2).toReal) atTop (𝓝 D) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsource := (Metric.tendsto_nhds.mp hd) (ε / 2) (by positivity)
  filter_upwards [hx, hy, hsource,
    G.eventually_inverse_distortion_lt_of_source_ball_coverage hT hcover hA
      (show 0 < ε / 2 by positivity)] with k hkx hky hkd hki
  have herr := hki (x k) hkx (y k) hky
  rw [Real.dist_eq] at hkd ⊢
  have htriangle := abs_sub_le
    (((G.limitCarrier.metricEMetricSpace (G.limitFlow.metricAt 0)).edist
      ((G.embedding k).inverse (0, x k)).2
      ((G.embedding k).inverse (0, y k)).2).toReal)
    ((((S.carrier (G.subsequence k)).metricEMetricSpace
      ((S.flow (G.subsequence k)).metricAt 0)).edist (x k) (y k)).toReal) D
  linarith

end PoincareConjecture.PointedGeometricConvergence
