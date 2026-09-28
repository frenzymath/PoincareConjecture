import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Embedding.MetricComparison
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Embedding.SpatialRegularity

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

theorem exhaustion_monotone (G : PointedGeometricConvergence S) :
    Monotone G.exhaustion :=
  monotone_nat_of_le_succ G.exhaustion_increasing

theorem exists_exhaustion_superset (G : PointedGeometricConvergence S)
    {K : Set G.limitCarrier.carrier}
    (hK : @IsCompact G.limitCarrier.carrier G.limitCarrier.topologicalSpace K) :
    ∃ j, K ⊆ G.exhaustion j := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  exact hK.elim_directed_cover G.exhaustion G.exhaustion_open
    (by rw [G.exhaustion_covers]; exact subset_univ _) G.exhaustion_monotone.directed_le

theorem eventually_pathELength_le (G : PointedGeometricConvergence S)
    {s : ℝ} (hs : s ∈ Ioo T' T) {γ : ℝ → G.limitCarrier.carrier}
    (hγ :
      letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
        G.limitCarrier.chartedSpace
      letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
      ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ) :
    ∀ᶠ k : ℕ in atTop,
      letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
        G.limitCarrier.chartedSpace
      letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
      let C := S.carrier (G.subsequence k)
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ((S.flow (G.subsequence k)).metricAt s).pathELength
          (fun u ↦ ((G.embedding k).toFun (s, γ u)).2) 0 1 ≤
        ENNReal.ofReal (Real.sqrt 2) * (G.limitFlow.metricAt s).pathELength γ 0 1 := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let K := γ '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image hγ.continuous
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hK
  obtain ⟨N, hjN, hN⟩ := G.pullback_metric_converges j K {s} hK hj
    isCompact_singleton (singleton_subset_iff.mpr hs) 1 zero_lt_one
  filter_upwards [eventually_ge_atTop N] with k hk
  let C := S.carrier (G.subsequence k)
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  apply (G.embedding k).pathELength_le_sqrt_two
  intro u hu
  have hγu : γ u ∈ G.exhaustion k :=
    G.exhaustion_monotone (hjN.trans hk) (hj (mem_image_of_mem γ hu))
  have he := (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hs hγu
  have hchain :
      mfderiv (𝓘(ℝ, ℝ)) (𝓡 n)
          (fun z ↦ ((G.embedding k).toFun (s, γ z)).2) u 1 =
        mfderiv (𝓡 n) (𝓡 n) (fun y ↦ ((G.embedding k).toFun (s, y)).2) (γ u)
          (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ u 1) :=
    mfderiv_comp_apply u (he.mdifferentiableAt (by simp))
      (hγ.mdifferentiable (by simp) u) (1 : ℝ)
  have hsq := G.pullback_tangentNorm_le_sqrt_two j k hs
    (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ u 1)
    (hN k hk s (mem_singleton s) (γ u) (mem_image_of_mem γ hu))
  change Real.sqrt _ ≤ Real.sqrt 2 * Real.sqrt _
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
  apply Real.sqrt_le_sqrt
  rw [hchain]
  exact hsq

theorem eventually_mem_ballAt (G : PointedGeometricConvergence S)
    (hT : T' < 0 ∧ 0 < T) {s A : ℝ} (hs : s ∈ Ioo T' T)
    {x : G.limitCarrier.carrier} (hx : x ∈ G.limitFlow.ballAt s A) :
    ∀ᶠ k : ℕ in atTop,
      ((G.embedding k).toFun (s, x)).2 ∈ (S.flow (G.subsequence k)).ballAt s (2 * A) := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : G.limitCarrier.carrier → Type _) :=
    ⟨(G.limitFlow.metricAt s).toRiemannianMetric⟩
  let : ∀ x : G.limitCarrier.carrier, ENormSMulClass ℝ (TangentSpace (𝓡 n) x) :=
    fun _ ↦ inferInstance
  change Manifold.riemannianEDist (𝓡 n) G.limitFlow.base x < ENNReal.ofReal A at hx
  obtain ⟨γ, hγ0, hγ1, hγ, hlength, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hx
      (zero_lt_one : (0 : ℝ) < 1)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (isCompact_Icc.image hγ.continuous)
  filter_upwards [G.eventually_pathELength_le hs hγ, eventually_ge_atTop j] with k hk hjk
  let C := S.carrier (G.subsequence k)
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let η : ℝ → C.carrier := fun u ↦ ((G.embedding k).toFun (s, γ u)).2
  have hη : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 η (Icc 0 1) := by
    intro u hu
    have hγu := G.exhaustion_monotone hjk (hj (mem_image_of_mem γ hu))
    exact (((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hs hγu).of_le
      (by simp) |>.comp u hγ.contMDiffAt).contMDiffWithinAt
  have hη0 : η 0 = (S.flow (G.subsequence k)).base := by
    simpa only [η, hγ0] using congrArg Prod.snd (G.base_preserving_at_time hT k hs)
  have hη1 : η 1 = ((G.embedding k).toFun (s, x)).2 := by simp only [η, hγ1]
  have hdist : ((S.flow (G.subsequence k)).metricAt s).edist
      (S.flow (G.subsequence k)).base ((G.embedding k).toFun (s, x)).2 ≤
      ((S.flow (G.subsequence k)).metricAt s).pathELength η 0 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C.carrier → Type _) :=
      ⟨((S.flow (G.subsequence k)).metricAt s).toRiemannianMetric⟩
    exact Manifold.riemannianEDist_le_pathELength hη hη0 hη1 zero_le_one
  have hsqrt : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt_le : Real.sqrt 2 ≤ 2 := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  change _ < ENNReal.ofReal (2 * A)
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt 2) * (G.limitFlow.metricAt s).pathELength γ 0 1 :=
      hdist.trans hk
    _ < ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal A :=
      (ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hsqrt))
        ENNReal.ofReal_ne_top) hlength
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal A :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hsqrt_le) le_rfl
    _ = ENNReal.ofReal (2 * A) := (ENNReal.ofReal_mul (by norm_num)).symm

end PoincareConjecture.PointedGeometricConvergence
