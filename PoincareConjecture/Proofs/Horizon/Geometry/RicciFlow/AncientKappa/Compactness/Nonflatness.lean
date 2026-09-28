import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Statement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Nonflatness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RicciFlow

variable {M : Type} [TopologicalSpace M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem exists_ancient_curvatureDerivativeNorm_bound_of_m23_predecessors
    (P : M23NormalizedKappaCompactnessPredecessors) (F : RicciFlow 3 M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ≤ 0, ∀ x : M,
      (F.connection t).curvatureDerivativeNorm m x ≤ C := by
  have hKp : 0 < K + 1 := by linarith
  obtain ⟨C, hC, hShi⟩ := P.local_derivative_estimates m (K + 1) (K + 1) 1
    hKp hKp (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro t ht x
  have hshift : (fun s : ℝ => s + (t - 1)) '' Icc 0 1 ⊆ Iic 0 := by
    rintro _ ⟨s, hs, rfl⟩
    change s + (t - 1) ≤ 0
    linarith [hs.2]
  have hne : (Icc (0 : ℝ) 1).Nontrivial :=
    ⟨0, by norm_num, 1, by norm_num, by norm_num⟩
  let G := F.translate (t - 1) hshift ordConnected_Icc hne
  have hcompact : IsCompact (closure ((G.metric 0).ball x 1)) := by
    change IsCompact (closure ((F.metric (0 + (t - 1))).ball x 1))
    exact (F.metric _).isCompact_closure_ball_of_metricComplete
      (hcomplete _ (by linarith)) x 1
  have hcurv : ∀ s ∈ Icc 0 1, ∀ y ∈ (G.metric 0).ball x 1,
      (G.connection s).curvatureTensorNorm y ≤ K + 1 := by
    intro s hs y _
    exact (hbound (s + (t - 1)) (by linarith [hs.2]) y).trans (by linarith)
  have hx : x ∈ (G.metric 0).ball x (1 / 2) := by
    change (G.metric 0).edist x x < ENNReal.ofReal (1 / 2)
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
    positivity
  have h := hShi M 1 (by norm_num) (by rw [div_self hKp.ne'])
    G x hcompact hcurv 1 (by norm_num) x hx
  change (F.connection (1 + (t - 1))).curvatureDerivativeNorm m x ≤
    C / (1 : ℝ) ^ ((m : ℝ) / 2) at h
  rwa [show 1 + (t - 1) = t by ring, Real.one_rpow, div_one] at h

private theorem scalarCurvature_nonpos_of_bounded_smoothExhaustion_m23
    (P : M23NormalizedKappaCompactnessPredecessors)
    {T : ℝ} (F : RicciFlow 3 M (Icc 0 T))
    {O : M} (S : SmoothExhaustion F O) (hT : 0 ≤ T)
    (hcomplete : MetricComplete (F.metric 0))
    (hRic : ∀ t ∈ Icc 0 T, ∀ x (v : TangentSpace (𝓡 3) x),
      0 ≤ (F.connection t).ricci x v v)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc 0 T, ∀ x, (F.connection t).scalarCurvature x ≤ B)
    (hinit : ∀ x, (F.connection 0).scalarCurvature x ≤ 0) :
    ∀ x t, t ∈ Icc 0 T → (F.connection t).scalarCurvature x ≤ 0 := by
  apply S.nonpos_of_heat_le_mul_of_metricComplete (show 0 ∈ Icc 0 T from ⟨le_rfl, hT⟩)
    hcomplete (u := fun x t => (F.connection t).scalarCurvature x)
    (du := fun x t => (F.connection t).laplacian (F.connection t).scalarCurvature x +
      2 * (F.connection t).ricciNormSq x) (C := 2 * B) (B := B)
    (by positivity) Subset.rfl
  · have hreg : ContinuousOn (fun z : ℝ × M => (F.connection z.1).scalarCurvature z.2)
        (Icc 0 T ×ˢ univ) := (P.scalar_regular M (Icc 0 T) F).continuousOn
    exact hreg.comp (f := fun z : M × ℝ => (z.2, z.1))
      (continuous_snd.prodMk continuous_fst).continuousOn (fun z hz => ⟨hz.2, hz.1⟩)
  · intro t ht
    have hs : ContMDiff (𝓡 3) ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ∞ (fun x : M => (t, x)) :=
      (contMDiff_const (I := 𝓡 3) (I' := 𝓘(ℝ, ℝ)) (c := t)).prodMk
        (contMDiff_id (I := 𝓡 3))
    simpa only [Function.comp_def] using
      (P.scalar_regular M (Icc 0 T) F).comp_contMDiff (f := fun x : M => (t, x))
        hs (fun x => ⟨ht, mem_univ x⟩)
  · intro x t ht
    exact P.scalar_evolution M (Icc 0 T) F t ⟨ht.1.le, ht.2⟩ x
  · intro x t ht
    exact hbound t ht x
  · intro x t ht
    have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    have hricci := (F.connection t).ricciNormSq_le_scalarCurvature_sq_of_ricci_nonneg
      (P.tensor_calculus 3 M (F.metric t) (F.connection t)) x (hRic t ht' x)
    have hnonneg : 0 ≤ (F.connection t).scalarCurvature x :=
      Finset.sum_nonneg (fun i _ => hRic t ht' x _)
    have hreaction := mul_le_mul_of_nonneg_right (hbound t ht' x) hnonneg
    nlinarith
  · exact hinit

private theorem scalarCurvature_nonpos_of_bounded_compact_m23
    [CompactSpace M] (P : M23NormalizedKappaCompactnessPredecessors)
    {T : ℝ} (F : RicciFlow 3 M (Icc 0 T))
    (hRic : ∀ t ∈ Icc 0 T, ∀ x (v : TangentSpace (𝓡 3) x),
      0 ≤ (F.connection t).ricci x v v)
    {B : ℝ} (hbound : ∀ t ∈ Icc 0 T, ∀ x, (F.connection t).scalarCurvature x ≤ B)
    (hinit : ∀ x, (F.connection 0).scalarCurvature x ≤ 0) :
    ∀ x t, t ∈ Icc 0 T → (F.connection t).scalarCurvature x ≤ 0 := by
  have hsmooth (t : ℝ) (ht : t ∈ Icc 0 T) :
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (F.connection t).scalarCurvature := by
    have hs : ContMDiff (𝓡 3) ((𝓘(ℝ, ℝ)).prod (𝓡 3)) ∞ (fun x : M => (t, x)) :=
      (contMDiff_const (I := 𝓡 3) (I' := 𝓘(ℝ, ℝ)) (c := t)).prodMk
        (contMDiff_id (I := 𝓡 3))
    simpa only [Function.comp_def] using
      (P.scalar_regular M (Icc 0 T) F).comp_contMDiff (f := fun x : M => (t, x))
        hs (fun x => ⟨ht, mem_univ x⟩)
  apply Poincare.Parabolic.nonpos_of_deriv_le_mul_at_max_of_nonpos_outside_compact
    (K := univ) isCompact_univ
    (F := fun x t => (F.connection t).scalarCurvature x)
    (F' := fun x t => (F.connection t).laplacian (F.connection t).scalarCurvature x +
      2 * (F.connection t).ricciNormSq x) (c := 2 * B)
  · exact (P.scalar_regular M (Icc 0 T) F).continuousOn.comp
      (f := fun z : M × ℝ => (z.2, z.1))
      (continuous_snd.prodMk continuous_fst).continuousOn (fun z hz => ⟨hz.2, hz.1⟩)
  · intro x t ht
    exact P.scalar_evolution M (Icc 0 T) F t ⟨ht.1.le, ht.2⟩ x
  · intro x t ht _ hmax
    have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    have hlap := (F.connection t).laplacian_nonpos_of_isLocalMax (hsmooth t ht')
      (Filter.Eventually.of_forall hmax)
    have hricci := (F.connection t).ricciNormSq_le_scalarCurvature_sq_of_ricci_nonneg
      (P.tensor_calculus 3 M (F.metric t) (F.connection t)) x (hRic t ht' x)
    have hnonneg : 0 ≤ (F.connection t).scalarCurvature x :=
      Finset.sum_nonneg (fun i _ => hRic t ht' x _)
    have hreaction := mul_le_mul_of_nonneg_right (hbound t ht' x) hnonneg
    nlinarith
  · exact hinit
  · intro x hx
    exact False.elim (hx (mem_univ x))



theorem scalarCurvature_terminal_nonpos_of_bounded_ancient_slice_nonpos_of_m23_predecessors
    (P : M23NormalizedKappaCompactnessPredecessors) (F : RicciFlow 3 M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {a : ℝ} (ha : a < 0)
    (hinit : ∀ x, (F.connection a).scalarCurvature x ≤ 0) :
    ∀ x, (F.connection 0).scalarCurvature x ≤ 0 := by
  classical
  by_cases hc : IsCompact (univ : Set M)
  · letI : CompactSpace M := ⟨hc⟩
    have hshift : (fun t : ℝ => t + a) '' Icc 0 (-a) ⊆ Iic 0 := by
      rintro _ ⟨t, ht, rfl⟩
      change t + a ≤ 0
      linarith [ht.2]
    have hne : (Icc 0 (-a)).Nontrivial := by
      refine ⟨0, ⟨le_rfl, by linarith⟩, -a, ⟨by linarith, le_rfl⟩, ?_⟩
      linarith
    let G := F.translate a hshift ordConnected_Icc hne
    have hresult : ∀ x t, t ∈ Icc 0 (-a) → (G.connection t).scalarCurvature x ≤ 0 := by
      refine scalarCurvature_nonpos_of_bounded_compact_m23 P G
        (B := (3 : ℝ) ^ 2 * K) ?_ ?_ ?_
      · intro t ht x v
        exact ((G.connection t).ricci_bounds_of_nonnegative_curvatureOperator
          (P.tensor_calculus 3 M (G.metric t) (G.connection t)) x
          (hoperator (t + a) (by linarith [ht.2]) x) v).1
      · intro t ht x
        exact (le_abs_self _).trans
          (((G.connection t).abs_scalarCurvature_le_curvatureTensorNorm x).trans
            (mul_le_mul_of_nonneg_left (hbound (t + a) (by linarith [ht.2]) x)
              (sq_nonneg _)))
      · intro x
        change (F.connection (0 + a)).scalarCurvature x ≤ 0
        rw [zero_add]
        exact hinit x
    intro x
    have hx := hresult x (-a) ⟨by linarith, le_rfl⟩
    change (F.connection (-a + a)).scalarCurvature x ≤ 0 at hx
    exact (congrArg (fun t => (F.connection t).scalarCurvature x ≤ 0)
      (neg_add_cancel a)).mp hx
  letI : NoncompactSpace M := ⟨hc⟩
  have hshift : (fun t : ℝ => t + a) '' Icc 0 (-a) ⊆ Iic 0 := by
    rintro _ ⟨t, ht, rfl⟩
    change t + a ≤ 0
    linarith [ht.2]
  have hne : (Icc 0 (-a)).Nontrivial := by
    refine ⟨0, ⟨le_rfl, by linarith⟩, -a, ⟨by linarith, le_rfl⟩, ?_⟩
    linarith
  let G := F.translate a hshift ordConnected_Icc hne
  have hzero : (0 : ℝ) ∈ Icc 0 (-a) := ⟨le_rfl, by linarith⟩
  have hcompleteG : MetricComplete (G.metric 0) := by
    simpa only [G, translate, zero_add] using hcomplete a ha.le
  have hcurv (t : ℝ) (ht : t ∈ Icc 0 (-a)) (x : M) :
      (G.connection t).curvatureTensorNorm x ≤ K :=
    hbound (t + a) (by linarith [ht.2]) x
  have hoperatorG (t : ℝ) (ht : t ∈ Icc 0 (-a)) (x : M) :
      (G.connection t).NonnegativeCurvatureOperator x :=
    hoperator (t + a) (by linarith [ht.2]) x
  obtain ⟨C, hCpos, hderiv⟩ :=
    F.exists_ancient_curvatureDerivativeNorm_bound_of_m23_predecessors P hcomplete hK hbound 1
  obtain ⟨B, _, hsmooth⟩ := RiemannianMetric.exists_uniform_smoothDistanceLike 3 hK
  let O : M := Classical.choice inferInstance
  obtain ⟨S, _⟩ := hsmooth (G.metric 0) (G.connection 0) hcompleteG (hcurv 0 hzero) O
  have hRicDeriv : ∀ t ∈ Icc 0 (-a), ∀ y (v w z : TangentSpace (𝓡 3) y),
      |(G.connection t).covariantTensorDerivative (G.connection t).ricciEvaluation
        y ![v, w, z]| ≤ (3 : ℝ) * C * (G.metric t).tangentNorm y v *
          (G.metric t).tangentNorm y w * (G.metric t).tangentNorm y z := by
    intro t ht y v w z
    apply ((G.connection t).abs_covariantTensorDerivative_ricci_le_curvatureDerivativeNorm
      (P.tensor_calculus 3 M (G.metric t) (G.connection t)) y v w z).trans
    have hd : (G.connection t).curvatureDerivativeNorm 1 y ≤ C :=
      hderiv (t + a) (by linarith [ht.2]) y
    have hnorm (v : TangentSpace (𝓡 3) y) : 0 ≤ (G.metric t).tangentNorm y v :=
      Real.sqrt_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num))
        (hnorm v)) (hnorm w)) (hnorm z)
  let exhaustion := G.smoothExhaustionOfInitialOfCurvatureBound O 0 hzero S K
    ((3 : ℝ) * C) (-a) hK (by positivity)
    (fun t ht => by simpa only [sub_zero, abs_of_nonneg ht.1] using ht.2)
    hcurv hRicDeriv
  have hscalar_bound (t : ℝ) (ht : t ∈ Icc 0 (-a)) (x : M) :
      (G.connection t).scalarCurvature x ≤ (3 : ℝ) ^ 2 * K :=
    (le_abs_self _).trans (((G.connection t).abs_scalarCurvature_le_curvatureTensorNorm x).trans
      (mul_le_mul_of_nonneg_left (hcurv t ht x) (sq_nonneg _)))
  have hresult : ∀ x t, t ∈ Icc 0 (-a) → (G.connection t).scalarCurvature x ≤ 0 := by
    refine scalarCurvature_nonpos_of_bounded_smoothExhaustion_m23 P G exhaustion
      (by linarith) hcompleteG ?_ (by positivity) hscalar_bound ?_
    · intro t ht x v
      exact ((G.connection t).ricci_bounds_of_nonnegative_curvatureOperator
        (P.tensor_calculus 3 M (G.metric t) (G.connection t)) x (hoperatorG t ht x) v).1
    · intro x
      exact (congrArg (fun t => (F.connection t).scalarCurvature x ≤ 0) (zero_add a)).mpr
        (hinit x)
  intro x
  have hx := hresult x (-a) ⟨by linarith, le_rfl⟩
  change (F.connection (-a + a)).scalarCurvature x ≤ 0 at hx
  exact (congrArg (fun t => (F.connection t).scalarCurvature x ≤ 0) (neg_add_cancel a)).mp hx



theorem scalarCurvature_positive_somewhere_of_bounded_ancient_of_m23_predecessors
    (P : M23NormalizedKappaCompactnessPredecessors) (F : RicciFlow 3 M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hnonflat : ∃ p : M, 0 < (F.connection 0).scalarCurvature p) :
    ∀ a ≤ 0, ∃ x : M, 0 < (F.connection a).scalarCurvature x := by
  intro a ha
  rcases lt_or_eq_of_le ha with ha | rfl
  · by_contra hn
    push Not at hn
    obtain ⟨p, hp⟩ := hnonflat
    exact hp.not_ge
      (F.scalarCurvature_terminal_nonpos_of_bounded_ancient_slice_nonpos_of_m23_predecessors
        P hcomplete hoperator hK hbound ha hn p)
  · exact hnonflat

end PoincareConjecture.RicciFlow
