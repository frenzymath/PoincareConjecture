import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.TensorCone
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.CurvatureTensor
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.ThreeDimensional











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientKappaRoundness


theorem tendsto_three_eigenvalues_of_round_contractions
    {α : Type*} {l : Filter α} {f g h : α → ℝ} {r : ℝ}
    (htrace : Tendsto (fun i => f i + g i + h i) l (𝓝 (3 * r)))
    (henergy : Tendsto (fun i => f i ^ 2 + g i ^ 2 + h i ^ 2) l (𝓝 (3 * r ^ 2))) :
    Tendsto f l (𝓝 r) ∧ Tendsto g l (𝓝 r) ∧ Tendsto h l (𝓝 r) := by
  let d (i : α) := (f i - r) ^ 2 + (g i - r) ^ 2 + (h i - r) ^ 2
  have hd : Tendsto d l (𝓝 0) := by
    have ht := (henergy.sub (htrace.const_mul (2 * r))).add_const (3 * r ^ 2)
    convert ht using 1
    · funext i
      dsimp only [d]
      ring
    · congr 1
      ring
  have hcomponent (u : α → ℝ) (hu : ∀ i, (u i - r) ^ 2 ≤ d i) :
      Tendsto u l (𝓝 r) := by
    have hs : Tendsto (fun i => (u i - r) ^ 2) l (𝓝 0) :=
      squeeze_zero (fun i => sq_nonneg _) hu hd
    have habs := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.dist_eq] using habs
  refine ⟨hcomponent f ?_, hcomponent g ?_, hcomponent h ?_⟩
  · intro i
    dsimp only [d]
    nlinarith [sq_nonneg (g i - r), sq_nonneg (h i - r)]
  · intro i
    dsimp only [d]
    nlinarith [sq_nonneg (f i - r), sq_nonneg (h i - r)]
  · intro i
    dsimp only [d]
    nlinarith [sq_nonneg (f i - r), sq_nonneg (g i - r)]



theorem exists_round_pinching_spectrum
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) :
    ∃ l m n : ℝ,
      D.scalarCurvature x = 2 * (l + m + n) ∧
      D.curvatureTensorNorm x ^ 2 = 4 * (l ^ 2 + m ^ 2 + n ^ 2) ∧
      (letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      ∀ c : ℝ, 0 ≤ c →
        (D.ricciComplementTensor hD x ∈ tensorPinchingCone c ↔ 0 ≤ n ∧ l ≤ c * n)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨b, hsym, hmetric, hunit, hpair, k, e, horder, heigen, hleast, hscalar, hnorm⟩ :=
    D.three_dimensional_curvature_operator_spectrum hD x
  refine ⟨k 0, k 1, k 2, hscalar, hnorm, fun c hc => ?_⟩
  rw [D.ricciComplementTensor_eq_transport_operatorTensor hD x b,
    tensorPinchingCone_transport_iff, operatorTensor_mem_tensorPinchingCone]
  exact mem_pinchingCone_iff_diagonal hsym e heigen horder hc



theorem eventually_ricciComplement_mem_of_round_contractions
    {α : Type*} {l : Filter α}
    {M : α → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, T2Space (M i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M i)]
    [∀ i, IsManifold (𝓡 3) ∞ (M i)]
    {g : ∀ i, RiemannianMetric 3 (M i)} (D : ∀ i, LeviCivitaData (g i))
    (hD : ∀ i, (D i).CurvatureTensorCalculus) (x : ∀ i, M i)
    {r : ℝ} (hr : 0 < r)
    (hscalar : Tendsto (fun i => (D i).scalarCurvature (x i)) l (𝓝 (6 * r)))
    (hnorm : Tendsto (fun i => (D i).curvatureTensorNorm (x i) ^ 2) l (𝓝 (12 * r ^ 2)))
    {c : ℝ} (hc : 1 < c) :
    ∀ᶠ i in l,
      letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M i → Type _) :=
        ⟨(g i).toRiemannianMetric⟩
      (D i).ricciComplementTensor (hD i) (x i) ∈ tensorPinchingCone c := by
  choose f g' h htrace henergy hcone using
    fun i => exists_round_pinching_spectrum (D i) (hD i) (x i)
  have ht : Tendsto (fun i => f i + g' i + h i) l (𝓝 (3 * r)) := by
    have hh := hscalar.div_const 2
    simpa only [htrace, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      show 6 * r / 2 = 3 * r by ring] using hh
  have he : Tendsto (fun i => f i ^ 2 + g' i ^ 2 + h i ^ 2) l (𝓝 (3 * r ^ 2)) := by
    have hh := hnorm.div_const 4
    simpa only [henergy, mul_div_cancel_left₀ _ (by norm_num : (4 : ℝ) ≠ 0),
      show 12 * r ^ 2 / 4 = 3 * r ^ 2 by ring] using hh
  obtain ⟨hf, _, hh⟩ := tendsto_three_eigenvalues_of_round_contractions ht he
  have hpos := (tendsto_const_nhds (x := (0 : ℝ))).eventually_lt hh hr
  have hratio := hf.eventually_lt (hh.const_mul c) (by nlinarith : r < c * r)
  filter_upwards [hpos, hratio] with i hi hi'
  exact (hcone i c (by linarith)).mpr ⟨hi.le, hi'.le⟩

end PoincareConjecture.AncientKappaRoundness
