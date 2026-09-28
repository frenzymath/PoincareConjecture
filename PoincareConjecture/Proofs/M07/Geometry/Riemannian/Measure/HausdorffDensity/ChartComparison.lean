import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.LocalDistance

set_option autoImplicit false

open Set Filter Manifold
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem exists_open_distortion_of_tangentNorm_comparison
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (he' : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {K : ℝ≥0} (hK : 1 < K)
    (hbound : ∀ᶠ z in 𝓝 x, ∀ v : EuclideanSpace ℝ (Fin n),
      ‖A v‖ ≤ (K : ℝ) * g.tangentNorm (e z) (mfderiv (𝓡 n) (𝓡 n) e z v) ∧
      g.tangentNorm (e z) (mfderiv (𝓡 n) (𝓡 n) e z v) ≤ (K : ℝ) * ‖A v‖) :
    ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ x ∈ U ∧ U ⊆ e.source ∧
      ∀ z ∈ U, ∀ w ∈ U,
        g.edist (e z) (e w) ≤ (K : ℝ≥0∞) * EDist.edist (A z) (A w) ∧
        EDist.edist (A z) (A w) ≤ (K : ℝ≥0∞) * g.edist (e z) (e w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  have heDiff : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), he'.mdifferentiableOn (by simp)⟩
  let Φ : EuclideanSpace ℝ (Fin n) → M := e ∘ A.symm
  let Ψ : M → EuclideanSpace ℝ (Fin n) := A ∘ e.symm
  have hΦ (z : EuclideanSpace ℝ (Fin n)) (hz : A.symm z ∈ e.source) :
      ContMDiffAt (𝓡 n) (𝓡 n) 1 Φ z := by
    exact ((he.contMDiffAt (e.open_source.mem_nhds hz)).of_le (by simp)).comp z
      A.symm.contDiff.contMDiff.contMDiffAt
  have hΨ (q : M) (hq : q ∈ e.target) : ContMDiffAt (𝓡 n) (𝓡 n) 1 Ψ q := by
    exact A.contDiff.contMDiff.contMDiffAt.comp q
      ((he'.contMDiffAt (e.open_target.mem_nhds hq)).of_le (by simp))
  have hdΦ (z : EuclideanSpace ℝ (Fin n)) (hz : A.symm z ∈ e.source) :
      mfderiv (𝓡 n) (𝓡 n) Φ z =
        (mfderiv (𝓡 n) (𝓡 n) e (A.symm z)) ∘L A.symm.toContinuousLinearMap := by
    rw [show Φ = e ∘ A.symm from rfl,
      mfderiv_comp z (heDiff.mdifferentiableAt hz) A.symm.differentiableAt.mdifferentiableAt,
      mfderiv_eq_fderiv, A.symm.fderiv]
  have hdΨ (q : M) (hq : q ∈ e.target) :
      mfderiv (𝓡 n) (𝓡 n) Ψ q =
        A.toContinuousLinearMap ∘L mfderiv (𝓡 n) (𝓡 n) e.symm q := by
    rw [show Ψ = A ∘ e.symm from rfl,
      mfderiv_comp q A.differentiableAt.mdifferentiableAt (heDiff.mdifferentiableAt_symm hq),
      mfderiv_eq_fderiv, A.fderiv]
  let S : Set (EuclideanSpace ℝ (Fin n)) := e.source ∩ {z | ∀ v,
    ‖A v‖ ≤ (K : ℝ) * g.tangentNorm (e z) (mfderiv (𝓡 n) (𝓡 n) e z v) ∧
    g.tangentNorm (e z) (mfderiv (𝓡 n) (𝓡 n) e z v) ≤ (K : ℝ) * ‖A v‖}
  have hS : S ∈ 𝓝 x := inter_mem (e.open_source.mem_nhds hx) hbound
  let T : Set M := e.target ∩ e.symm ⁻¹' S
  have hT : T ∈ 𝓝 (e x) := by
    refine inter_mem (e.open_target.mem_nhds (e.map_source hx)) ?_
    apply (e.continuousAt_symm (e.map_source hx)).preimage_mem_nhds
    simpa only [e.left_inv hx] using hS
  have hΨbound (q : M) (hq : q ∈ T) :
      ‖mfderiv (𝓡 n) (𝓡 n) Ψ q‖ₑ ≤ K := by
    rw [← ofReal_norm, ENNReal.ofReal_le_coe]
    apply ContinuousLinearMap.opNorm_le_bound _ K.coe_nonneg
    intro v
    have hinv : mfderiv (𝓡 n) (𝓡 n) e (e.symm q)
        (mfderiv (𝓡 n) (𝓡 n) e.symm q v) = v := by
      have h := heDiff.comp_symm_deriv hq.1
      exact congr($h v)
    have hb := (hq.2.2 (mfderiv (𝓡 n) (𝓡 n) e.symm q v)).1
    rw [hinv, e.right_inv hq.1] at hb
    rw [hdΨ q hq.1]
    change ‖A (mfderiv (𝓡 n) (𝓡 n) e.symm q v)‖ ≤ (K : ℝ) * g.tangentNorm q v
    exact hb
  obtain ⟨V, hV, _, hVdist⟩ :=
    Poincare.exists_nhds_edist_le_mul_riemannianEDist_of_mfderiv_le
      hT (fun q hq ↦ hΨ q hq.1) (zero_lt_one.trans hK) hΨbound
  have hAS : A.symm ⁻¹' S ∈ 𝓝 (A x) := by
    apply A.symm.continuous.continuousAt.preimage_mem_nhds
    simpa only [A.symm_apply_apply] using hS
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hAS
  have hΦbound (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball (A x) r) :
      ‖mfderiv (𝓡 n) (𝓡 n) Φ z‖ₑ ≤ K := by
    rw [← ofReal_norm, ENNReal.ofReal_le_coe]
    apply ContinuousLinearMap.opNorm_le_bound _ K.coe_nonneg
    intro v
    rw [hdΦ z (hball hz).1]
    change g.tangentNorm (e (A.symm z))
      (mfderiv (𝓡 n) (𝓡 n) e (A.symm z) (A.symm v)) ≤ (K : ℝ) * ‖v‖
    simpa only [A.apply_symm_apply] using ((hball hz).2 (A.symm v)).2
  have hN : (e.source ∩ A ⁻¹' Metric.ball (A x) r) ∩ e ⁻¹' V ∈ 𝓝 x :=
    inter_mem
      (inter_mem (e.open_source.mem_nhds hx)
        (A.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hr)))
      ((e.continuousAt hx).preimage_mem_nhds hV)
  obtain ⟨U, hUN, hUopen, hxU⟩ := mem_nhds_iff.mp hN
  refine ⟨U, hUopen, hxU, fun z hz ↦ (hUN hz).1.1, ?_⟩
  intro z hz w hw
  have hz' := hUN hz
  have hw' := hUN hw
  constructor
  · have hd := Poincare.riemannianEDist_le_mul_edist_of_convex (convex_ball _ _)
      (fun q hq ↦ hΦ q (hball hq).1) hΦbound hz'.1.2 hw'.1.2
    simpa only [edist, Φ, Function.comp_apply, A.symm_apply_apply] using hd
  · have hd := hVdist (e z) hz'.2 (e w) hw'.2
    simpa only [edist, Ψ, Function.comp_apply, e.left_inv hz'.1.1, e.left_inv hw'.1.1] using hd

end PoincareConjecture.RiemannianMetric
