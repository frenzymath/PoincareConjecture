import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Maximum











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M]

omit [T3Space M] [ConnectedSpace M] in
private theorem gradient_const_mul (g : RiemannianMetric (m + 1) M)
    (D : LeviCivitaData g) (c : ℝ) (f : M → ℝ) (x : M) :
    D.gradient (fun y => c * f y) x = c • D.gradient f x := by
  apply (g.inner_isInvertible x).injective
  ext v
  simp only [D.inner_gradient, mvfderiv_const_mul, map_smul, smul_apply,
    smul_eq_mul]



theorem exists_busemannApprox_lower_support
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g)
    (hRic : ∀ y : M, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      0 ≤ D.ricci y v v)
    (γ : ℝ → M) (t : ℝ) (x : M) (hpx : γ t ≠ x) :
    ∃ (U : Set M) (σ : M → ℝ), IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ σ U ∧
      σ x = t - (g.edist (γ t) x).toReal ∧
      (∀ y ∈ U, σ y ≤ t - (g.edist (γ t) y).toReal) ∧
      g.inner x (D.gradient σ x) (D.gradient σ x) = 1 ∧
      -(2 * (m : ℝ) / (g.edist (γ t) x).toReal) ≤ D.laplacian σ x := by
  obtain ⟨U, ρ, hU, hx, hρ, heq, hle, hgrad, hlap⟩ :=
    g.exists_distance_laplacian_upper_support D hm hcomplete (k := 0)
      le_rfl (by simpa using hRic) (γ t) x hpx
  have hρx := hρ.contMDiffAt (hU.mem_nhds hx)
  have hneg : ContMDiffAt (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞
      (fun y => (-1 : ℝ) * ρ y) x := contMDiffAt_const.mul hρx
  refine ⟨U, (fun y => t + (-1) * ρ y), hU, hx, ?_, ?_, ?_, ?_, ?_⟩
  · exact contMDiffOn_const.add (contMDiffOn_const.mul hρ)
  · change t + (-1) * ρ x = t - (g.edist (γ t) x).toReal
    rw [heq]
    ring
  · intro y hy
    have := hle y hy
    linarith
  · rw [D.gradient_const_add_at (hneg.mdifferentiableAt (by simp)) t,
      gradient_const_mul g D (-1) ρ x]
    simpa only [map_smul, smul_apply, smul_eq_mul, neg_one_mul, neg_neg] using hgrad
  · rw [D.laplacian_const_add_at hneg t,
      D.laplacian_const_mul]
    simp only [mul_zero, add_zero] at hlap
    linarith



theorem eventually_le_toReal_edist_line_on_compact
    (g : RiemannianMetric (m + 1) M) (γ : ℝ → M)
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    {K : Set M} (hK : IsCompact K) (A : ℝ) :
    ∀ᶠ t : ℝ in atTop, ∀ x ∈ K, A ≤ (g.edist (γ t) x).toReal := by
  obtain ⟨R, hR⟩ := hK.bddAbove_image (g.continuous_toReal_edist (γ 0)).continuousOn
  filter_upwards [eventually_ge_atTop (max 0 (A + R))] with t ht x hx
  have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
  have hline : (g.edist (γ t) (γ 0)).toReal = t := by
    rw [hγ, sub_zero, abs_of_nonneg ht0, ENNReal.toReal_ofReal ht0]
  have hcomm : g.edist x (γ 0) = g.edist (γ 0) x := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact Manifold.riemannianEDist_comm
  have htriangle := g.toReal_edist_triangle (γ t) x (γ 0)
  rw [hline, hcomm] at htriangle
  have hxR := hR (mem_image_of_mem _ hx)
  have hAR : A + R ≤ t := (le_max_right _ _).trans ht
  linarith



theorem eventually_busemannApprox_lower_supports_on_compact
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g)
    (hRic : ∀ y : M, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      0 ≤ D.ricci y v v)
    (γ : ℝ → M)
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    {K : Set M} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ x ∈ K,
      ∃ (U : Set M) (σ : M → ℝ), IsOpen U ∧ x ∈ U ∧
        ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ σ U ∧
        σ x = t - (g.edist (γ t) x).toReal ∧
        (∀ y ∈ U, σ y ≤ t - (g.edist (γ t) y).toReal) ∧
        g.inner x (D.gradient σ x) (D.gradient σ x) = 1 ∧
        -ε ≤ D.laplacian σ x := by
  filter_upwards [g.eventually_le_toReal_edist_line_on_compact γ hγ hK
    (2 * (m : ℝ) / ε + 1)] with t ht x hx
  have hdist := ht x hx
  have hnonneg : 0 ≤ 2 * (m : ℝ) / ε := by positivity
  have hpos : 0 < (g.edist (γ t) x).toReal := by linarith
  have hpx : γ t ≠ x := by
    intro heq
    have hself := hγ t t
    rw [heq, sub_self, abs_zero, ENNReal.ofReal_zero] at hself
    rw [heq, hself, ENNReal.toReal_zero] at hpos
    exact (lt_irrefl 0) hpos
  obtain ⟨U, σ, hU, hxU, hσ, heq, hle, hgrad, hlap⟩ :=
    g.exists_busemannApprox_lower_support D hm hcomplete hRic γ t x hpx
  refine ⟨U, σ, hU, hxU, hσ, heq, hle, hgrad, ?_⟩
  have hquot : 2 * (m : ℝ) / (g.edist (γ t) x).toReal ≤ ε := by
    apply (div_le_iff₀ hpos).2
    have h := (div_le_iff₀ hε).mp (show 2 * (m : ℝ) / ε ≤
      (g.edist (γ t) x).toReal by linarith)
    nlinarith
  linarith

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem laplacian_upper_test_ge_of_lower_support (D : LeviCivitaData g)
    {u φ σ : M → ℝ} {U V : Set M} {x : M} {a : ℝ}
    (hU : IsOpen U) (hxU : x ∈ U)
    (hσ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ U)
    (heq : σ x = u x) (hle : ∀ y ∈ U, σ y ≤ u y)
    (hlap : a ≤ D.laplacian σ x)
    (hV : IsOpen V) (hxV : x ∈ V)
    (hφ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ V)
    (hmax : IsLocalMax (fun y => u y - φ y) x) :
    a ≤ D.laplacian φ x := by
  have hlocal : IsLocalMax (fun y => σ y - φ y) x := by
    filter_upwards [hU.mem_nhds hxU, hmax] with y hy hm
    change σ y - φ y ≤ σ x - φ x
    rw [heq]
    exact (sub_le_sub_right (hle y hy) _).trans hm
  have hsub := Dirichlet.laplacian_nonpos_of_isLocalMax_on D (hU.inter hV)
    ((hσ.mono inter_subset_left).sub (hφ.mono inter_subset_right))
    ⟨hxU, hxV⟩ hlocal
  rw [Dirichlet.laplacian_sub_on D (hU.inter hV)
    (hσ.mono inter_subset_left) (hφ.mono inter_subset_right) ⟨hxU, hxV⟩] at hsub
  linarith



theorem le_on_compact_of_lower_supports (D : LeviCivitaData g)
    {K : Set M} (hK : IsCompact K) {u φ : M → ℝ} {a : ℝ}
    (hu : ContinuousOn u K)
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hsupport : ∀ x ∈ interior K,
      ∃ (U : Set M) (σ : M → ℝ), IsOpen U ∧ x ∈ U ∧
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ U ∧
        σ x = u x ∧ (∀ y ∈ U, σ y ≤ u y) ∧ a ≤ D.laplacian σ x)
    (hlap : ∀ x ∈ interior K, D.laplacian φ x < a)
    (hboundary : ∀ x ∈ K, x ∉ interior K → u x ≤ φ x) :
    ∀ x ∈ K, u x ≤ φ x := by
  intro x hx
  by_contra hfail
  obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn ⟨x, hx⟩
    (hu.sub hφ.continuous.continuousOn)
  have hpos : 0 < u q - φ q :=
    (sub_pos.mpr (lt_of_not_ge hfail)).trans_le (hmax hx)
  have hqint : q ∈ interior K := by
    by_contra hnot
    exact (not_le_of_gt hpos) (sub_nonpos.mpr (hboundary q hq hnot))
  have hlocal : IsLocalMax (fun y => u y - φ y) q := by
    filter_upwards [isOpen_interior.mem_nhds hqint] with y hy
    exact hmax (interior_subset hy)
  obtain ⟨U, σ, hU, hqU, hσ, heq, hle, hσlap⟩ := hsupport q hqint
  have htest := D.laplacian_upper_test_ge_of_lower_support hU hqU hσ heq hle hσlap
    isOpen_univ (mem_univ q) hφ.contMDiffOn hlocal
  exact (not_le_of_gt (hlap q hqint)) htest

end PoincareConjecture.LeviCivitaData
