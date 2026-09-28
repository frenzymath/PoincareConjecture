import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Embedding.MetricComparison
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M47

theorem terminalGerms_pathELength_le_two
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : Type v} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    {f : M → N} {γ : ℝ → M}
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) 1 γ)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f (γ t))
    (hquad : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace (𝓡 3) (γ t),
      h.inner (f (γ t)) (mfderiv (𝓡 3) (𝓡 3) f (γ t) v)
        (mfderiv (𝓡 3) (𝓡 3) f (γ t) v) ≤ 4 * g.inner (γ t) v v) :
    h.pathELength (f ∘ γ) 0 1 ≤ 2 * g.pathELength γ 0 1 := by
  have hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      h.tangentNorm (f (γ t)) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 3) (f ∘ γ) t 1) ≤
        2 * g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 3) γ t 1) := by
    intro t ht
    have hchain := mfderiv_comp_apply t ((hf t ht).mdifferentiableAt (by simp))
      (hγ.mdifferentiable (by simp) t) (1 : ℝ)
    change Real.sqrt _ ≤ 2 * Real.sqrt _
    rw [hchain]
    calc
      _ ≤ Real.sqrt (4 * g.inner (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) (𝓡 3) γ t 1)
          (mfderiv (𝓘(ℝ, ℝ)) (𝓡 3) γ t 1)) := Real.sqrt_le_sqrt (hquad t ht _)
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [RiemannianMetric.pathELength_eq_lintegral_tangentNorm,
    RiemannianMetric.pathELength_eq_lintegral_tangentNorm]
  calc
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
        (2 * g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 3) γ t 1)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact ENNReal.ofReal_le_ofReal (hspeed t ht)
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [lintegral_const_mul']
      · norm_num
      · exact ENNReal.ofReal_ne_top

theorem terminalGerms_eventually_mem_ball
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ → Type v} [∀ k, TopologicalSpace (N k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (N k)]
    [∀ k, IsManifold (𝓡 3) ∞ (N k)]
    (g : RiemannianMetric 3 M) (h : ∀ k, RiemannianMetric 3 (N k))
    (E : ℕ → Set M) (hE : ∀ k, IsOpen (E k)) (hmono : Monotone E)
    (hcover : (⋃ k, E k) = univ) (f : ∀ k, M → N k)
    (hf : ∀ k, IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (f k) (E k))
    (hquad : ∀ K : Set M, IsCompact K → ∀ᶠ k in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        (h k).inner (f k x) (mfderiv (𝓡 3) (𝓡 3) (f k) x v)
          (mfderiv (𝓡 3) (𝓡 3) (f k) x v) ≤ 4 * g.inner x v v)
    {p x : M} {A : ℝ} (hx : x ∈ g.ball p A) :
    ∀ᶠ k in atTop, f k x ∈ (h k).ball (f k p) (2 * A) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist (𝓡 3) p x < ENNReal.ofReal A at hx
  obtain ⟨γ, hγ0, hγ1, hγ, hlength, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hx
      (zero_lt_one : (0 : ℝ) < 1)
  have hK : IsCompact (γ '' Icc (0 : ℝ) 1) := isCompact_Icc.image hγ.continuous
  obtain ⟨j, hj⟩ := hK.elim_directed_cover E hE
    (by rw [hcover]; exact subset_univ _) hmono.directed_le
  filter_upwards [hquad _ hK, eventually_ge_atTop j] with k hk hjk
  have hfγ : ∀ t ∈ Icc (0 : ℝ) 1, ContMDiffAt (𝓡 3) (𝓡 3) ∞ (f k) (γ t) :=
    fun t ht => (hf k ⟨γ t, hmono hjk (hj (mem_image_of_mem γ ht))⟩).contMDiffAt
  have hη : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 3) 1 (f k ∘ γ) (Icc 0 1) := by
    intro t ht
    exact ((hfγ t ht).of_le (by simp) |>.comp t hγ.contMDiffAt).contMDiffWithinAt
  have hdist : (h k).edist (f k p) (f k x) ≤ (h k).pathELength (f k ∘ γ) 0 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : N k → Type _) :=
      ⟨(h k).toRiemannianMetric⟩
    exact Manifold.riemannianEDist_le_pathELength hη (by simp [hγ0])
      (by simp [hγ1]) zero_le_one
  have hlen := terminalGerms_pathELength_le_two g (h k) hγ hfγ
    (fun t ht => hk (γ t) (mem_image_of_mem γ ht))
  change _ < ENNReal.ofReal (2 * A)
  calc
    _ ≤ 2 * g.pathELength γ 0 1 := hdist.trans hlen
    _ < 2 * ENNReal.ofReal A :=
      (ENNReal.mul_lt_mul_right (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)) hlength
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

end PoincareConjecture.M47
