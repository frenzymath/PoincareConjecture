import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Distance.MetricPathLength
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open MeasureTheory

universe u v

namespace PoincareConjecture.MetricSurgery

theorem pathELength_eq_lintegral_speed_Ioo
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]
    (g : RiemannianMetric n X) (gamma : ℝ → X) (a b : ℝ) :
    g.pathELength gamma a b =
      ∫⁻ t in Set.Ioo a b, ENNReal.ofReal (metricPathSpeed g gamma t) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.pathELength (𝓡 n) gamma a b = _
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t _
  dsimp only
  erw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]

omit [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y] in
theorem path_contMDiffOn_comp_at {f : X → Y} {U : Set X}
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    {gamma : ℝ → X}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Set.Icc (0 : ℝ) 1))
    (hU : gamma '' Set.Icc (0 : ℝ) 1 ⊆ U) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (f ∘ gamma) (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  exact ((hf (gamma t) (hU ⟨t, ht, rfl⟩)).of_le (by simp)).comp_contMDiffWithinAt t
    (hgamma t ht)

set_option backward.isDefEq.respectTransparency false in
theorem pathELength_comp_eq_of_pullback (g : RiemannianMetric 3 X)
    (h : RiemannianMetric 3 Y) {f : X → Y} {U : Set X}
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hmetric : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 3) x,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) =
        g.inner x v w)
    {gamma : ℝ → X}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Set.Icc (0 : ℝ) 1))
    (hU : gamma '' Set.Icc (0 : ℝ) 1 ⊆ U) :
    h.pathELength (f ∘ gamma) 0 1 = g.pathELength gamma 0 1 := by
  rw [pathELength_eq_lintegral_speed_Ioo, pathELength_eq_lintegral_speed_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hgammaAt := ((hgamma t ht').contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
    (by simp)
  have hfAt := (hf (gamma t) (hU ⟨t, ht', rfl⟩)).mdifferentiableAt (by simp)
  change ENNReal.ofReal (h.tangentNorm (f (gamma t))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (f ∘ gamma) t 1)) =
    ENNReal.ofReal (g.tangentNorm (gamma t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma t 1))
  rw [mfderiv_comp t hfAt hgammaAt]
  simp only [ContinuousLinearMap.comp_apply, Function.comp_apply, RiemannianMetric.tangentNorm,
    hmetric (gamma t) (hU ⟨t, ht', rfl⟩)]

theorem intrinsicEDist_image_le_of_pullback (g : RiemannianMetric 3 X)
    (h : RiemannianMetric 3 Y) {f : X → Y} {U : Set X}
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hmetric : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 3) x,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) =
        g.inner x v w)
    (x y : X) :
    intrinsicEDist h (f '' U) (f x) (f y) ≤ intrinsicEDist g U x y := by
  apply le_sInf
  rintro L ⟨gamma, hgamma, hzero, hone, hU, rfl⟩
  apply sInf_le
  refine ⟨f ∘ gamma, path_contMDiffOn_comp_at hf hgamma hU, ?_, ?_, ?_, ?_⟩
  · simp only [Function.comp_apply, hzero]
  · simp only [Function.comp_apply, hone]
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨gamma t, hU ⟨t, ht, rfl⟩, rfl⟩
  · exact (pathELength_comp_eq_of_pullback g h hf hmetric hgamma hU).symm

theorem intrinsicEDist_image_eq_of_inverse_pullbacks (g : RiemannianMetric 3 X)
    (h : RiemannianMetric 3 Y) {f : X → Y} {k : Y → X} {U : Set X}
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hk : ∀ y ∈ f '' U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ k y)
    (hinv : Set.LeftInvOn k f U)
    (hmetric : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 3) x,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) =
        g.inner x v w)
    (hmetricInv : ∀ y ∈ f '' U, ∀ v w : TangentSpace (𝓡 3) y,
      g.inner (k y) (mfderiv (𝓡 3) (𝓡 3) k y v) (mfderiv (𝓡 3) (𝓡 3) k y w) =
        h.inner y v w)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    intrinsicEDist h (f '' U) (f x) (f y) = intrinsicEDist g U x y := by
  apply le_antisymm (intrinsicEDist_image_le_of_pullback g h hf hmetric x y)
  have himage : k '' (f '' U) = U := by
    ext z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      simpa only [hinv hw] using hw
    · intro hz
      exact ⟨f z, ⟨z, hz, rfl⟩, hinv hz⟩
  have hle := intrinsicEDist_image_le_of_pullback h g hk hmetricInv (f x) (f y)
  simpa only [himage, hinv hx, hinv hy] using hle

end PoincareConjecture.MetricSurgery
