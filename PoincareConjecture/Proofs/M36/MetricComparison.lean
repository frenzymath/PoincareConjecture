import PoincareConjecture.Proofs.M36.IntrinsicIsometry










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open MeasureTheory

universe u v

namespace PoincareConjecture.M36

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]

theorem metric_pathELength_mono (g : RiemannianMetric 3 X) (gamma : ℝ → X)
    {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b) :
    g.pathELength gamma c d ≤ g.pathELength gamma a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.pathELength_mono hac hdb

theorem metric_pathELength_add (g : RiemannianMetric 3 X) (gamma : ℝ → X)
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    g.pathELength gamma a b + g.pathELength gamma b c = g.pathELength gamma a c := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.pathELength_add hab hbc

theorem metric_edist_le_pathELength (g : RiemannianMetric 3 X) {gamma : ℝ → X}
    {a b : ℝ} (hab : a ≤ b)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Set.Icc a b)) :
    g.edist (gamma a) (gamma b) ≤ g.pathELength gamma a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_le_pathELength hgamma rfl rfl hab

theorem metric_edist_self (g : RiemannianMetric 3 X) (x : X) : g.edist x x = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_self

theorem metric_edist_triangle (g : RiemannianMetric 3 X) (x y z : X) :
    g.edist x z ≤ g.edist x y + g.edist y z := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_triangle

theorem metric_edist_continuous [RegularSpace X] (g : RiemannianMetric 3 X) :
    Continuous (fun z : X × X => g.edist z.1 z.2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : PseudoEMetricSpace X := PseudoEMetricSpace.ofRiemannianMetric (𝓡 3) X
  exact continuous_fst.edist continuous_snd

set_option backward.isDefEq.respectTransparency false in
theorem pathELength_comp_le_of_pullback_bound (g : RiemannianMetric 3 X)
    (h : RiemannianMetric 3 Y) {f : X → Y} {U : Set X}
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hmetric : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
        g.inner x v v)
    {gamma : ℝ → X} {a b : ℝ}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Set.Icc a b))
    (hU : gamma '' Set.Icc a b ⊆ U) :
    h.pathELength (f ∘ gamma) a b ≤ g.pathELength gamma a b := by
  rw [pathELength_eq_lintegral_speed_Ioo, pathELength_eq_lintegral_speed_Ioo]
  apply setLIntegral_mono' measurableSet_Ioo
  intro t ht
  have ht' : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hx := hU ⟨t, ht', rfl⟩
  have hgammaAt := ((hgamma t ht').contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
    (by simp)
  have hfAt := (hf (gamma t) hx).mdifferentiableAt (by simp)
  change ENNReal.ofReal (Real.sqrt (h.inner (f (gamma t))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (f ∘ gamma) t 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (f ∘ gamma) t 1))) ≤
    ENNReal.ofReal (Real.sqrt (g.inner (gamma t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma t 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) gamma t 1)))
  rw [mfderiv_comp t hfAt hgammaAt]
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  exact hmetric (gamma t) hx _

theorem edist_comp_le_pathELength_of_pullback_bound (g : RiemannianMetric 3 X)
    (h : RiemannianMetric 3 Y) {f : X → Y} {U : Set X}
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hmetric : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
        g.inner x v v)
    {gamma : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Set.Icc a b))
    (hU : gamma '' Set.Icc a b ⊆ U) :
    h.edist (f (gamma a)) (f (gamma b)) ≤ g.pathELength gamma a b := by
  have hc : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (f ∘ gamma) (Set.Icc a b) := by
    intro t ht
    exact ((hf (gamma t) (hU ⟨t, ht, rfl⟩)).of_le (by simp)).comp_contMDiffWithinAt t
      (hgamma t ht)
  exact (metric_edist_le_pathELength h hab hc).trans
    (pathELength_comp_le_of_pullback_bound g h hf hmetric hgamma hU)

theorem edist_le_intrinsicEDist_of_pullback_bound (g : RiemannianMetric 3 X)
    (h : RiemannianMetric 3 Y) {f : X → Y} {U : Set X}
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hmetric : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
        g.inner x v v) (x y : X) :
    h.edist (f x) (f y) ≤ intrinsicEDist g U x y := by
  apply le_sInf
  rintro L ⟨gamma, hgamma, hzero, hone, hU, rfl⟩
  have hle := edist_comp_le_pathELength_of_pullback_bound g h hf hmetric zero_le_one hgamma hU
  simpa only [hzero, hone] using hle

end PoincareConjecture.M36
