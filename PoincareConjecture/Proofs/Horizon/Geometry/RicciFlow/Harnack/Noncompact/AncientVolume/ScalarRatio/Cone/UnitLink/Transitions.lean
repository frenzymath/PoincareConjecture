import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.IsometryTensor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.UnitLink.Manifold
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.UniversalProperty
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevel
import Mathlib.Topology.OpenPartialHomeomorph.Composition












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)



theorem edist_eq_on_isometric_chart_transition
    {n m : ℕ} {Y : Type*} [MetricSpace Y]
    (g : RiemannianMetric n (E n)) (h : RiemannianMetric m (E m))
    (F : OpenPartialHomeomorph (E n) Y) (G : OpenPartialHomeomorph (E m) Y)
    (hF : ∀ x ∈ F.source, ∀ y ∈ F.source, dist (F x) (F y) = (g.edist x y).toReal)
    (hG : ∀ x ∈ G.source, ∀ y ∈ G.source, dist (G x) (G y) = (h.edist x y).toReal) :
    ∀ x ∈ (F.trans G.symm).source, ∀ y ∈ (F.trans G.symm).source,
      h.edist ((F.trans G.symm) x) ((F.trans G.symm) y) = g.edist x y := by
  intro x hx y hy
  change x ∈ F.source ∧ F x ∈ G.target at hx
  change y ∈ F.source ∧ F y ∈ G.target at hy
  apply (ENNReal.toReal_eq_toReal_iff' (h.edist_ne_top _ _) (g.edist_ne_top _ _)).mp
  change (h.edist (G.symm (F x)) (G.symm (F y))).toReal = (g.edist x y).toReal
  rw [← hG _ (G.map_target hx.2) _ (G.map_target hy.2),
    G.right_inv hx.2, G.right_inv hy.2, hF x hx.1 y hy.1]



theorem contDiffOn_isometric_chart_transition
    {n m : ℕ} {Y : Type*} [MetricSpace Y]
    (g : RiemannianMetric n (E n)) (h : RiemannianMetric m (E m))
    (F : OpenPartialHomeomorph (E n) Y) (G : OpenPartialHomeomorph (E m) Y)
    (hF : ∀ x ∈ F.source, ∀ y ∈ F.source, dist (F x) (F y) = (g.edist x y).toReal)
    (hG : ∀ x ∈ G.source, ∀ y ∈ G.source, dist (G x) (G y) = (h.edist x y).toReal) :
    ContDiffOn ℝ ∞ (F.trans G.symm) (F.trans G.symm).source :=
  g.contDiffOn_of_edist_eq h (F.trans G.symm).open_source
    (g.edist_eq_on_isometric_chart_transition h F G hF hG)




theorem contMDiffOn_regularLevel_transition_of_isometric_charts
    {n : ℕ} {Y : Type*} [MetricSpace Y]
    (g h : RiemannianMetric (n + 1) (E (n + 1)))
    (F G : OpenPartialHomeomorph (E (n + 1)) Y)
    (hF : ∀ x ∈ F.source, ∀ y ∈ F.source, dist (F x) (F y) = (g.edist x y).toReal)
    (hG : ∀ x ∈ G.source, ∀ y ∈ G.source, dist (G x) (G y) = (h.edist x y).toReal)
    (f₁ f₂ : E (n + 1) → ℝ)
    (hf₁ : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f₁)
    (hf₂ : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f₂)
    (hreg₁ : ∀ x ∈ F.source, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f₁ x ≠ 0)
    (hreg₂ : ∀ x ∈ G.source, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f₂ x ≠ 0)
    (c : ℝ) :
    let U₁ : Opens (E (n + 1)) := ⟨F.source, F.open_source⟩
    let U₂ : Opens (E (n + 1)) := ⟨G.source, G.open_source⟩
    letI : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf₁ U₁ hreg₁ n c
    letI := openLevelSetChartedSpace hf₂ U₂ hreg₂ n c
    ∀ T : OpenPartialHomeomorph (openLevelSet f₁ U₁ c) (openLevelSet f₂ U₂ c),
      (∀ x ∈ T.source, G (openLevelIncl f₂ U₂ c (T x)) = F (openLevelIncl f₁ U₁ c x)) →
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ T T.source := by
  let U₁ : Opens (E (n + 1)) := ⟨F.source, F.open_source⟩
  let U₂ : Opens (E (n + 1)) := ⟨G.source, G.open_source⟩
  let : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf₁ U₁ hreg₁ n c
  let := openLevelSetChartedSpace hf₂ U₂ hreg₂ n c
  dsimp only
  intro T hT x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_into_openLevelSet_iff hf₂ n c U₂ hreg₂ T x).mpr
  have hxin : openLevelIncl f₁ U₁ c x ∈ (F.trans G.symm).source := by
    change openLevelIncl f₁ U₁ c x ∈ F.source ∧ F (openLevelIncl f₁ U₁ c x) ∈ G.target
    refine ⟨x.1.2, ?_⟩
    rw [← hT x hx]
    exact G.map_source (T x).1.2
  have hs : ContMDiffAt (𝓡 (n + 1)) (𝓡 (n + 1)) ∞
      (F.trans G.symm) (openLevelIncl f₁ U₁ c x) :=
    ((g.contDiffOn_isometric_chart_transition h F G hF hG).contDiffAt
      ((F.trans G.symm).open_source.mem_nhds hxin)).contMDiffAt
  have hcomp := hs.comp x (contMDiff_openLevelIncl hf₁ U₁ hreg₁ n c x)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [T.open_source.mem_nhds hx] with z hz
  change openLevelIncl f₂ U₂ c (T z) = G.symm (F (openLevelIncl f₁ U₁ c z))
  rw [← hT z hz]
  exact (G.left_inv (T z).1.2).symm




theorem regularLevelMetric_transition_of_isometric_charts
    {n : ℕ} {Y : Type*} [MetricSpace Y]
    (g h : RiemannianMetric (n + 1) (E (n + 1)))
    (F G : OpenPartialHomeomorph (E (n + 1)) Y)
    (hF : ∀ x ∈ F.source, ∀ y ∈ F.source, dist (F x) (F y) = (g.edist x y).toReal)
    (hG : ∀ x ∈ G.source, ∀ y ∈ G.source, dist (G x) (G y) = (h.edist x y).toReal)
    (f₁ f₂ : E (n + 1) → ℝ)
    (hf₁ : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f₁)
    (hf₂ : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f₂)
    (hreg₁ : ∀ x ∈ F.source, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f₁ x ≠ 0)
    (hreg₂ : ∀ x ∈ G.source, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f₂ x ≠ 0)
    (c : ℝ) :
    let U₁ : Opens (E (n + 1)) := ⟨F.source, F.open_source⟩
    let U₂ : Opens (E (n + 1)) := ⟨G.source, G.open_source⟩
    letI : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf₁ U₁ hreg₁ n c
    letI := openLevelSetChartedSpace hf₂ U₂ hreg₂ n c
    letI := isManifold_openLevelSet hf₁ U₁ hreg₁ n c
    letI := isManifold_openLevelSet hf₂ U₂ hreg₂ n c
    ∀ T : OpenPartialHomeomorph (openLevelSet f₁ U₁ c) (openLevelSet f₂ U₂ c),
      (∀ x ∈ T.source, G (openLevelIncl f₂ U₂ c (T x)) = F (openLevelIncl f₁ U₁ c x)) →
      ∀ x ∈ T.source, ∀ v w : E n,
        (regularLevelMetric hf₂ U₂ hreg₂ c h).inner (T x)
          (mfderiv (𝓡 n) (𝓡 n) T x v) (mfderiv (𝓡 n) (𝓡 n) T x w) =
            (regularLevelMetric hf₁ U₁ hreg₁ c g).inner x v w := by
  let U₁ : Opens (E (n + 1)) := ⟨F.source, F.open_source⟩
  let U₂ : Opens (E (n + 1)) := ⟨G.source, G.open_source⟩
  let : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf₁ U₁ hreg₁ n c
  let := openLevelSetChartedSpace hf₂ U₂ hreg₂ n c
  let := isManifold_openLevelSet hf₁ U₁ hreg₁ n c
  let := isManifold_openLevelSet hf₂ U₂ hreg₂ n c
  dsimp only
  intro T hT x hx v w
  change TangentSpace (𝓡 n) x at v w
  have hxin : openLevelIncl f₁ U₁ c x ∈ (F.trans G.symm).source := by
    change openLevelIncl f₁ U₁ c x ∈ F.source ∧ F (openLevelIncl f₁ U₁ c x) ∈ G.target
    refine ⟨x.1.2, ?_⟩
    rw [← hT x hx]
    exact G.map_source (T x).1.2
  have hsT := (g.contMDiffOn_regularLevel_transition_of_isometric_charts h F G hF hG
    f₁ f₂ hf₁ hf₂ hreg₁ hreg₂ c T hT).contMDiffAt (T.open_source.mem_nhds hx)
  obtain ⟨hsA, _, hmetric⟩ := g.smooth_isometric_charts_of_edist_eq h (F.trans G.symm)
    (g.edist_eq_on_isometric_chart_transition h F G hF hG)
  have heq : openLevelIncl f₂ U₂ c ∘ T =ᶠ[𝓝 x]
      (F.trans G.symm) ∘ openLevelIncl f₁ U₁ c := by
    filter_upwards [T.open_source.mem_nhds hx] with z hz
    change openLevelIncl f₂ U₂ c (T z) = G.symm (F (openLevelIncl f₁ U₁ c z))
    rw [← hT z hz]
    exact (G.left_inv (T z).1.2).symm
  have hderiv := heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓡 (n + 1))
  rw [mfderiv_comp x
      ((contMDiff_openLevelIncl hf₂ U₂ hreg₂ n c (T x)).mdifferentiableAt (by simp))
      (hsT.mdifferentiableAt (by simp)),
    mfderiv_comp x
      ((hsA.contMDiffAt ((F.trans G.symm).open_source.mem_nhds hxin)).mdifferentiableAt (by simp))
      ((contMDiff_openLevelIncl hf₁ U₁ hreg₁ n c x).mdifferentiableAt (by simp))] at hderiv
  have hvec (a : TangentSpace (𝓡 n) x) :
      mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f₂ U₂ c) (T x)
        (mfderiv (𝓡 n) (𝓡 n) T x a) =
      mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (F.trans G.symm) (openLevelIncl f₁ U₁ c x)
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f₁ U₁ c) x a) :=
    congrArg (fun A => A a) hderiv
  change h.inner (openLevelIncl f₂ U₂ c (T x))
    (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f₂ U₂ c) (T x)
      (mfderiv (𝓡 n) (𝓡 n) T x v))
    (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f₂ U₂ c) (T x)
      (mfderiv (𝓡 n) (𝓡 n) T x w)) =
    g.inner (openLevelIncl f₁ U₁ c x)
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f₁ U₁ c) x v)
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f₁ U₁ c) x w)
  rw [hvec v, hvec w]
  have hvalue : openLevelIncl f₂ U₂ c (T x) = (F.trans G.symm) (openLevelIncl f₁ U₁ c x) :=
    heq.self_of_nhds
  rw [hvalue]
  exact hmetric _ hxin _ _

end PoincareConjecture.RiemannianMetric

namespace Poincare.AncientVolume.ScalarRatio.UnitSliceRadialChartData

variable {X : Type*} [MetricSpace X] {p : X} {hcomparison : RayComparison p} {n : ℕ}

theorem levelEmbedding_val (d : UnitSliceRadialChartData hcomparison n)
    (z x : d.Level) :
    (d.levelEmbedding z x).1 = d.ambientChart (openLevelIncl d.potential d.source (1 / 2) x) := rfl



def levelTransition (d₁ d₂ : UnitSliceRadialChartData hcomparison n)
    (z₁ : d₁.Level) (z₂ : d₂.Level) : OpenPartialHomeomorph d₁.Level d₂.Level :=
  (d₁.levelEmbedding z₁).trans (d₂.levelEmbedding z₂).symm

theorem levelTransition_ambient (d₁ d₂ : UnitSliceRadialChartData hcomparison n)
    (z₁ : d₁.Level) (z₂ : d₂.Level) {x : d₁.Level}
    (hx : x ∈ (d₁.levelTransition d₂ z₁ z₂).source) :
    d₂.ambientChart (openLevelIncl d₂.potential d₂.source (1 / 2)
      (d₁.levelTransition d₂ z₁ z₂ x)) =
        d₁.ambientChart (openLevelIncl d₁.potential d₁.source (1 / 2) x) := by
  have htarget : d₁.levelEmbedding z₁ x ∈ (d₂.levelEmbedding z₂).target := hx.2
  have hh := congrArg Subtype.val ((d₂.levelEmbedding z₂).right_inv htarget)
  exact hh

theorem contMDiffOn_levelTransition (d₁ d₂ : UnitSliceRadialChartData hcomparison n)
    (z₁ : d₁.Level) (z₂ : d₂.Level) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (d₁.levelTransition d₂ z₁ z₂)
      (d₁.levelTransition d₂ z₁ z₂).source :=
  d₁.metric.contMDiffOn_regularLevel_transition_of_isometric_charts d₂.metric
    d₁.ambientChart d₂.ambientChart d₁.distance d₂.distance
    d₁.potential d₂.potential d₁.smooth d₂.smooth d₁.regular d₂.regular (1 / 2)
    (d₁.levelTransition d₂ z₁ z₂) (fun _ hx => d₁.levelTransition_ambient d₂ z₁ z₂ hx)



theorem regularLevelMetric_levelTransition
    (d₁ d₂ : UnitSliceRadialChartData hcomparison n)
    (z₁ : d₁.Level) (z₂ : d₂.Level) {x : d₁.Level}
    (hx : x ∈ (d₁.levelTransition d₂ z₁ z₂).source)
    (v w : EuclideanSpace ℝ (Fin n)) :
    letI : Fact (Module.finrank ℝ (UnitSliceAmbient n) = n + 1) := ⟨finrank_euclideanSpace_fin⟩
    (PoincareConjecture.RiemannianMetric.regularLevelMetric d₂.smooth d₂.source d₂.regular (1 / 2) d₂.metric).inner
      (d₁.levelTransition d₂ z₁ z₂ x)
      (mfderiv (𝓡 n) (𝓡 n) (d₁.levelTransition d₂ z₁ z₂) x v)
      (mfderiv (𝓡 n) (𝓡 n) (d₁.levelTransition d₂ z₁ z₂) x w) =
        (PoincareConjecture.RiemannianMetric.regularLevelMetric d₁.smooth d₁.source d₁.regular (1 / 2) d₁.metric).inner
          x v w :=
  d₁.metric.regularLevelMetric_transition_of_isometric_charts d₂.metric
    d₁.ambientChart d₂.ambientChart d₁.distance d₂.distance
    d₁.potential d₂.potential d₁.smooth d₂.smooth d₁.regular d₂.regular (1 / 2)
    (d₁.levelTransition d₂ z₁ z₂) (fun _ hx => d₁.levelTransition_ambient d₂ z₁ z₂ hx)
    x hx v w



theorem contDiffOn_chart_transition (d₁ d₂ : UnitSliceRadialChartData hcomparison n)
    (z₁ : d₁.Level) (z₂ : d₂.Level) :
    ContDiffOn ℝ ∞ ((d₁.chart z₁).symm.trans (d₂.chart z₂))
      ((d₁.chart z₁).symm.trans (d₂.chart z₂)).source := by
  let a₁ := chartAt (EuclideanSpace ℝ (Fin n)) z₁
  let a₂ := chartAt (EuclideanSpace ℝ (Fin n)) z₂
  let T := d₁.levelTransition d₂ z₁ z₂
  have heq : (d₁.chart z₁).symm.trans (d₂.chart z₂) =
      (a₁.symm.trans T).trans a₂ := by
    simp only [chart, levelTransition, levelEmbedding, a₁, a₂, T,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc]
  rw [heq]
  have h₁ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ a₁.symm a₁.target := contMDiffOn_chart_symm
  have h₂ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ a₂ a₂.source := contMDiffOn_chart
  have hT : ContMDiffOn (𝓡 n) (𝓡 n) ∞ T T.source :=
    d₁.contMDiffOn_levelTransition d₂ z₁ z₂
  have hfirst : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (a₁.symm.trans T) (a₁.symm.trans T).source := by
    exact hT.comp (h₁.mono (fun _ hx => hx.1)) (fun _ hx => hx.2)
  have htotal : ContMDiffOn (𝓡 n) (𝓡 n) ∞ ((a₁.symm.trans T).trans a₂)
      ((a₁.symm.trans T).trans a₂).source := by
    exact h₂.comp (hfirst.mono (fun _ hx => hx.1)) (fun _ hx => hx.2)
  exact contMDiffOn_iff_contDiffOn.mp htotal

end Poincare.AncientVolume.ScalarRatio.UnitSliceRadialChartData
