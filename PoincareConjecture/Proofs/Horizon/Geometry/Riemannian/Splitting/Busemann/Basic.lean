import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.UniformSpace.Dini

















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


def busemannApprox (g : RiemannianMetric n M) (γ : ℝ → M) (t : ℝ) (x : M) : ℝ :=
  t - (g.edist (γ t) x).toReal


def busemann (g : RiemannianMetric n M) (γ : ℝ → M) (x : M) : ℝ :=
  ⨆ t : Set.Ici (0 : ℝ), g.busemannApprox γ t x

variable [T3Space M] [PreconnectedSpace M] (g : RiemannianMetric n M)
  {γ : ℝ → M}

omit [T3Space M] [PreconnectedSpace M] in
private theorem line_distance
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) (s t : ℝ) :
    (g.edist (γ s) (γ t)).toReal = |s - t| := by
  rw [hγ, ENNReal.toReal_ofReal (abs_nonneg _)]

theorem continuous_busemannApprox (γ : ℝ → M) (t : ℝ) :
    Continuous (g.busemannApprox γ t) :=
  continuous_const.sub (g.continuous_toReal_edist (γ t))

theorem abs_busemannApprox_sub_le (γ : ℝ → M) (t : ℝ) (x y : M) :
    |g.busemannApprox γ t x - g.busemannApprox γ t y| ≤ (g.edist x y).toReal := by
  simpa only [busemannApprox, sub_sub_sub_cancel_left, abs_sub_comm] using
    g.abs_toReal_edist_sub_le (γ t) x y

theorem busemannApprox_monotone
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) (x : M) :
    Monotone (fun t => g.busemannApprox γ t x) := by
  intro s t hst
  have h := g.toReal_edist_triangle (γ t) (γ s) x
  rw [g.line_distance hγ, abs_of_nonneg (sub_nonneg.mpr hst)] at h
  dsimp [busemannApprox]
  linarith

theorem busemannApprox_le_distance
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (t : ℝ) (x : M) : g.busemannApprox γ t x ≤ (g.edist (γ 0) x).toReal := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := g.toReal_edist_triangle (γ 0) x (γ t)
  have hc : g.edist x (γ t) = g.edist (γ t) x := Manifold.riemannianEDist_comm
  rw [g.line_distance hγ, zero_sub, abs_neg, hc] at h
  dsimp [busemannApprox]
  linarith [le_abs_self t]

theorem busemannApprox_bddAbove
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) (x : M) :
    BddAbove (Set.range fun t : Set.Ici (0 : ℝ) => g.busemannApprox γ t x) :=
  ⟨(g.edist (γ 0) x).toReal, by
    rintro _ ⟨t, rfl⟩
    exact g.busemannApprox_le_distance hγ t x⟩

theorem busemannApprox_le_busemann
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    {t : ℝ} (ht : 0 ≤ t) (x : M) : g.busemannApprox γ t x ≤ g.busemann γ x :=
  le_ciSup (g.busemannApprox_bddAbove hγ x) ⟨t, ht⟩

theorem tendsto_busemannApprox
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) (x : M) :
    Tendsto (fun t => g.busemannApprox γ t x) atTop (𝓝 (g.busemann γ x)) :=
  tendsto_comp_val_Ici_atTop.mp
    (tendsto_atTop_ciSup ((g.busemannApprox_monotone hγ x).comp (Subtype.mono_coe _))
      (g.busemannApprox_bddAbove hγ x))

theorem abs_busemann_sub_le
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) (x y : M) :
    |g.busemann γ x - g.busemann γ y| ≤ (g.edist x y).toReal :=
  le_of_tendsto ((g.tendsto_busemannApprox hγ x).sub
    (g.tendsto_busemannApprox hγ y) |>.abs)
    (Eventually.of_forall fun t => g.abs_busemannApprox_sub_le γ t x y)

theorem continuous_busemann
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    Continuous (g.busemann γ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : MetricSpace M := EMetricSpace.toMetricSpace (g.edist_ne_top)
  have hLip : LipschitzWith 1 (g.busemann γ) := LipschitzWith.mk_one fun x y => by
    rw [Real.dist_eq, dist_edist]
    exact g.abs_busemann_sub_le hγ x y
  exact hLip.continuous

theorem tendstoUniformlyOn_busemannApprox
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    {K : Set M} (hK : IsCompact K) :
    TendstoUniformlyOn (g.busemannApprox γ) (g.busemann γ) atTop K :=
  Monotone.tendstoUniformlyOn_of_forall_tendsto hK
    (fun t => (g.continuous_busemannApprox γ t).continuousOn)
    (fun x _ => g.busemannApprox_monotone hγ x)
    (g.continuous_busemann hγ).continuousOn (fun x _ => g.tendsto_busemannApprox hγ x)

theorem busemann_apply_line
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) (s : ℝ) :
    g.busemann γ (γ s) = s := by
  apply tendsto_nhds_unique (g.tendsto_busemannApprox hγ (γ s))
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop s] with t ht
  dsimp [busemannApprox]
  rw [g.line_distance hγ, abs_of_nonneg (sub_nonneg.mpr ht)]
  ring

omit [T3Space M] [PreconnectedSpace M] in
theorem minimizing_line_reverse
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    ∀ s t : ℝ, g.edist (γ (-s)) (γ (-t)) = ENNReal.ofReal |s - t| := by
  intro s t
  rw [hγ, neg_sub_neg, abs_sub_comm]

theorem busemann_add_reverse_le_zero
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) (x : M) :
    g.busemann γ x + g.busemann (fun t => γ (-t)) x ≤ 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply le_of_tendsto ((g.tendsto_busemannApprox hγ x).add
    (g.tendsto_busemannApprox (g.minimizing_line_reverse hγ) x))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h := g.toReal_edist_triangle (γ t) x (γ (-t))
  have hc : g.edist x (γ (-t)) = g.edist (γ (-t)) x :=
    Manifold.riemannianEDist_comm
  rw [g.line_distance hγ, sub_neg_eq_add, abs_of_nonneg (by linarith), hc] at h
  dsimp [busemannApprox]
  linarith

theorem busemann_add_reverse_apply_line
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) (s : ℝ) :
    g.busemann γ (γ s) + g.busemann (fun t => γ (-t)) (γ s) = 0 := by
  have hr := g.busemann_apply_line (g.minimizing_line_reverse hγ) (-s)
  simpa [g.busemann_apply_line hγ s] using congrArg (fun r => s + r) hr

end PoincareConjecture.RiemannianMetric
