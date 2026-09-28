import PoincareConjecture.Proofs.M10.IntrinsicLipschitz
import PoincareConjecture.Proofs.M10.SpatialSupports
import PoincareConjecture.Proofs.M10.TimeLipschitz
import PoincareConjecture.Definitions.Ch06.ReducedVolume









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}

set_option backward.isDefEq.respectTransparency false in

theorem reducedLength_locallyLipschitz
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ J) (p : M) :
    reducedLengthLocallyLipschitz F T τmax p := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨(F.metric T).inner, (F.metric T).toContinuousRiemannianMetric.continuous,
      fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  change LocallyLipschitzOn (univ ×ˢ Ioo 0 τmax)
    (fun z : M × ℝ ↦ reducedLength F T p z.1 z.2)
  intro z hz
  obtain ⟨N, hNopen, hzN, hNtime, C, D, hsupports⟩ :=
    reducedLength_local_terminal_supports hDifferential hwindow z hz (p := p)
  obtain ⟨U, hU, S, hS, hUS⟩ := mem_nhds_prod_iff.mp (hNopen.mem_nhds hzN)
  obtain ⟨a, b, hzI, hIS⟩ := mem_nhds_iff_exists_Ioo_subset.mp hS
  have hUI : U ×ˢ Ioo a b ⊆ N := fun w hw ↦ hUS ⟨hw.1, hIS hw.2⟩
  have hItime : Ioo a b ⊆ Ioo 0 τmax := by
    intro s hs
    have hmem : (z.1, s) ∈ N := hUI ⟨mem_of_mem_nhds hU, hs⟩
    exact (hNtime hmem).2
  obtain ⟨ε, hε, hεU⟩ := EMetric.mem_nhds_iff.mp hU
  obtain ⟨r, hr, hrε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (by norm_num : (3 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) hε.ne'
  have hsum : (r : ℝ≥0∞) + r + r < ε := by
    convert hrε using 1
    ring
  have hrle : (r : ℝ≥0∞) ≤ r + r + r := by
    exact (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ r from bot_le)).trans
      (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ r from bot_le))
  have hsmallU : Metric.eball z.1 (r : ℝ≥0∞) ⊆ U :=
    fun q hq ↦ hεU (hq.trans_le (hrle.trans hsum.le))
  refine ⟨C + D, Metric.eball z.1 (r : ℝ≥0∞) ×ˢ Ioo a b,
    mem_nhdsWithin_of_mem_nhds ?_, ?_⟩
  · exact prod_mem_nhds (Metric.eball_mem_nhds _ (ENNReal.coe_pos.mpr hr))
      (isOpen_Ioo.mem_nhds hzI)
  intro x hx y hy
  have hspatial : edist (reducedLength F T p x.1 x.2) (reducedLength F T p y.1 x.2) ≤
      (C : ℝ≥0∞) * edist x.1 y.1 := by
    change edist (reducedLength F T p x.1 x.2) (reducedLength F T p y.1 x.2) ≤
      (C : ℝ≥0∞) * (F.metric T).edist x.1 y.1
    refine edist_le_mul_riemannianEDist_of_upper_supports (F.metric T)
      (f := fun q ↦ reducedLength F T p q x.2) (C := C)
      (U := U) (x₀ := z.1) (x := x.1) (y := y.1) (r := r) ?_ ?_ ?_ ?_ ?_
    · exact (reducedLength_continuousOn hL hDifferential p).comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun q _ ↦ ⟨mem_univ q, hItime hx.2⟩)
    · intro q hq
      obtain ⟨B, _, hB⟩ := hsupports (q, x.2) (hUI ⟨hq, hx.2⟩)
      have hdom : ∀ᶠ w : M × ℝ in 𝓝 (q, x.2),
          reducedLength F T p w.1 w.2 ≤ B.representative w :=
        Filter.eventually_of_mem (B.neighborhood_open.mem_nhds B.center_mem) B.dominates
      exact ⟨fun q' ↦ B.representative (q', x.2),
        B.representative_space_smooth.mdifferentiableAt (by simp), B.touches,
        (continuous_id.prodMk continuous_const).continuousAt hdom, hB⟩
    · intro q hq
      apply hεU
      simpa only [Metric.mem_eball, edist_comm] using
        (show edist z.1 q < (r : ℝ≥0∞) + r + r from hq).trans hsum
    · change edist z.1 x.1 < (r : ℝ≥0∞)
      exact Metric.mem_eball'.mp hx.1
    · change edist z.1 y.1 < (r : ℝ≥0∞)
      exact Metric.mem_eball'.mp hy.1
  have htime : LipschitzOnWith D (fun s ↦ reducedLength F T p y.1 s) (Ioo a b) := by
    apply reducedLength_time_lipschitzOnWith hL hDifferential (convex_Ioo a b) hItime
    intro s hs
    obtain ⟨B, hB, _⟩ := hsupports (y.1, s) (hUI ⟨hsmallU hy.1, hs⟩)
    exact ⟨B, hB⟩
  calc
    edist (reducedLength F T p x.1 x.2) (reducedLength F T p y.1 y.2) ≤
        edist (reducedLength F T p x.1 x.2) (reducedLength F T p y.1 x.2) +
          edist (reducedLength F T p y.1 x.2) (reducedLength F T p y.1 y.2) :=
      edist_triangle _ _ _
    _ ≤ (C : ℝ≥0∞) * edist x.1 y.1 + (D : ℝ≥0∞) * edist x.2 y.2 :=
      add_le_add hspatial (htime hx.2 hy.2)
    _ ≤ (C : ℝ≥0∞) * edist x y + (D : ℝ≥0∞) * edist x y := by
      rw [Prod.edist_eq]
      exact add_le_add (mul_le_mul_right (le_max_left _ _) _)
        (mul_le_mul_right (le_max_right _ _) _)
    _ = ((C + D : ℝ≥0) : ℝ≥0∞) * edist x y := by
      rw [ENNReal.coe_add, add_mul]

end PoincareConjecture.M10
