import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.MinimizingGeodesic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem exists_precompact_ball_subset_open (g : RiemannianMetric 3 M)
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∃ R : ℝ, 0 < R ∧ IsCompact (closure (g.ball x R)) ∧
      closure (g.ball x R) ⊆ U := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin 3)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨c, hc, hball⟩ := setOfPred_riemannianEDist_lt_subset_nhds
    (𝓡 3) (mem_interior_iff_mem_nhds.mp hxK)
  have hballK : g.ball x (c : ℝ) ⊆ K := by
    simpa only [RiemannianMetric.ball, RiemannianMetric.edist,
      ENNReal.ofReal_coe_nnreal] using hball
  have hclosure : closure (g.ball x (c : ℝ)) ⊆ K :=
    closure_minimal hballK hK.isClosed
  exact ⟨c, hc, hK.of_isClosed_subset isClosed_closure hclosure, hclosure.trans hKU⟩

private theorem exists_intrinsic_ball_buffer (g : RiemannianMetric 3 M)
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ IsOpen (g.ball x r) ∧ x ∈ g.ball x r ∧ g.ball x r ⊆ U ∧
      (∀ y ∈ g.ball x r, IsCompact (closure (g.ball y (2 * r))) ∧
        g.ball y (2 * r) ⊆ U) ∧
      ∀ y ∈ g.ball x r, ∀ z ∈ g.ball x r,
        intrinsicEDist g U y z = g.edist y z ∧
          g.edist y z < ENNReal.ofReal (2 * r) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin 3)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  obtain ⟨R, hR, hcompact, hRsub⟩ := exists_precompact_ball_subset_open g hU hx
  let r := R / 4
  have hr : 0 < r := div_pos hR (by norm_num)
  have h2r : 0 < 2 * r := by positivity
  have h3rR : 3 * r < R := by dsimp [r]; linarith
  have hcontain (y : M) (hy : y ∈ g.ball x r) :
      g.ball y (2 * r) ⊆ g.ball x R := by
    intro w hw
    change edist x w < ENNReal.ofReal R
    calc
      edist x w ≤ edist x y + edist y w := edist_triangle x y w
      _ < ENNReal.ofReal r + ENNReal.ofReal (2 * r) := ENNReal.add_lt_add hy hw
      _ = ENNReal.ofReal (3 * r) := by
        rw [← ENNReal.ofReal_add hr.le h2r.le]
        congr 1
        ring
      _ < ENNReal.ofReal R := (ENNReal.ofReal_lt_ofReal_iff hR).mpr h3rR
  have hWopen : IsOpen (g.ball x r) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hxW : x ∈ g.ball x r := by
    change edist x x < ENNReal.ofReal r
    simpa only [edist_self] using ENNReal.ofReal_pos.mpr hr
  have hWU : g.ball x r ⊆ U := by
    intro y hy
    apply hRsub
    apply subset_closure
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (by dsimp [r]; linarith))
  refine ⟨r, hr, hWopen, hxW, hWU, ?_, ?_⟩
  · intro y hy
    exact ⟨hcompact.of_isClosed_subset isClosed_closure (closure_mono (hcontain y hy)),
      fun z hz => hRsub (subset_closure (hcontain y hy hz))⟩
  intro y hy z hz
  have hdyz : g.edist y z < ENNReal.ofReal (2 * r) := by
    have hyx : edist y x < ENNReal.ofReal r := by
      change edist x y < ENNReal.ofReal r at hy
      simpa only [edist_comm] using hy
    calc
      g.edist y z ≤ edist y x + edist x z := edist_triangle y x z
      _ < ENNReal.ofReal r + ENNReal.ofReal r :=
        ENNReal.add_lt_add hyx hz
      _ = ENNReal.ofReal (2 * r) := by
        rw [← ENNReal.ofReal_add hr.le hr.le]
        congr 1
        ring
  refine ⟨?_, hdyz⟩
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro l hl
    obtain ⟨α, hα0, hα1, hα, hαlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt (lt_min hl hdyz)
    have hαball : MapsTo α (Icc (0 : ℝ) 1) (g.ball y (2 * r)) := by
      simpa only [hα0] using g.mapsTo_ball_of_pathELength_lt hα
        (hαlen.trans_le (min_le_right _ _))
    have hαU : MapsTo α (Icc (0 : ℝ) 1) U :=
      fun t ht => hRsub (subset_closure (hcontain y hy (hαball ht)))
    have hinf := intrinsicEDist_le_pathELength g zero_le_one hα hαU
    rw [hα0, hα1] at hinf
    exact hinf.trans (hαlen.trans_le (min_le_left _ _)).le
  · rw [intrinsicEDist]
    apply le_sInf
    rintro l ⟨α, hα, hα0, hα1, _, rfl⟩
    exact Manifold.riemannianEDist_le_pathELength hα hα0 hα1 zero_le_one

theorem exists_open_intrinsic_distance_eq (g : RiemannianMetric 3 M)
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∀ y ∈ W, ∀ z ∈ W, intrinsicEDist g U y z = g.edist y z := by
  obtain ⟨r, _, hWopen, hxW, hWU, _, hpair⟩ := exists_intrinsic_ball_buffer g hU hx
  exact ⟨g.ball x r, hWopen, hxW, hWU, fun y hy z hz => (hpair y hy z hz).1⟩

theorem exists_open_intrinsic_minimizing_paths (g : RiemannianMetric 3 M)
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∀ y ∈ W, ∀ z ∈ W, ∃ γ : ℝ → M,
        γ 0 = y ∧ γ 1 = z ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
        MapsTo γ (Icc (0 : ℝ) 1) U ∧
        g.pathELength γ 0 1 = intrinsicEDist g U y z := by
  obtain ⟨r, hr, hWopen, hxW, hWU, hbuffer, hpair⟩ :=
    exists_intrinsic_ball_buffer g hU hx
  refine ⟨g.ball x r, hWopen, hxW, hWU, ?_⟩
  intro y hy z hz
  obtain ⟨hcompactY, hballU⟩ := hbuffer y hy
  obtain ⟨hdist, hdyz⟩ := hpair y hy z hz
  have h2r : 0 < 2 * r := by positivity
  obtain ⟨delta, hdelta, γ, hgeo, hγ0, hγ1, hsegment⟩ :=
    g.exists_minimizing_geodesic_of_precompact_ball y z h2r hcompactY hdyz
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-delta) (1 + delta) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hγU : MapsTo γ (Icc (0 : ℝ) 1) U := by
    intro t ht
    apply hballU
    have h := hsegment 0 (by norm_num) t ht
    rw [hγ0, zero_sub, abs_neg, abs_of_nonneg ht.1] at h
    have ht1 : ENNReal.ofReal t ≤ 1 := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ht.2
    change g.edist y (γ t) < ENNReal.ofReal (2 * r)
    calc
      g.edist y (γ t) = ENNReal.ofReal t * g.edist y z := h
      _ ≤ 1 * g.edist y z := mul_le_mul_left ht1 _
      _ = g.edist y z := one_mul _
      _ < ENNReal.ofReal (2 * r) := hdyz
  refine ⟨γ, hγ0, hγ1, hgeo.contMDiffOn.mono hI, hγU, ?_⟩
  rw [hdist]
  exact hgeo.pathELength_eq_of_edist_segment hdelta hγ0 hsegment

end PoincareConjecture.M28
