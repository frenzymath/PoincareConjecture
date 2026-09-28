import PoincareConjecture.Proofs.M34.Standard.PathLengthComparison
import PoincareConjecture.Proofs.M34.Standard.MetricComparisonCompleteness
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CompactConfinement










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N] [T3Space M]




theorem edist_image_le_mul_edist_of_tangentNorm_le_on_triple_ball
    (g : RiemannianMetric n M) (h : RiemannianMetric m N) (f : M → N)
    (o : M) {r C : ℝ} (hr : 0 < r) (hC : 0 < C)
    (hf : ContMDiffOn (𝓡 n) (𝓡 m) 1 f (g.ball o (3 * r)))
    (hbound : ∀ z ∈ g.ball o (3 * r), ∀ v : TangentSpace (𝓡 n) z,
      h.tangentNorm (f z) (mfderiv (𝓡 n) (𝓡 m) f z v) ≤ C * g.tangentNorm z v)
    {x y : M} (hx : x ∈ g.ball o r) (hy : y ∈ g.ball o r) :
    h.edist (f x) (f y) ≤ ENNReal.ofReal C * g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := g.comparisonPseudoEMetric
  have hopen : IsOpen (g.ball o (3 * r)) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hxy : g.edist x y < ENNReal.ofReal (2 * r) := by
    calc
      _ ≤ g.edist x o + g.edist o y := Manifold.riemannianEDist_triangle
      _ < ENNReal.ofReal r + ENNReal.ofReal r := ENNReal.add_lt_add
        (by
          change g.comparisonPseudoEMetric.edist x o < _
          rw [g.comparisonPseudoEMetric.edist_comm]
          exact hx) hy
      _ = _ := by rw [← ENNReal.ofReal_add hr.le hr.le]; congr 1; ring
  have hdiv : h.edist (f x) (f y) / ENNReal.ofReal C ≤ g.edist x y := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt (lt_min hb hxy)
    have hγball : MapsTo γ (Icc (0 : ℝ) 1) (g.ball o (3 * r)) := by
      intro u hu
      have hd := g.edist_le_pathELength_of_mem_Icc hγ hu
      rw [hγ0] at hd
      have hxu := hd.trans_lt (hlen.trans_le (min_le_right _ _))
      calc
        g.edist o (γ u) ≤ g.edist o x + g.edist x (γ u) :=
          Manifold.riemannianEDist_triangle
        _ < ENNReal.ofReal r + ENNReal.ofReal (2 * r) := ENNReal.add_lt_add hx hxu
        _ = ENNReal.ofReal (3 * r) := by
          rw [← ENNReal.ofReal_add hr.le (by positivity)]; congr 1; ring
    have hη : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 m) 1 (f ∘ γ) (Icc (0 : ℝ) 1) :=
      hf.comp hγ hγball
    have hlength : h.pathELength (f ∘ γ) 0 1 ≤ ENNReal.ofReal C * g.pathELength γ 0 1 := by
      apply h.pathELength_le_mul_of_speed_le g (f ∘ γ) γ 0 1 hC.le
      intro u hu
      have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
      have hfd := ((hf (γ u) (hγball hu')).contMDiffAt
        (hopen.mem_nhds (hγball hu'))).mdifferentiableAt (by simp)
      have hγd := ((hγ u hu').contMDiffAt
        (Icc_mem_nhds hu.1 hu.2)).mdifferentiableAt (by simp)
      rw [mfderiv_comp_apply u hfd hγd (1 : ℝ)]
      exact hbound (γ u) (hγball hu') _
    have hdist : h.edist (f x) (f y) ≤ h.pathELength (f ∘ γ) 0 1 := by
      simpa only [Function.comp_apply, hγ0, hγ1] using
        h.edist_le_pathELength_of_mem_Icc hη (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
    apply (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top).mpr
    exact (hdist.trans hlength).trans (by
      rw [mul_comm b]
      exact mul_le_mul' le_rfl (hlen.le.trans (min_le_left _ _)))
  simpa only [mul_comm] using (ENNReal.div_le_iff
    (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top).mp hdiv




theorem exists_open_edist_image_bound_of_tangentNorm_le
    (g : RiemannianMetric n M) (h : RiemannianMetric m N) (f : M → N)
    {U : Set M} (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 m) 1 f U)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ z ∈ U, ∀ v : TangentSpace (𝓡 n) z,
      h.tangentNorm (f z) (mfderiv (𝓡 n) (𝓡 m) f z v) ≤ C * g.tangentNorm z v)
    {x : M} (hx : x ∈ U) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∀ y ∈ V, ∀ z ∈ V, h.edist (f y) (f z) ≤ ENNReal.ofReal C * g.edist y z := by
  let : PseudoEMetricSpace M := g.comparisonPseudoEMetric
  obtain ⟨ε, hε, hεU⟩ := EMetric.mem_nhds_iff.mp (hU.mem_nhds hx)
  obtain ⟨d, _, hd, hdε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hdpos : 0 < d := ENNReal.ofReal_pos.mp hd
  have hr : 0 < d / 3 := div_pos hdpos (by norm_num)
  have hlarge : g.ball x (3 * (d / 3)) ⊆ U := by
    intro y hy
    apply hεU
    change g.comparisonPseudoEMetric.edist y x < ε
    rw [g.comparisonPseudoEMetric.edist_comm]
    have heq : 3 * (d / 3) = d := by ring
    have hy' : g.edist x y < ENNReal.ofReal d := by
      rw [heq] at hy
      exact hy
    exact hy'.trans hdε
  have hsmall : g.ball x (d / 3) ⊆ g.ball x (3 * (d / 3)) := by
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
  refine ⟨g.ball x (d / 3),
    isOpen_lt (continuous_const.edist continuous_id) continuous_const, ?_,
    hsmall.trans hlarge, ?_⟩
  · change g.comparisonPseudoEMetric.edist x x < ENNReal.ofReal (d / 3)
    rw [g.comparisonPseudoEMetric.edist_self]
    exact ENNReal.ofReal_pos.mpr hr
  · intro y hy z hz
    exact g.edist_image_le_mul_edist_of_tangentNorm_le_on_triple_ball h f x hr hC
      (hf.mono hlarge) (fun w hw => hbound w (hlarge hw)) hy hz

end PoincareConjecture.RiemannianMetric
