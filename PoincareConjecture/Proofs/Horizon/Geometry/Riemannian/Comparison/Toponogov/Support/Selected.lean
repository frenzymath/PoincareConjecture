import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Tail

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

omit [T3Space M] [ConnectedSpace M] in
private theorem geodesic_open_interval {g : RiemannianMetric n M} {γ : ℝ → M}
    (hγ : g.IsGeodesicOn γ (Icc 0 1)) :
    ∃ ε : ℝ, 0 < ε ∧ g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) := by
  obtain ⟨U, hU, h0U, hγU⟩ := hγ.exists_open_nhds (by simp : (0 : ℝ) ∈ Icc 0 1)
  obtain ⟨V, hV, h1V, hγV⟩ := hγ.exists_open_nhds (by simp : (1 : ℝ) ∈ Icc 0 1)
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  obtain ⟨s, hs, hsV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h1V)
  refine ⟨min r s, lt_min hr hs, fun t ht => ?_⟩
  by_cases h0 : t < 0
  · apply hγU t (hrU ?_)
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg h0]
    linarith [min_le_left r s, ht.1]
  by_cases h1 : 1 < t
  · apply hγV t (hsV ?_)
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr h1)]
    linarith [min_le_right r s, ht.2]
  exact hγ t ⟨le_of_not_gt h0, le_of_not_gt h1⟩

theorem exists_radial_support_on_minimizing_segment
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {γ : ℝ → M}
    (hγ : g.IsGeodesicOn γ (Icc 0 1)) (hneq : γ 0 ≠ γ 1)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1)) :
    ∃ (R : ℝ) (e : EuclideanSpace ℝ (Fin n) → M)
      (v : EuclideanSpace ℝ (Fin n))
      (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M),
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R) ∧
      (∀ a b, g.pullbackCoefficients e 0 a b = inner ℝ a b) ∧
      (∀ w ∈ Metric.ball 0 R,
        g.IsGeodesicOn (fun r : ℝ => e (r • w))
          {r : ℝ | r • w ∈ Metric.ball 0 R}) ∧
      v ∈ Metric.ball 0 R ∧ v ≠ 0 ∧ e v = γ 1 ∧
      ‖v‖ = (g.edist (γ 0) (γ 1)).toReal / 2 ∧
      ((fun r : ℝ => e (r • v)) =ᶠ[𝓝 1] (fun r => γ (r / 2 + 1 / 2))) ∧
      v ∈ B.source ∧ EqOn e B B.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ B.symm B.target ∧
      (∀ y ∈ B.target,
        (g.edist (γ 0) y).toReal ≤
          (g.edist (γ 0) (γ 1)).toReal / 2 + ‖B.symm y‖) := by
  obtain ⟨ε, hε, hγopen⟩ := geodesic_open_interval hγ
  let d := (g.edist (γ 0) (γ 1)).toReal
  let R := d + 1
  have hd : 0 < d := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    exact ENNReal.toReal_pos (edist_pos.mpr hneq).ne' (g.edist_ne_top _ _)
  have hR : 0 < R := by dsimp [R]; linarith
  obtain ⟨L, e, hL, he, he0, hed, hradial⟩ :=
    g.exists_orthonormal_radial_exponential_of_metricComplete hcomplete (γ (1 / 2)) hR
  have hgeo := fun w hw => (hradial w hw).1
  obtain ⟨v, hv, hvnorm, hx, hsplit, hmatch⟩ :=
    g.exists_shifted_radial_vector_of_le_half hε hγopen rfl rfl hmin
      (by norm_num : (0 : ℝ) < 1 / 2) le_rfl
      (by dsimp [R, d]; linarith) L e hL he0 hed hgeo
  have hvnorm' : ‖v‖ = d / 2 := by
    convert! hvnorm using 1
    ring
  have hv0 : v ≠ 0 := norm_pos_iff.mp (by rw [hvnorm']; positivity)
  have heorigin := he.contMDiffAt (Metric.isOpen_ball.mem_nhds
    (show (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 R by simpa using hR))
  have hnorm := g.pullbackCoefficients_zero_of_orthonormal (γ (1 / 2))
    heorigin he0 hed hL
  have hinit := isInvertible_mfderiv_zero_of_chart_derivative
    (heorigin.mdifferentiableAt (by simp)) he0 hed
  have hback : e ((-1 : ℝ) • v) = γ 0 := by
    have h := (hmatch (-1) (by norm_num)).self_of_nhds
    norm_num at h
    simpa only [neg_one_smul] using h
  have hminback : g.edist (e ((-1 : ℝ) • v)) (e v) = ENNReal.ofReal ((1 + 1) * ‖v‖) := by
    rw [hback, hx, hvnorm']
    have heq : (1 + 1 : ℝ) * (d / 2) = d := by ring
    rw [heq, ENNReal.ofReal_toReal (g.edist_ne_top _ _)]
  have hi := g.isInvertible_mfderiv_of_minimizing_backward_extension_of_le_one
    D he hinit hgeo (fun w hw t ht => ((hradial w hw).2 t ht).1)
    hv hv0 (by norm_num : (0 : ℝ) < 1) le_rfl hminback
  obtain ⟨B, hvB, hBU, heB, hB, hBi, hzero, hnormB⟩ :=
    exists_smooth_radial_inverse_branch Metric.isOpen_ball he hv hv0 hi
  refine ⟨R, e, v, B, he, hnorm, hgeo, hv, hv0, hx, hvnorm', ?_, hvB, heB, hBi, ?_⟩
  · convert! hmatch 1 (by norm_num) using 1
    funext r
    congr 1
    ring
  · intro y hy
    have hleft : (g.edist (γ 0) (γ (1 / 2))).toReal = d / 2 := by
      linarith [hsplit]
    apply inverse_branch_distance_majorant g (γ 0) (γ (1 / 2))
      (B := B) (e := e) (R := R) (left := d / 2) ?_ hBU heB hleft hy
    intro w hw
    simpa only [one_smul, ENNReal.ofReal_one, mul_one] using
      ((hradial w hw).2 1 (by simp)).2

end PoincareConjecture.RiemannianMetric
