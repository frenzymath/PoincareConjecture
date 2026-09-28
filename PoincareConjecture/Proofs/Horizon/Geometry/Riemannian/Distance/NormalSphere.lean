import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Orthonormal
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.NormalBall









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle InnerProductSpace

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]



theorem exists_distance_sphere_homeomorph_radius
    (g : RiemannianMetric n M) (p : M) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      Nonempty ((Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ≃ₜ
        {y : M // (g.edist p y).toReal = r}) := by
  let := g.toMetricSpace
  let E := EuclideanSpace ℝ (Fin n)
  obtain ⟨e, h0, he0, he, he', hgauss, _⟩ := g.exists_exponential_chart_gauss p
  obtain ⟨a, ha, hsource, hdist⟩ :=
    g.exists_tangentBall_edist_eq_of_gauss p e h0 he0 he he' hgauss
  obtain ⟨L, hL⟩ := g.exists_orthonormal_coordinate_frame p
  have hLn (v : E) : g.tangentNorm p (L v) = ‖v‖ := by
    unfold tangentNorm
    rw [← g.chartCoefficients_center, hL, real_inner_self_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg _)]
  have hnorm : Continuous (fun v : E => g.tangentNorm p v) := by
    unfold tangentNorm
    exact Real.continuous_sqrt.comp
      ((continuous_const.clm_apply continuous_id).clm_apply continuous_id)
  have hV : {v : E | g.tangentNorm p v < a} ∈ 𝓝 0 :=
    (isOpen_lt hnorm continuous_const).mem_nhds (by simpa [tangentNorm] using ha)
  have hU : e '' {v : E | g.tangentNorm p v < a} ∈ 𝓝 p := by
    simpa only [he0] using e.image_mem_nhds h0 hV
  obtain ⟨b, hb, hcover⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro r hr hrR
  have hra : r < a := hrR.trans_le (min_le_left _ _)
  have hrb : r < b := hrR.trans_le (min_le_right _ _)
  let S := Metric.sphere (0 : E) 1
  let T := {y : M // (g.edist p y).toReal = r}
  have hunit (θ : S) : ‖θ.val‖ = 1 := by
    simpa only [S, Metric.mem_sphere, dist_zero_right] using θ.property
  have hradial (θ : S) : g.tangentNorm p (L (r • θ.val)) = r := by
    rw [hLn, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hunit, mul_one]
  have hradialsource (θ : S) : L (r • θ.val) ∈ e.source :=
    hsource (by change g.tangentNorm p (L (r • θ.val)) < a; rw [hradial]; exact hra)
  have hradialdist (θ : S) : (g.edist p (e (L (r • θ.val)))).toReal = r := by
    rw [hdist _ (by rw [hradial]; exact hra), hradial, ENNReal.toReal_ofReal hr.le]
  have himage (y : T) : y.val ∈ e '' {v : E | g.tangentNorm p v < a} := by
    apply hcover
    change dist y.val p < b
    rw [dist_comm, g.toMetricSpace_dist, y.property]
    exact hrb
  have htarget (y : T) : y.val ∈ e.target := by
    obtain ⟨v, hv, heq⟩ := himage y
    exact heq ▸ e.map_source (hsource hv)
  have hinversenorm (y : T) : ‖L.symm (e.symm y.val)‖ = r := by
    obtain ⟨v, hv, heq⟩ := himage y
    have hd : g.tangentNorm p v = r := by
      have h := y.property
      rw [← heq, hdist v hv] at h
      have hn : 0 ≤ g.tangentNorm p v := Real.sqrt_nonneg _
      rwa [ENNReal.toReal_ofReal hn] at h
    rw [← hLn, L.apply_symm_apply, ← heq, e.left_inv (hsource hv), hd]
  let forward : S → T := fun θ => ⟨e (L (r • θ.val)), hradialdist θ⟩
  let backward : T → S := fun y => ⟨r⁻¹ • L.symm (e.symm y.val), by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), hinversenorm, inv_mul_cancel₀ hr.ne']⟩
  have hleft : Function.LeftInverse backward forward := by
    intro θ
    apply Subtype.ext
    change r⁻¹ • L.symm (e.symm (e (L (r • θ.val)))) = θ.val
    rw [e.left_inv (hradialsource θ), L.symm_apply_apply, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  have hright : Function.RightInverse backward forward := by
    intro y
    apply Subtype.ext
    change e (L (r • (r⁻¹ • L.symm (e.symm y.val)))) = y.val
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, L.apply_symm_apply,
      e.right_inv (htarget y)]
  have hforward : Continuous forward := by
    apply Continuous.subtype_mk
    exact e.continuousOn.comp_continuous
      (L.continuous.comp (continuous_subtype_val.const_smul r)) hradialsource
  have hbackward : Continuous backward := by
    apply Continuous.subtype_mk
    exact (L.symm.continuous.comp
      (e.symm.continuousOn.comp_continuous continuous_subtype_val htarget)).const_smul r⁻¹
  exact ⟨{
    toFun := forward
    invFun := backward
    left_inv := hleft
    right_inv := hright
    continuous_toFun := hforward
    continuous_invFun := hbackward
  }⟩


theorem exists_small_distance_sphere_homeomorph
    (g : RiemannianMetric n M) (p : M) :
    ∃ r : ℝ, 0 < r ∧
      Nonempty ((Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ≃ₜ
        {y : M // (g.edist p y).toReal = r}) := by
  obtain ⟨R, hR, h⟩ := g.exists_distance_sphere_homeomorph_radius p
  exact ⟨R / 2, half_pos hR, h _ (half_pos hR) (half_lt_self hR)⟩

end PoincareConjecture.RiemannianMetric
