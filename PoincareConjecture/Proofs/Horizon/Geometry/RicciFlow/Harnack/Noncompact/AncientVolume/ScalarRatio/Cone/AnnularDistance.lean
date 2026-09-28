import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.LimitTransport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactEnergy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]

omit [T3Space M] [PreconnectedSpace M] in
theorem eventually_normal_chart_tangent_bounds
    (g : ℕ → RiemannianMetric n M)
    (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hconv : TendstoUniformlyOn (fun k => (g k).pullbackCoefficients (Φ k))
      h.euclideanCoefficients atTop K) {C : ℝ} (hC : 1 < C) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v : EuclideanSpace ℝ (Fin n),
      (g k).tangentNorm (Φ k x) (mfderiv (𝓡 n) (𝓡 n) (Φ k) x v) ≤
          C * h.tangentNorm x v ∧
        h.tangentNorm x v ≤
          C * (g k).tangentNorm (Φ k x) (mfderiv (𝓡 n) (𝓡 n) (Φ k) x v) := by
  obtain ⟨c, hc, hlower⟩ := exists_uniform_bilinear_lower_bound hK
    (show ContinuousOn h.euclideanCoefficients K from
      fun x _ => (h.contDiffAt_euclideanCoefficients x).continuousAt.continuousWithinAt)
    (fun x _ v hv => h.pos x v hv)
  let δ := (C - 1) / C
  have hδ : 0 < δ := div_pos (sub_pos.mpr hC) (zero_lt_one.trans hC)
  filter_upwards [(Metric.tendstoUniformlyOn_iff (f := h.euclideanCoefficients)).mp
    hconv (c * δ) (mul_pos hc hδ)] with k hk x hx v
  apply h.tangentNorm_pullback_bounds_of_unit_error (g k) (Φ k) hC
  intro u hu
  have hcoeff : ‖(g k).pullbackCoefficients (Φ k) x - h.euclideanCoefficients x‖ < c * δ := by
    calc
      ‖(g k).pullbackCoefficients (Φ k) x - h.euclideanCoefficients x‖ =
          dist (h.euclideanCoefficients x) ((g k).pullbackCoefficients (Φ k) x) := by
        exact (norm_sub_rev ((g k).pullbackCoefficients (Φ k) x)
          (h.euclideanCoefficients x)).trans
          (dist_eq_norm (h.euclideanCoefficients x)
            ((g k).pullbackCoefficients (Φ k) x)).symm
      _ < c * δ := hk x hx
  have hinner : h.inner x u u ≤ 1 := by
    have hn : 0 ≤ h.inner x u u := by
      by_cases hz : u = 0
      · simp [hz]
      · exact (h.pos x u hz).le
    have hsq := Real.sq_sqrt hn
    change Real.sqrt (h.inner x u u) ≤ 1 at hu
    nlinarith [Real.sqrt_nonneg (h.inner x u u)]
  have hbound := hlower x hx u
  let B := (g k).pullbackCoefficients (Φ k) x - h.euclideanCoefficients x
  have hB : |B u u| ≤ ‖B‖ * ‖u‖ ^ 2 := by
    calc
      |B u u| = ‖B u u‖ := rfl
      _ ≤ ‖B u‖ * ‖u‖ := (B u).le_opNorm u
      _ ≤ (‖B‖ * ‖u‖) * ‖u‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm u) (norm_nonneg u)
      _ = ‖B‖ * ‖u‖ ^ 2 := by ring
  have hlast : ‖B‖ * ‖u‖ ^ 2 ≤ δ := by
    have hmul := mul_le_mul_of_nonneg_right hcoeff.le (sq_nonneg ‖u‖)
    have hmul' := mul_le_mul_of_nonneg_left hbound hδ.le
    have hmul'' := mul_le_mul_of_nonneg_left hinner hδ.le
    change c * ‖u‖ ^ 2 ≤ h.inner x u u at hbound
    nlinarith
  exact hB.trans hlast

omit [T3Space M] [PreconnectedSpace M] in
theorem normal_chart_edist_bounds
    (g : RiemannianMetric n M)
    (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (q : M)
    (Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {S R r C : ℝ} (hr : 0 < r) (hC : 0 < C) (hRS : R ≤ S) (h3r : 3 * r < R)
    (hsource : Φ.source = Metric.ball 0 S) (htarget : Φ.target = g.ball q S)
    (hradial : ∀ x ∈ Metric.ball 0 S, g.edist q (Φ x) = ENNReal.ofReal ‖x‖)
    (hlimitBall : h.ball 0 (3 * r) ⊆ Metric.closedBall 0 R)
    (hnorm : ∀ x ∈ Metric.closedBall 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      g.tangentNorm (Φ x) (mfderiv (𝓡 n) (𝓡 n) Φ x v) ≤ C * h.tangentNorm x v ∧
        h.tangentNorm x v ≤ C * g.tangentNorm (Φ x) (mfderiv (𝓡 n) (𝓡 n) Φ x v))
    (hstrict : R < S)
    {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ Metric.ball 0 r ∩ h.ball 0 r) (hy : y ∈ Metric.ball 0 r ∩ h.ball 0 r) :
    g.edist (Φ x) (Φ y) ≤ ENNReal.ofReal C * h.edist x y ∧
      h.edist x y ≤ ENNReal.ofReal C * g.edist (Φ x) (Φ y) := by
  have hRsource : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ Φ.source := by
    rw [hsource]
    exact closedBall_subset_ball hstrict
  have he : Φ.toOpenPartialHomeomorph.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨Φ.mdifferentiableOn (by simp), Φ.symm.mdifferentiableOn (by simp)⟩
  have hinv (z : M) (hz : z ∈ g.ball q (3 * r)) :
      z ∈ Φ.target ∧ Φ.symm z ∈ Metric.closedBall 0 R := by
    have hzS : z ∈ Φ.target := by
      rw [htarget]
      exact hz.trans_le (ENNReal.ofReal_le_ofReal (h3r.le.trans hRS))
    have hrad := hradial (Φ.symm z) (by rw [← hsource]; exact Φ.map_target hzS)
    have hright : Φ (Φ.symm z) = z := Φ.right_inv hzS
    rw [hright] at hrad
    have hn : ‖Φ.symm z‖ < 3 * r := by
      change g.edist q z < ENNReal.ofReal (3 * r) at hz
      rw [hrad] at hz
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 3 * r)).mp hz
    refine ⟨hzS, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hn.trans h3r).le
  have hback : ∀ z ∈ g.ball q (3 * r), ∀ v : TangentSpace (𝓡 n) z,
      h.tangentNorm (Φ.symm z) (mfderiv (𝓡 n) (𝓡 n) Φ.symm z v) ≤ C * g.tangentNorm z v := by
    intro z hz v
    have hright : mfderiv (𝓡 n) (𝓡 n) Φ (Φ.symm z)
        (mfderiv (𝓡 n) (𝓡 n) Φ.symm z v) = v :=
      congrArg (fun A => A v) (he.comp_symm_deriv (hinv z hz).1)
    have hb := (hnorm (Φ.symm z) (hinv z hz).2
      (mfderiv (𝓡 n) (𝓡 n) Φ.symm z v)).2
    change h.tangentNorm (Φ.symm z) _ ≤
      C * g.tangentNorm (Φ (Φ.symm z)) _ at hb
    have hrightPoint : Φ (Φ.symm z) = z := Φ.right_inv (hinv z hz).1
    rw [hright, hrightPoint] at hb
    exact hb
  have hsmall (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball 0 r) :
      z ∈ Φ.source ∧ Φ z ∈ g.ball q r := by
    have hrS : r < S := by linarith
    have hzS : z ∈ Metric.ball 0 S := (Metric.ball_subset_ball hrS.le) hz
    refine ⟨by rwa [hsource], ?_⟩
    change g.edist q (Φ z) < ENNReal.ofReal r
    rw [hradial z hzS]
    apply ENNReal.ofReal_lt_ofReal_iff hr |>.mpr
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  constructor
  · exact h.edist_image_le_mul_edist_of_tangentNorm_le_on_ball g Φ 0 hr hC
      (fun z hz => (Φ.contMDiffOn.contMDiffAt
        (Φ.open_source.mem_nhds (hRsource (hlimitBall hz)))).of_le (by simp))
      (fun z hz v => (hnorm z (hlimitBall hz) v).1) hx.2 hy.2
  · have hh := g.edist_image_le_mul_edist_of_tangentNorm_le_on_ball h Φ.symm q hr hC
      (fun z hz => (Φ.symm.contMDiffOn.contMDiffAt
        (Φ.open_target.mem_nhds (hinv z hz).1)).of_le (by simp)) hback
      (hsmall x hx.1).2 (hsmall y hy.1).2
    have hxback : Φ.symm (Φ x) = x := Φ.left_inv (hsmall x hx.1).1
    have hyback : Φ.symm (Φ y) = y := Φ.left_inv (hsmall y hy.1).1
    rwa [hxback, hyback] at hh





theorem exists_uniform_distance_limit_of_normal_chart_coefficients
    (g : ℕ → RiemannianMetric n M)
    (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (q : ℕ → M)
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {S : ℝ} (hS : 0 < S)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (htarget : ∀ k, (Φ k).target = (g k).ball (q k) S)
    (hradial : ∀ k x, x ∈ Metric.ball 0 S →
      (g k).edist (q k) (Φ k x) = ENNReal.ofReal ‖x‖)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V) (hzero : 0 ∈ V)
    (hconv : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ V →
      TendstoUniformlyOn (fun k => (g k).pullbackCoefficients (Φ k))
        h.euclideanCoefficients atTop K) :
    ∃ W : Set (EuclideanSpace ℝ (Fin n)), IsOpen W ∧ 0 ∈ W ∧ W ⊆ V ∧
      W ⊆ Metric.ball 0 S ∧
      TendstoUniformlyOn
        (fun k (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
          ((g k).edist (Φ k z.1) (Φ k z.2)).toReal)
        (fun z => (h.edist z.1 z.2).toReal) atTop (W ×ˢ W) := by
  obtain ⟨ρ, hρ, hρV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hzero)
  let R := min ρ S / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRρ : R < ρ := by
    have := min_le_left ρ S
    dsimp [R]
    linarith
  have hRS : R < S := by
    have := min_le_right ρ S
    dsimp [R]
    linarith
  have hKV : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ V :=
    (closedBall_subset_ball hRρ).trans hρV
  have hsmall : ∃ a : ℝ, 0 < a ∧ h.ball 0 a ⊆ Metric.closedBall 0 R := by
    have hnb : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R ∈ 𝓝 0 :=
      Metric.ball_mem_nhds _ hR
    obtain ⟨a, ha, hsub⟩ := (@Metric.mem_nhds_iff _
      h.toMetricSpace.toPseudoMetricSpace 0 _).mp hnb
    refine ⟨a, ha, ?_⟩
    rw [h.toMetricSpace_ball] at hsub
    exact hsub.trans ball_subset_closedBall
  obtain ⟨a, ha, haball⟩ := hsmall
  let r := min a R / 6
  have hr : 0 < r := by dsimp [r]; positivity
  have h3rR : 3 * r < R := by
    have := min_le_right a R
    dsimp [r]
    linarith
  have h3ra : 3 * r ≤ a := by
    have := min_le_left a R
    dsimp [r]
    linarith
  have hlimitBall : h.ball 0 (3 * r) ⊆ Metric.closedBall 0 R := by
    intro x hx
    exact haball (hx.trans_le (ENNReal.ofReal_le_ofReal h3ra))
  let W := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ∩ h.ball 0 r
  have hWo : IsOpen W := by
    apply isOpen_ball.inter
    rw [← h.toMetricSpace_ball]
    exact @isOpen_ball _ h.toMetricSpace.toPseudoMetricSpace 0 r
  have hW0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ W := by
    refine ⟨Metric.mem_ball_self hr, ?_⟩
    rw [← h.toMetricSpace_ball]
    exact @Metric.mem_ball_self _ h.toMetricSpace.toPseudoMetricSpace 0 r hr
  have hWr : W ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    exact ball_subset_closedBall ((Metric.ball_subset_ball (by linarith : r ≤ R)) hx.1)
  refine ⟨W, hWo, hW0, hWr.trans hKV,
    hWr.trans (closedBall_subset_ball hRS), ?_⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let C := 1 + min (1 / 2) (ε / (4 * r))
  have hC : 1 < C := by
    have hh : 0 < min (1 / 2 : ℝ) (ε / (4 * r)) := lt_min (by norm_num) (by positivity)
    dsimp [C]
    linarith
  have herror : (C - 1) * (2 * r) < ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * r)).mp
      (min_le_right (1 / 2 : ℝ) (ε / (4 * r)))
    dsimp [C]
    nlinarith
  filter_upwards [eventually_normal_chart_tangent_bounds g h Φ (isCompact_closedBall _ _)
    (hconv _ (isCompact_closedBall _ _) hKV) hC] with k hk z hz
  obtain ⟨hforward, hback⟩ := normal_chart_edist_bounds (g k) h (q k) (Φ k)
    hr (zero_lt_one.trans hC) hRS.le h3rR (hsource k) (htarget k)
    (hradial k) hlimitBall hk hRS hz.1 hz.2
  have hforward' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (h.edist_ne_top z.1 z.2)) hforward
  have hback' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ((g k).edist_ne_top (Φ k z.1) (Φ k z.2))) hback
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (zero_lt_one.trans hC).le] at hforward' hback'
  have hlimit : (h.edist z.1 z.2).toReal < 2 * r := by
    have hx : (h.edist 0 z.1).toReal < r :=
      (ENNReal.lt_ofReal_iff_toReal_lt (h.edist_ne_top 0 z.1)).mp hz.1.2
    have hy : (h.edist 0 z.2).toReal < r :=
      (ENNReal.lt_ofReal_iff_toReal_lt (h.edist_ne_top 0 z.2)).mp hz.2.2
    have ht := @dist_triangle _ h.toMetricSpace.toPseudoMetricSpace z.1 0 z.2
    rw [@dist_comm _ h.toMetricSpace.toPseudoMetricSpace z.1 0] at ht
    change (h.edist z.1 z.2).toReal ≤ (h.edist 0 z.1).toReal + (h.edist 0 z.2).toReal at ht
    linarith
  change |(h.edist z.1 z.2).toReal - ((g k).edist (Φ k z.1) (Φ k z.2)).toReal| < ε
  have hprod := mul_le_mul_of_nonneg_left hlimit.le (sub_pos.mpr hC).le
  apply abs_lt.mpr
  constructor
  · nlinarith
  · by_cases hh : ((g k).edist (Φ k z.1) (Φ k z.2)).toReal ≤ (h.edist z.1 z.2).toReal
    · have hm := mul_le_mul_of_nonneg_left hh (sub_pos.mpr hC).le
      nlinarith
    · linarith

end PoincareConjecture.RiemannianMetric
