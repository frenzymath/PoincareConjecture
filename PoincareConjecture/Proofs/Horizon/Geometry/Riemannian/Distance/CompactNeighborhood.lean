import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactMetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {X M : Type*}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [IsManifold (𝓡 n) ∞ X]
  [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem exists_local_image_distance_bound
    (g : RiemannianMetric n X) (gseq : ℕ → RiemannianMetric n X)
    (gM : ℕ → RiemannianMetric n M) (A : ℕ → X → M)
    (hA : ∀ᶠ k in atTop, ContMDiff (𝓡 n) (𝓡 n) ∞ (A k))
    (hmetric : ∀ᶠ k in atTop, ∀ x v w,
      (gseq k).inner x v w = (gM k).inner (A k x)
        (mfderiv (𝓡 n) (𝓡 n) (A k) x v) (mfderiv (𝓡 n) (𝓡 n) (A k) x w))
    (p : X) (c : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (hp : p ∈ c.source)
    (hc : IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ c.symm c.target)
    (hlim : ∀ C, IsCompact C → C ⊆ c.target →
      TendstoUniformlyOn (fun k => (gseq k).pullbackCoefficients c.symm)
        (g.pullbackCoefficients c.symm) atTop C) :
    ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∀ᶠ k in atTop, ∀ x ∈ W, ((gM k).edist (A k x) (A k p)).toReal ≤ D := by
  let E := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (c.open_target.mem_nhds (c.map_source hp))
  let C := Metric.closedBall (c p) (r / 2)
  have hC : IsCompact C := isCompact_closedBall _ _
  have hCt : C ⊆ c.target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrsub
  have hcont : ContinuousOn (g.pullbackCoefficients c.symm) C := by
    intro x hx
    exact (g.contDiffAt_pullbackCoefficients (hc ⟨x, hCt hx⟩).contMDiffAt).continuousAt.continuousWithinAt
  obtain ⟨b, hb⟩ := hC.exists_bound_of_continuousOn hcont
  let B := |b| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound : ∀ᶠ k in atTop, ∀ x ∈ C,
      ‖(gseq k).pullbackCoefficients c.symm x‖ ≤ B := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hlim C hC hCt) 1 zero_lt_one]
      with k hk x hx
    have he : ‖(gseq k).pullbackCoefficients c.symm x - g.pullbackCoefficients c.symm x‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hk x hx
    calc
      _ ≤ ‖(gseq k).pullbackCoefficients c.symm x - g.pullbackCoefficients c.symm x‖ +
          ‖g.pullbackCoefficients c.symm x‖ := norm_le_norm_sub_add _ _
      _ ≤ B := by linarith [hb x hx, le_abs_self b]
  let W := c.source ∩ c ⁻¹' Metric.ball (c p) (r / 2)
  refine ⟨W, c.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨hp, Metric.mem_ball_self (by positivity)⟩,
    Real.sqrt B * (r / 2), mul_nonneg (Real.sqrt_nonneg _) (by positivity), ?_⟩
  filter_upwards [hA, hmetric, hbound] with k hkA hkm hkb x hx
  have hcs : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c.symm (Metric.ball (c p) (r / 2)) := by
    intro y hy
    exact (hc ⟨y, hCt (Metric.ball_subset_closedBall hy)⟩).contMDiffAt.contMDiffWithinAt
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (A k ∘ c.symm) (Metric.ball (c p) (r / 2)) :=
    hkA.comp_contMDiffOn hcs
  have hupper : ∀ y ∈ Metric.ball (c p) (r / 2), ∀ v : E,
      (gM k).pullbackCoefficients (A k ∘ c.symm) y v v ≤ B * ‖v‖ ^ 2 := by
    intro y hy v
    have hcy := (hc ⟨y, hCt (Metric.ball_subset_closedBall hy)⟩).contMDiffAt
    have hcoeff : (gM k).pullbackCoefficients (A k ∘ c.symm) y v v =
        (gseq k).pullbackCoefficients c.symm y v v := by
      simp only [pullbackCoefficients, mfderiv_comp y
        (hkA.mdifferentiable (by simp) (c.symm y)) (hcy.mdifferentiableAt (by simp)),
        ContinuousLinearMap.comp_apply, Function.comp_apply]
      exact (hkm _ _ _).symm
    rw [hcoeff]
    calc
      _ ≤ |(gseq k).pullbackCoefficients c.symm y v v| := le_abs_self _
      _ ≤ ‖(gseq k).pullbackCoefficients c.symm y‖ * ‖v‖ * ‖v‖ := by
        simpa only [Real.norm_eq_abs] using
          ((gseq k).pullbackCoefficients c.symm y).le_opNorm₂ v v
      _ ≤ B * ‖v‖ ^ 2 := by
        simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_right
          (hkb y (Metric.ball_subset_closedBall hy)) (mul_nonneg (norm_nonneg v) (norm_nonneg v))
  have hdist := (gM k).toReal_edist_le_of_pullback_upper Metric.isOpen_ball
    (convex_ball _ _) he hB.le hupper hx.2 (Metric.mem_ball_self (by positivity))
  simp only [Function.comp_apply, c.left_inv hx.1, c.left_inv hp] at hdist
  exact hdist.trans (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hx.2).le (Real.sqrt_nonneg _))

theorem exists_open_uniform_image_distance_bound
    (g : RiemannianMetric n X) (gseq : ℕ → RiemannianMetric n X)
    (gM : ℕ → RiemannianMetric n M) (A : ℕ → X → M) (q : ℕ → M)
    {K : Set X} (hK : IsCompact K)
    (hA : ∀ᶠ k in atTop, ContMDiff (𝓡 n) (𝓡 n) ∞ (A k))
    (hmetric : ∀ᶠ k in atTop, ∀ x v w,
      (gseq k).inner x v w = (gM k).inner (A k x)
        (mfderiv (𝓡 n) (𝓡 n) (A k) x v) (mfderiv (𝓡 n) (𝓡 n) (A k) x w))
    (hcharts : ∀ p ∈ K, ∃ c : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)),
      p ∈ c.source ∧ IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ c.symm c.target ∧
      ∀ C, IsCompact C → C ⊆ c.target →
        TendstoUniformlyOn (fun k => (gseq k).pullbackCoefficients c.symm)
          (g.pullbackCoefficients c.symm) atTop C)
    {D : ℝ} (hbase : ∀ᶠ k in atTop, ∀ x ∈ K, ((gM k).edist (A k x) (q k)).toReal ≤ D) :
    ∃ W : Set X, IsOpen W ∧ K ⊆ W ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ k in atTop, ∀ x ∈ W, ((gM k).edist (A k x) (q k)).toReal ≤ C := by
  classical
  have hlocal (p : K) : ∃ W : Set X, IsOpen W ∧ (p : X) ∈ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ x ∈ W,
        ((gM k).edist (A k x) (A k p)).toReal ≤ C := by
    obtain ⟨c, hpc, hc, hlim⟩ := hcharts p p.property
    exact exists_local_image_distance_bound g gseq gM A hA hmetric p c hpc hc hlim
  choose W hW hp C hC hbound using hlocal
  obtain ⟨s, hs⟩ := hK.elim_nhds_subcover' (fun p hp => W ⟨p, hp⟩)
    (fun p hpK => (hW ⟨p, hpK⟩).mem_nhds (hp ⟨p, hpK⟩))
  let U := ⋃ p ∈ s, W p
  let C₀ := ∑ p ∈ s, C p
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun p _ => hC p
  refine ⟨U, isOpen_iUnion fun p => isOpen_iUnion fun _ => hW p, hs,
    C₀ + |D| + 1, by positivity, ?_⟩
  have hall := (Filter.eventually_all_finite s.finite_toSet).mpr
    (fun p (_ : p ∈ s) => hbound p)
  filter_upwards [hall, hbase] with k hk hkb x hx
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
  have hCp : C p ≤ C₀ := Finset.single_le_sum (fun p _ => hC p) hp
  have htriangle := (gM k).toReal_edist_triangle (A k x) (A k p) (q k)
  linarith [hk p hp x hxp, hkb p p.property, le_abs_self D]

end PoincareConjecture.RiemannianMetric
