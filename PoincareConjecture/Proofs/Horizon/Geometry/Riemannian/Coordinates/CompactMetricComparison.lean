import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactFamily
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareConjecture
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem eventually_inner_le_near_chart
    (gseq : ℕ → RiemannianMetric n M) (g : RiemannianMetric n M)
    (p : M) (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hp : p ∈ c.source)
    (hc : IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ c.symm c.target)
    (hmetric : ∀ C, IsCompact C → C ⊆ c.target →
      TendstoUniformlyOn (fun k => (gseq k).pullbackCoefficients c.symm)
        (g.pullbackCoefficients c.symm) atTop C) :
    ∃ N ∈ 𝓝 p, ∀ᶠ k in atTop, ∀ q ∈ N, ∀ v : TangentSpace (𝓡 n) q,
      (gseq k).inner q v v ≤ 2 * g.inner q v v := by
  let E := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  have hi (x : E) (hx : x ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm x).IsInvertible :=
    ⟨(hc ⟨x, hx⟩).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (c.open_target.mem_nhds (c.map_source hp))
  let C := Metric.closedBall (c p) (r / 2)
  have hC : IsCompact C := isCompact_closedBall _ _
  have hCt : C ⊆ c.target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrsub
  have hcont : ContinuousOn (g.pullbackCoefficients c.symm) C := by
    intro x hx
    exact (g.contDiffAt_pullbackCoefficients
      (hc ⟨x, hCt hx⟩).contMDiffAt).continuousAt.continuousWithinAt
  have hpos : ∀ x ∈ C, ∀ v : E, v ≠ 0 →
      0 < g.pullbackCoefficients c.symm x v v := by
    intro x hx v hv
    apply g.pos
    intro hz
    apply hv
    apply (hi x (hCt hx)).injective
    rw [map_zero]
    exact hz
  obtain ⟨a, ha, hlower⟩ := exists_uniform_bilinear_family_lower_bound hC hcont hpos
  have hconv := (Metric.tendstoUniformlyOn_iff
    (α := E →L[ℝ] E →L[ℝ] ℝ)).mp (hmetric C hC hCt) a ha
  let N := c.source ∩ c ⁻¹' Metric.ball (c p) (r / 2)
  have hN : N ∈ 𝓝 p := inter_mem (c.open_source.mem_nhds hp)
    ((c.continuousOn.continuousAt (c.open_source.mem_nhds hp)).preimage_mem_nhds
      (Metric.ball_mem_nhds (c p) (by positivity)))
  refine ⟨N, hN, ?_⟩
  filter_upwards [hconv] with k hk q hq v
  have hqc : c q ∈ C := Metric.ball_subset_closedBall hq.2
  have hqi := hi (c q) (hCt hqc)
  let w : E := (mfderiv (𝓡 n) (𝓡 n) c.symm (c q)).inverse v
  have herr : |(gseq k).pullbackCoefficients c.symm (c q) w w -
      g.pullbackCoefficients c.symm (c q) w w| ≤
        a * ‖w‖ ^ 2 := by
    have hd : ‖(gseq k).pullbackCoefficients c.symm (c q) -
        g.pullbackCoefficients c.symm (c q)‖ ≤ a := by
      simpa only [dist_eq_norm, norm_sub_rev] using (hk (c q) hqc).le
    calc
      _ ≤ ‖(gseq k).pullbackCoefficients c.symm (c q) -
          g.pullbackCoefficients c.symm (c q)‖ * ‖w‖ * ‖w‖ := by
        simpa only [sub_apply, Real.norm_eq_abs] using
          ((gseq k).pullbackCoefficients c.symm (c q) -
            g.pullbackCoefficients c.symm (c q)).le_opNorm₂ w w
      _ ≤ a * ‖w‖ ^ 2 := by
        simpa only [pow_two, mul_assoc] using
          mul_le_mul_of_nonneg_right hd (mul_nonneg (norm_nonneg w) (norm_nonneg w))
  have hbound : (gseq k).pullbackCoefficients c.symm (c q) w w ≤
      2 * g.pullbackCoefficients c.symm (c q) w w := by
    have hh := (abs_le.mp herr).2
    linarith [hlower (c q) hqc w]
  change (gseq k).inner (c.symm (c q))
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c q) w)
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c q) w) ≤
    2 * g.inner (c.symm (c q))
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c q) w)
      (mfderiv (𝓡 n) (𝓡 n) c.symm (c q) w) at hbound
  have htransport := congrArg (fun z : M =>
    (gseq k).inner z v v ≤ 2 * g.inner z v v) (c.left_inv hq.1)
  apply htransport.mp
  simpa only [w, hqi.self_apply_inverse] using hbound

theorem eventually_inner_le_twice_of_chart_convergence
    (gseq : ℕ → RiemannianMetric n M) (g : RiemannianMetric n M)
    {K : Set M} (hK : IsCompact K)
    (hcharts : ∀ p ∈ K,
      ∃ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
        p ∈ c.source ∧ IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ c.symm c.target ∧
        ∀ C, IsCompact C → C ⊆ c.target →
          TendstoUniformlyOn (fun k => (gseq k).pullbackCoefficients c.symm)
            (g.pullbackCoefficients c.symm) atTop C) :
    ∀ᶠ k in atTop, ∀ q ∈ K, ∀ v : TangentSpace (𝓡 n) q,
      (gseq k).inner q v v ≤ 2 * g.inner q v v := by
  classical
  have hlocal (p : M) (hp : p ∈ K) : ∃ N ∈ 𝓝 p,
      ∀ᶠ k in atTop, ∀ q ∈ N, ∀ v : TangentSpace (𝓡 n) q,
        (gseq k).inner q v v ≤ 2 * g.inner q v v := by
    obtain ⟨c, hpc, hc, hm⟩ := hcharts p hp
    exact eventually_inner_le_near_chart gseq g p c hpc hc hm
  choose N hN hbound using hlocal
  obtain ⟨s, hs⟩ := hK.elim_nhds_subcover' N hN
  have hall := (Filter.eventually_all_finite s.finite_toSet).mpr
    (fun (p : K) (_ : p ∈ s) => hbound p p.property)
  filter_upwards [hall] with k hk q hq v
  obtain ⟨p, hp, hqp⟩ := mem_iUnion₂.mp (hs hq)
  exact hk p hp q hqp v

end PoincareConjecture.RiemannianMetric
