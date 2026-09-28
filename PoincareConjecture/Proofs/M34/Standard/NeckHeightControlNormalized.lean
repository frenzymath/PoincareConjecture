import PoincareConjecture.Proofs.M34.Standard.NeckHeightControlImage
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNormalizedBalls

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.CapCertificate

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {m : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] [IsManifold (𝓡 m) ∞ X]
  [T3Space X] {g : RiemannianMetric 3 M} (N : CapCertificate g)

theorem normalized_ball_closure_subset_image_recutCarrier
    (h : RiemannianMetric m X) (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn (𝓡 3) (𝓡 m) 1 e e.source)
    (hi : ContMDiffOn (𝓡 m) (𝓡 3) 1 e.symm e.target)
    {c d b A mu L r : ℝ} (hc : -N.epsilon⁻¹ < c) (hcd : c < d) (hdb : d < b)
    (hb : b < N.epsilon⁻¹) (hA : 0 < A)
    (hcapture : closure (N.recutCarrier b) ⊆ e.source)
    (hbound : ∀ x ∈ closure (N.recutCarrier b), ∀ v : TangentSpace (𝓡 3) x,
      g.tangentNorm x v ≤ A * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 m) e x v))
    (hmu : 0 < mu) (hL : 0 < L) (hgap : 1 < mu * L ^ 2)
    (hshort : (2 / N.end_neck.scale) * A * L ≤ b - d)
    {R : X → ℝ} (hboundary : ∀ x ∈ N.boundary_sphere, mu ≤ R (e x))
    {o : M} (ho : o ∈ N.closed_core) (hr : 0 < r)
    (hbounded : BddAbove (R '' h.ball (e o) r))
    (hnormalized : sSup (R '' h.ball (e o) r) = r⁻¹ ^ 2) :
    closure (h.ball (e o) r) ⊆ e '' N.recutCarrier b := by
  have hcore : N.closed_core ⊆ e.source := fun x hx => hcapture (subset_closure (Or.inl hx))
  have hYcompact : IsCompact (e '' N.closed_core) :=
    N.closed_core_compact.image_of_continuousOn (e.continuousOn.mono hcore)
  have hfront : e '' N.boundary_sphere = frontier (e '' N.closed_core) := by
    rw [← N.core_frontier_eq_boundary]
    apply e.image_frontier_eq_of_isCompact
    · simpa only [N.closed_core_compact.isClosed.closure_eq] using N.closed_core_compact
    · simpa only [N.closed_core_compact.isClosed.closure_eq] using hcore
  apply h.closure_normalized_ball_subset_of_collar hYcompact.isClosed
    (image_mono (fun _ hx => Or.inl hx)) (mem_image_of_mem e ho) hmu hL hgap
    (fun x hx => ?_) (fun s hs => ?_) hr hbounded hnormalized
  · rw [← hfront] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hboundary y hy
  · apply N.ball_subset_image_recutCarrier_of_tangentNorm_le h e hf hi hc hcd hdb hb hA
      hcapture hbound _ ho
    exact (mul_le_mul_of_nonneg_left hs.le
      (mul_nonneg (div_nonneg (by norm_num) N.end_neck.scale_pos.le) hA.le)).trans hshort

theorem exists_normalized_ball_in_image_recutCarrier [ConnectedSpace X]
    (h : RiemannianMetric m X) (hcomplete : MetricComplete h)
    (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn (𝓡 3) (𝓡 m) 1 e e.source)
    (hi : ContMDiffOn (𝓡 m) (𝓡 3) 1 e.symm e.target)
    {c d b A mu L : ℝ} (hc : -N.epsilon⁻¹ < c) (hcd : c < d) (hdb : d < b)
    (hb : b < N.epsilon⁻¹) (hA : 0 < A)
    (hcapture : closure (N.recutCarrier b) ⊆ e.source)
    (hbound : ∀ x ∈ closure (N.recutCarrier b), ∀ v : TangentSpace (𝓡 3) x,
      g.tangentNorm x v ≤ A * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 m) e x v))
    (hmu : 0 < mu) (hL : 0 < L) (hgap : 1 < mu * L ^ 2)
    (hshort : (2 / N.end_neck.scale) * A * L ≤ b - d)
    {R : X → ℝ} (hR : Continuous R)
    (hboundary : ∀ x ∈ N.boundary_sphere, mu ≤ R (e x))
    {o : M} (ho : o ∈ N.closed_core) (hRo : 0 < R (e o)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ (Real.sqrt (R (e o)))⁻¹ ∧
      sSup (R '' h.ball (e o) r) = r⁻¹ ^ 2 ∧
      IsCompact (closure (h.ball (e o) r)) ∧
      closure (h.ball (e o) r) ⊆ e '' N.recutCarrier b := by
  obtain ⟨r, hr, hrr, hnorm, hcompact⟩ :=
    h.exists_normalized_ball_of_continuous hcomplete hR (e o) hRo
  have hbounded : BddAbove (R '' h.ball (e o) r) :=
    (hcompact.image hR).bddAbove.mono (image_mono subset_closure)
  exact ⟨r, hr, hrr, hnorm, hcompact,
    N.normalized_ball_closure_subset_image_recutCarrier h e hf hi hc hcd hdb hb hA
      hcapture hbound hmu hL hgap hshort hboundary ho hr hbounded hnorm⟩

end PoincareConjecture.CapCertificate
