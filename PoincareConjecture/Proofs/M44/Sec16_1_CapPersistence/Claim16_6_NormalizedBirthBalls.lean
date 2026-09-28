import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_PhysicalBirthChart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_BufferBalls
import PoincareConjecture.Proofs.M01.NormalizationVolumeScaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

private theorem metric_eq_of_inner {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g h : RiemannianMetric n M)
    (heq : ∀ x v w, g.inner x v w = h.inner x v w) : g = h := by
  have hi : g.inner = h.inner := by
    funext x
    ext v w
    exact heq x v w
  cases g
  cases h
  cases hi
  rfl

theorem normalized_birth_ball {M : Type*} [TopologicalSpace M]
    [ChartedSpace StandardCapSpace M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M]
    (g ghat : RiemannianMetric 3 M) {h : ℝ} (hh : 0 < h)
    (hmetric : ∀ y v w, ghat.inner y v w = h⁻¹ ^ 2 * g.inner y v w)
    (p : M) (R : ℝ) : ghat.ball p R = g.ball p (h * R) := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  have heq : ghat = m01RescaledMetric g (h⁻¹ ^ 2) (sq_pos_of_pos (inv_pos.mpr hh)) :=
    metric_eq_of_inner _ _ hmetric
  rw [heq, m01RescaledMetric_ball, Real.sqrt_sq (inv_pos.mpr hh).le,
    div_inv_eq_mul, mul_comm R h]

theorem physical_birth_chart_image_ball
    (F : SurgeryFlowData.{u}) (t : ℝ) (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    {r eta : ℝ} (hr : 0 < r) (hreta : r < eta⁻¹)
    (Q : SurgeryCapClose F.standard_initial
      ((F.event t hT).local_result i).output ((F.event t hT).local_result i).metric
      ((F.event t hT).local_result i).tip (((F.event t hT).necks i).neck.scale) eta)
    (hball : Q.map '' F.standard_initial.metric.ball 0 r =
      ((F.event t hT).local_result i).metric.ball ((F.event t hT).local_result i).tip
        (((F.event t hT).necks i).neck.scale * r))
    (g : RiemannianMetric 3 (F.slice t).carrier)
    (hg : ∀ y v w, g.inner y v w = (F.parameters.h t)⁻¹ ^ 2 * (F.metric t).inner y v w)
    (f : StandardCapSpace → (F.slice t).carrier)
    (hf : ∀ x ∈ F.standard_initial.metric.ball 0 r,
      f x = (F.event t hT).local_embed i (Q.map x)) :
    f '' F.standard_initial.metric.ball 0 r = g.ball ((F.event t hT).caps i).tip r := by
  obtain ⟨e, hsource, hmap, htarget, _⟩ := exists_physical_birth_chart F t hT i hr hreta Q hball
  have hh := F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  rw [normalized_birth_ball (F.metric t) g hh hg, ← htarget, ← e.image_source_eq_target, hsource]
  exact image_congr (fun x hx => (hf x hx).trans (hmap x).symm)

theorem physical_birth_chart_buffer_balls
    (F : SurgeryFlowData.{u}) {t : ℝ} (ht : t ∈ F.time_domain)
    (g : RiemannianMetric 3 (F.slice t).carrier) (tip : (F.slice t).carrier)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) StandardCapSpace (F.slice t).carrier ∞)
    {a r R : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hmargin : a + r < R)
    (htarget : e.target = g.ball tip R) {V : Set StandardCapSpace}
    (hinner : e '' V ⊆ g.ball tip a) :
    ∀ x ∈ V, IsCompact (closure (g.ball (e x) r)) ∧ closure (g.ball (e x) r) ⊆ e.target := by
  intro x hx
  refine ⟨(F.slices_compact t ht).of_isClosed_subset isClosed_closure (subset_univ _), ?_⟩
  rw [htarget]
  exact g.closure_ball_subset_ball_of_margin ha hr hmargin (hinner (mem_image_of_mem e hx))

end PoincareConjecture.M44
