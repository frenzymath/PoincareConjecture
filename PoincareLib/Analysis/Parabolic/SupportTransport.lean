import PoincareLib.Analysis.Parabolic.ConvexSupport
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Transport of supporting normals

Linear isometries carry unit supporting normals and preserve distance to the
carrier. A locally transported active support therefore touches the distance
envelope from below. This module uses the isometry supplied by transport;
constructing that isometry from a compatible connection is a separate step.

Source: Morgan--Tian, Claim 4.2, printed p. 64; Theorems 4.7--4.8, p. 66.
-/

set_option autoImplicit false

open Set Filter
open scoped InnerProductSpace Topology

namespace Poincare.Parabolic

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Transporting the contact point, normal, and test vector preserves support
evaluation exactly. -/
lemma support_eval_map (e : E ≃ₗᵢ[ℝ] F) (p n v : E) :
    ⟪e n, e v - e p⟫_ℝ = ⟪n, v - p⟫_ℝ := by
  rw [← e.map_sub, e.inner_map_map]

/-- The corresponding evaluation formula for a vector in the target fiber. -/
lemma support_eval_pullback (e : E ≃ₗᵢ[ℝ] F) (p n : E) (v : F) :
    ⟪e n, v - e p⟫_ℝ = ⟪n, e.symm v - p⟫_ℝ := by
  simpa only [e.apply_symm_apply] using support_eval_map e p n (e.symm v)

/-- Unit support pairs are carried to unit support pairs of the image carrier. -/
lemma unitSupport_map (e : E ≃ₗᵢ[ℝ] F) {K : Set E} {q : E × E}
    (hq : q ∈ unitSupportSet K) :
    (e q.1, e q.2) ∈ unitSupportSet (e '' K) := by
  refine ⟨mem_image_of_mem e hq.1, ?_, ?_⟩
  · simpa only [e.norm_map] using hq.2.1
  · rintro _ ⟨z, hz, rfl⟩
    simpa only [support_eval_map] using hq.2.2 z hz

/-- Support-pair transport is an equivalence. No compactness of the carrier is
needed for this algebraic statement. -/
lemma unitSupport_map_iff (e : E ≃ₗᵢ[ℝ] F) {K : Set E} {q : E × E} :
    (e q.1, e q.2) ∈ unitSupportSet (e '' K) ↔ q ∈ unitSupportSet K := by
  refine ⟨fun hq => ?_, unitSupport_map e⟩
  have h := unitSupport_map e.symm hq
  have hK : e.symm '' (e '' K) = K := by
    ext z
    simp
  simpa only [e.symm_apply_apply, hK] using h

/-- Isometric support transport also preserves bounds on the contact points. -/
lemma boundedUnitSupport_map_iff (e : E ≃ₗᵢ[ℝ] F) {K : Set E} {q : E × E} {R : ℝ} :
    (e q.1, e q.2) ∈ boundedUnitSupportSet (e '' K) R ↔
      q ∈ boundedUnitSupportSet K R := by
  change ((e q.1, e q.2) ∈ unitSupportSet (e '' K) ∧ ‖e q.1‖ ≤ R) ↔
    (q ∈ unitSupportSet K ∧ ‖q.1‖ ≤ R)
  rw [unitSupport_map_iff, e.norm_map]

/-- Distance to a carrier is invariant under an isometry mapping it onto the
target carrier. -/
lemma infDist_map_carrier (e : E ≃ₗᵢ[ℝ] F) {K : Set E} {L : Set F}
    (hmap : e '' K = L) (v : E) :
    Metric.infDist (e v) L = Metric.infDist v K := by
  rw [← hmap]
  exact Metric.infDist_image e.isometry

/-- Pull back a target vector to compute its distance to the transported carrier. -/
lemma infDist_pullback_carrier (e : E ≃ₗᵢ[ℝ] F) {K : Set E} {L : Set F}
    (hmap : e '' K = L) (v : F) :
    Metric.infDist v L = Metric.infDist (e.symm v) K := by
  simpa only [e.apply_symm_apply] using infDist_map_carrier e hmap (e.symm v)

/-- A transported support bounds distance from below in the target fiber. -/
lemma transported_support_eval_le_infDist [FiniteDimensional ℝ E]
    {K : Set E} (hne : K.Nonempty) (hclosed : IsClosed K) (hconv : Convex ℝ K)
    (e : E ≃ₗᵢ[ℝ] F) {L : Set F} (hmap : e '' K = L)
    {q : E × E} (hq : q ∈ unitSupportSet K) (v : F) :
    ⟪e q.2, v - e q.1⟫_ℝ ≤ Metric.infDist v L := by
  rw [support_eval_pullback, infDist_pullback_carrier e hmap]
  exact unitSupport_eval_le_infDist hne hclosed hconv hq (e.symm v)

/-- A support active at a local distance maximum gives a scalar local maximum
after transport. The fibers may depend on the base point; carrier transport
is required only on a neighborhood of the contact point. -/
theorem isLocalMax_transported_support [FiniteDimensional ℝ E]
    {X : Type*} [TopologicalSpace X] {V : X → Type*}
    [∀ y, NormedAddCommGroup (V y)] [∀ y, InnerProductSpace ℝ (V y)]
    {K : Set E} (hne : K.Nonempty) (hclosed : IsClosed K) (hconv : Convex ℝ K)
    (e : ∀ y, E ≃ₗᵢ[ℝ] V y) (L : ∀ y, Set (V y)) (U : ∀ y, V y)
    {x : X} (hmap : ∀ᶠ y in 𝓝 x, e y '' K = L y)
    {q : E × E} (hq : q ∈ unitSupportSet K)
    (hactive : ⟪e x q.2, U x - e x q.1⟫_ℝ = Metric.infDist (U x) (L x))
    (hmax : IsLocalMax (fun y => Metric.infDist (U y) (L y)) x) :
    IsLocalMax (fun y => ⟪e y q.2, U y - e y q.1⟫_ℝ) x := by
  filter_upwards [hmap, hmax] with y hy hdist
  exact ((transported_support_eval_le_infDist hne hclosed hconv (e y) hy hq (U y)).trans
    hdist).trans_eq hactive.symm

end Poincare.Parabolic
