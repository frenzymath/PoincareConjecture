import PoincareConjecture.Proofs.M14.Sec6_3_PrefixJoinCoefficients
import PoincareConjecture.Proofs.M14.Sec6_3_PrefixJoinCoordinates
import PoincareConjecture.Proofs.M14.Sec6_3_GaugeBlendDensity
import PoincareConjecture.Proofs.M14.Sec6_1_InteriorDensity

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14.PrefixJoinGauge

open Proofs.M09

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ c : ℝ} {x y : G.Point}
  {q : M14BackwardPath G T τ₁ τ₂ x y}
  {p : M14BackwardPath G T τ₁ c x (q.curve c)} (D : PrefixJoinGauge q p)

private noncomputable local instance dualNormedGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance dualNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance bilinearNormedGroup :
    NormedAddCommGroup
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance bilinearNormedSpace :
    NormedSpace ℝ
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem blend_contMDiffOn_one (a d : ℝ) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1
      (gaugeBlend D.index D.lift p.curve q.curve a d) (Ioo (c - D.radius) c) := by
  intro s hs
  have hp : s ∈ Ioo τ₁ c := ⟨D.left_margin.trans hs.1, hs.2⟩
  have hq : s ∈ Ioo τ₁ τ₂ :=
    ⟨hp.1, by linarith [hs.2, D.radius_pos, D.right_margin]⟩
  exact (gaugeBlend_contMDiffAt D.index D.lift p.curve q.curve D.image_open D.lift_smooth
    (by simp : (1 : ℕ∞ω) ≤ ∞) (c := a) (d := d)
    ((p.curve_regular s hp).contMDiffAt (isOpen_Ioo.mem_nhds hp))
    ((q.curve_regular s hq).contMDiffAt (isOpen_Ioo.mem_nhds hq))
    (D.prefix_in_image s (Ioo_subset_Icc_self hs))
    (D.continuation_in_image s ⟨hs.1.le, by linarith [hs.2, D.radius_pos]⟩)
    (D.region_subset (D.blend_mem_region a d (Ioo_subset_Icc_self hs)))).contMDiffWithinAt

theorem exists_blend_density_bound (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a d : ℝ, ∀ s ∈ Ioo (c - D.radius) c,
      ‖M14RawLIntegrand G (gaugeBlend D.index D.lift p.curve q.curve a d)
        (projectedCurveVelocity G (gaugeBlend D.index D.lift p.curve q.curve a d)) s‖ ≤
      C * (1 + ‖deriv (smoothJoinBlend (fun t => (D.lift (p.curve t)).2.val)
        (fun t => (D.lift (q.curve t)).2.val) a d) s‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := D.exists_coefficient_bound hM12
  refine ⟨C, hC, ?_⟩
  intro a d s hs
  have hp : s ∈ Ioo τ₁ c := ⟨D.left_margin.trans hs.1, hs.2⟩
  have hq : s ∈ Ioo τ₁ τ₂ :=
    ⟨hp.1, by linarith [hs.2, D.radius_pos, D.right_margin]⟩
  have hwide : s ∈ Icc (c - D.radius) (c + D.radius) :=
    ⟨hs.1.le, by linarith [hs.2, D.radius_pos]⟩
  have hclock := (D.lift_time _ (D.continuation_in_image s hwide)).trans
    (q.curve_time s (Ioo_subset_Icc_self hq))
  have hmem := D.blend_mem_region a d (Ioo_subset_Icc_self hs)
  rw [gaugeBlend_quadraticDensity D.index D.lift p.curve q.curve
    (D.lift (q.curve c)).2 D.image_open D.lift_smooth
    ((p.curve_regular s hp).contMDiffAt (isOpen_Ioo.mem_nhds hp))
    ((q.curve_regular s hq).contMDiffAt (isOpen_Ioo.mem_nhds hq))
    (D.prefix_in_image s (Ioo_subset_Icc_self hs))
    (D.continuation_in_image s hwide) (D.region_subset hmem) hclock]
  let v := smoothJoinBlend (fun t => (D.lift (p.curve t)).2.val)
    (fun t => (D.lift (q.curve t)).2.val) a d
  let B := backwardMetricCoefficient (G.gaugeCover.spatial D.index)
    (G.gaugeCover.metric D.index).metric T (D.lift (q.curve c)).2 (s, v s)
  let V := backwardPotentialCoefficient D.index (fun t => (D.lift (q.curve t)).1)
    (D.lift (q.curve c)).2 (s, v s)
  obtain ⟨hB, hV⟩ := hbound s hwide (v s) hmem
  change ‖B (deriv v s) (deriv v s) / 2 + V‖ ≤ C * (1 + ‖deriv v s‖ ^ 2)
  have hkin := B.le_of_opNorm₂_le_of_le hB (le_refl ‖deriv v s‖) (le_refl ‖deriv v s‖)
  have hsum := norm_add_le (B (deriv v s) (deriv v s) / 2) V
  norm_num only [norm_div, Real.norm_ofNat] at hsum
  nlinarith [mul_nonneg hC (sq_nonneg ‖deriv v s‖)]

end PoincareConjecture.M14.PrefixJoinGauge
