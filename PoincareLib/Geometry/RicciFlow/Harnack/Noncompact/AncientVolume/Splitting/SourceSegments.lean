import PoincareLib.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Geometry
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.EndpointSelection

/-!
# Actual source segments at escaping centers

Complete Riemannian metrics provide finite minimizing geodesics. Constant
reparameterization gives unit-speed segments, including for the metrics
rescaled by an inverse squared length. Comparison cosines are unchanged
by this rescaling. The point-selection radius-to-distance limit and the
farther-vertex estimate force both normalized endpoint lengths to infinity.

These are source-space inputs to Kleiner--Lott, Appendix G, p. 2852, and
Morgan--Tian, arXiv:math/0607607v2, Theorem 5.35, pp. 122--123. Hinge and
corresponding-side comparisons remain explicit inputs to the neighboring
selection and arc-construction theorems.

Direct statement comparison: the segment theorem constructs the segments
from completeness and endpoints. The divergence theorem assumes only the
stated numerical point-selection and farther-vertex bounds. No segment,
line, distance convergence, or splitting is an input to either conclusion.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace Poincare.AncientVolume.Splitting

/-- The spatial point-selection scale and farther-vertex bound force both
endpoint distances to diverge in the normalized metric. -/
theorem normalized_endpoint_lengths_tendsto_atTop
    {X : Type*} [MetricSpace X] (p : X) (q y : ℕ → X) (r : ℕ → ℝ)
    (hq : ∀ i, 0 < dist p (q i)) (hr : ∀ i, 0 < r i)
    (hsmall : Tendsto (fun i => r i / dist p (q i)) atTop (𝓝 0))
    (hfar : ∀ i, dist p (q i) * ((i : ℝ) + 2) + 1 ≤ dist p (y i)) :
    Tendsto (fun i => dist p (q i) / r i) atTop atTop ∧
      Tendsto (fun i => dist (q i) (y i) / r i) atTop atTop := by
  have hsmall' : Tendsto (fun i => r i / dist p (q i)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsmall, Eventually.of_forall fun i => div_pos (hr i) (hq i)⟩
  have hleft : Tendsto (fun i => dist p (q i) / r i) atTop atTop := by
    simpa only [Function.comp_def, inv_div] using tendsto_inv_nhdsGT_zero.comp hsmall'
  refine ⟨hleft, tendsto_atTop_mono (fun i => ?_) hleft⟩
  apply div_le_div_of_nonneg_right _ (hr i).le
  have htri := dist_triangle p (q i) (y i)
  have hnonneg := mul_nonneg (hq i).le (Nat.cast_nonneg i : 0 ≤ (i : ℝ))
  nlinarith [hfar i]

end Poincare.AncientVolume.Splitting

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Exact intrinsic distance after normalization by an inverse squared
length. This identity does not require completeness. -/
theorem rescaledMetric_edist_toReal_of_inverse_square
    (g : RiemannianMetric n M) (r : ℝ) (hr : 0 < r) (x y : M) :
    ((rescaledMetric g ((r ^ 2)⁻¹) (by positivity)).edist x y).toReal =
      (g.edist x y).toReal / r := by
  rw [rescaledMetric_edist, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sqrt_inv, Real.sqrt_sq hr.le]
  ring

/-- Constant positive metric rescaling preserves the intrinsic Euclidean
comparison cosine of three endpoints. -/
theorem endpoint_comparison_cosine_rescaledMetric
    (g : RiemannianMetric n M) (c : ℝ) (hc : 0 < c) (p q y : M) :
    let d := fun x z => (g.edist x z).toReal
    let D := fun x z => ((rescaledMetric g c hc).edist x z).toReal
    (D p q ^ 2 + D q y ^ 2 - D p y ^ 2) / (2 * D p q * D q y) =
      (d p q ^ 2 + d q y ^ 2 - d p y ^ 2) / (2 * d p q * d q y) := by
  dsimp only
  simp only [rescaledMetric_edist, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have hfactor : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  by_cases hleft : (g.edist p q).toReal = 0
  · simp [hleft]
  by_cases hright : (g.edist q y).toReal = 0
  · simp [hright]
  field_simp

/-- A complete metric constructs a finite unit-speed minimizing segment
between any two distinct endpoints. -/
theorem exists_unit_speed_minimizing_segment_of_metricComplete
    [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p q : M)
    (hd : 0 < (g.edist p q).toReal) :
    ∃ γ : ℝ → M, γ 0 = p ∧ γ (g.edist p q).toReal = q ∧
      ∀ s ∈ Icc (0 : ℝ) (g.edist p q).toReal,
      ∀ t ∈ Icc (0 : ℝ) (g.edist p q).toReal,
        (g.edist (γ s) (γ t)).toReal = |s - t| := by
  obtain ⟨ε, _, γ, _, hγ0, hγ1, hγ⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hc p q
  refine ⟨fun t => γ (t / (g.edist p q).toReal), ?_, ?_, ?_⟩
  · simpa only [zero_div] using hγ0
  · simpa only [div_self hd.ne'] using hγ1
  · intro s hs t ht
    rw [hγ (s / (g.edist p q).toReal)
      ⟨div_nonneg hs.1 hd.le, (div_le_one hd).mpr hs.2⟩
      (t / (g.edist p q).toReal)
      ⟨div_nonneg ht.1 hd.le, (div_le_one hd).mpr ht.2⟩,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
      ← sub_div, abs_div, abs_of_pos hd, div_mul_cancel₀ _ hd.ne']

/-- Actual normalized source segments from each center to the original
base point and its chosen farther vertex. -/
theorem exists_normalized_source_segments
    [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    (p : M) (q y : ℕ → M) (r : ℕ → ℝ)
    (hq : ∀ i, 0 < (g.edist (q i) p).toReal)
    (hy : ∀ i, 0 < (g.edist (q i) (y i)).toReal)
    (hr : ∀ i, 0 < r i) :
    let G := fun i => rescaledMetric g ((r i ^ 2)⁻¹) (inv_pos.mpr (pow_pos (hr i) 2))
    let a := fun i => (g.edist (q i) p).toReal / r i
    let b := fun i => (g.edist (q i) (y i)).toReal / r i
    ∃ minus plus : ℕ → ℝ → M,
      (∀ i, minus i 0 = q i ∧ minus i (a i) = p ∧
        plus i 0 = q i ∧ plus i (b i) = y i) ∧
      (∀ i, ∀ s ∈ Icc (0 : ℝ) (a i), ∀ t ∈ Icc (0 : ℝ) (a i),
        ((G i).edist (minus i s) (minus i t)).toReal = |s - t|) ∧
      (∀ i, ∀ s ∈ Icc (0 : ℝ) (b i), ∀ t ∈ Icc (0 : ℝ) (b i),
        ((G i).edist (plus i s) (plus i t)).toReal = |s - t|) := by
  dsimp only
  have hsegments (i : ℕ) (z : M) (hz : 0 < (g.edist (q i) z).toReal) :
      ∃ γ : ℝ → M, γ 0 = q i ∧ γ ((g.edist (q i) z).toReal / r i) = z ∧
        ∀ s ∈ Icc (0 : ℝ) ((g.edist (q i) z).toReal / r i),
        ∀ t ∈ Icc (0 : ℝ) ((g.edist (q i) z).toReal / r i),
          ((rescaledMetric g ((r i ^ 2)⁻¹) (inv_pos.mpr (pow_pos (hr i) 2))).edist
            (γ s) (γ t)).toReal =
            |s - t| := by
    have hdist := g.rescaledMetric_edist_toReal_of_inverse_square (r i) (hr i) (q i) z
    obtain ⟨γ, hγ0, hγend, hγ⟩ :=
      (rescaledMetric g ((r i ^ 2)⁻¹) (inv_pos.mpr (pow_pos (hr i) 2))).exists_unit_speed_minimizing_segment_of_metricComplete
        (metricComplete_rescaledMetric _ _ _ hc) (q i) z (by rw [hdist]; exact div_pos hz (hr i))
    exact ⟨γ, hγ0, by simpa only [hdist] using hγend, by simpa only [hdist] using hγ⟩
  choose minus hminus0 hminusend hminus using fun i => hsegments i p (hq i)
  choose plus hplus0 hplusend hplus using fun i => hsegments i (y i) (hy i)
  exact ⟨minus, plus, fun i => ⟨hminus0 i, hminusend i, hplus0 i, hplusend i⟩,
    hminus, hplus⟩

end PoincareMT.RiemannianMetric
