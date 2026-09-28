import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.CanonicalImageMetric
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.UniformMetricDistance
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.OpenMetricScaling
import PoincareConjecture.Proofs.M28.Mathlib.RelativeBilinearLimits
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMetricSpace











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M28

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ






theorem exists_canonicalImageMetric_source_distance_limit
    {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace E N]
    [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 N) (U : TopologicalSpace.Opens N)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set N) (p : N) (q : N) ≠ ⊤)
    (q : ℕ → U) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
    {a : ℝ} (ha : 0 < a)
    (Psi : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) E N ∞)
    (hsource : ∀ i, Metric.ball (0 : E) a ⊆ (Psi i).source)
    (hcenter : ∀ i, Psi i 0 = (q i : N))
    (hinside : ∀ᶠ i in atTop, Psi i '' Metric.ball (0 : E) a ⊆ (U : Set N))
    (A : E → Bilin) (B : ℕ → E → Bilin)
    (hA : ∀ z ∈ Metric.ball (0 : E) a, ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ A z v v)
    (hB : ∀ i z, z ∈ Metric.ball (0 : E) a → ∀ v,
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ B i z v v ∧ B i z v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2)
    (hlimit : TendstoUniformlyOn B A atTop (Metric.ball (0 : E) a))
    (lower upper : ℕ → ℝ)
    (hlower : Tendsto lower atTop (𝓝 1)) (hupper : Tendsto upper atTop (𝓝 1))
    (hsqueeze : ∀ᶠ i in atTop, ∀ z ∈ Metric.ball (0 : E) a, ∀ v,
      lower i * B i z v v ≤
        RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric g (R i) (hR i))
          (Psi i) z v v ∧
      RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric g (R i) (hR i))
          (Psi i) z v v ≤
        upper i * B i z v v) :
    let V : TopologicalSpace.Opens E := ⟨Metric.ball 0 a, Metric.isOpen_ball⟩
    let K : Set E := Metric.closedBall 0 (a / 64)
    let k : K → V := fun z => ⟨z, Metric.closedBall_subset_ball (by linarith) z.property⟩
    letI : Nonempty V := ⟨⟨0, Metric.mem_ball_self ha⟩⟩
    letI := V.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := V.isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ h : RiemannianMetric 3 V,
      (∀ (z : V) v w, h.inner z v w = A z v w) →
    letI := intrinsicOpenMetricSpace g U hfinite
    ∃ x : ℕ → K → U,
      (∀ᶠ i in atTop, ∀ z : K, (x i z : N) = Psi i z) ∧
      (∀ z w : K, h.edist (k z) (k w) ≠ ⊤) ∧
      TendstoUniformlyOn
        (fun i (p : K × K) => Real.sqrt (R i) * dist (x i p.1) (x i p.2))
        (fun p => (h.edist (k p.1) (k p.2)).toReal) atTop univ ∧
      ∀ᶠ i in atTop, ∀ z : K,
        Real.sqrt (R i) * dist (x i z) (q i) ≤ 3 * a / 64 := by
  classical
  intro V K k
  let : Nonempty V := ⟨⟨0, Metric.mem_ball_self ha⟩⟩
  let := V.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := V.isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  intro h hmetric
  let := intrinsicOpenMetricSpace g U hfinite
  let gseq : ℕ → RiemannianMetric 3 V := fun i =>
    canonicalImageMetric (M13.scaleSmoothMetric g (R i) (hR i))
      (Psi i) V (hsource i)
  let SK : Set V := {z | z.val ∈ K}
  have hcompare : ∀ c : ℝ, 1 < c → ∀ᶠ i in atTop, ∀ (z : V) (v : E),
      (gseq i).inner z v v ≤ c ^ 2 * h.inner z v v ∧
        h.inner z v v ≤ c ^ 2 * (gseq i).inner z v v := by
    intro c hc
    have hcomp := ContinuousLinearMap.eventually_mutual_quadratic_bounds_of_uniform_squeeze
      A B (fun i => RiemannianMetric.pullbackCoefficients
        (M13.scaleSmoothMetric g (R i) (hR i)) (Psi i))
      (by norm_num : (0 : ℝ) < 1 / 4) hA hlimit lower upper hlower hupper hsqueeze c hc
    filter_upwards [hcomp] with i hi
    intro z v
    simpa only [gseq, canonicalImageMetric_inner, hmetric] using hi z z.property v
  have hcoeff : ∀ᶠ i in atTop, ∀ z ∈ Metric.ball (0 : E) a, ∀ v,
      (1 / 8 : ℝ) * ‖v‖ ^ 2 ≤
        RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric g (R i) (hR i))
          (Psi i) z v v ∧
      RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric g (R i) (hR i))
          (Psi i) z v v ≤
        (9 / 2 : ℝ) * ‖v‖ ^ 2 := by
    filter_upwards [(tendsto_order.mp hlower).1 (1 / 2) (by norm_num),
      (tendsto_order.mp hupper).2 2 (by norm_num), hsqueeze] with i hlo hup hsq
    intro z hz v
    have hnonneg : 0 ≤ B i z v v :=
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (sq_nonneg ‖v‖)).trans
        (hB i z hz v).1
    constructor
    · calc
        (1 / 8 : ℝ) * ‖v‖ ^ 2 = (1 / 2 : ℝ) * ((1 / 4 : ℝ) * ‖v‖ ^ 2) := by ring
        _ ≤ (1 / 2 : ℝ) * B i z v v :=
          mul_le_mul_of_nonneg_left (hB i z hz v).1 (by norm_num)
        _ ≤ lower i * B i z v v := mul_le_mul_of_nonneg_right hlo.le hnonneg
        _ ≤ _ := (hsq z hz v).1
    · calc
        _ ≤ upper i * B i z v v := (hsq z hz v).2
        _ ≤ 2 * B i z v v := mul_le_mul_of_nonneg_right hup.le hnonneg
        _ ≤ 2 * ((9 / 4 : ℝ) * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hB i z hz v).2 (by norm_num)
        _ = (9 / 2 : ℝ) * ‖v‖ ^ 2 := by ring
  have hdistance : ∀ᶠ i in atTop, ∀ z ∈ SK, ∀ w ∈ SK,
      (gseq i).edist z w ≤
        ENNReal.ofReal (Real.sqrt (9 / 2 : ℝ)) * edist (z : E) (w : E) := by
    filter_upwards [hinside, hcoeff] with i hin hb
    intro z hz w hw
    exact (canonicalImageMetric_originalOpen_edist
      (M13.scaleSmoothMetric g (R i) (hR i)) (Psi i) U ha
      (hsource i) hin hb z w hz hw).2.1
  have hsqrt : Real.sqrt (9 / 2 : ℝ) ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 9 / 2),
      Real.sqrt_nonneg (9 / 2 : ℝ)]
  have hdiam : ∀ z ∈ SK, ∀ w ∈ SK, h.edist z w ≤ ENNReal.ofReal (3 * a / 16) := by
    obtain ⟨i, hi, hd⟩ := ((hcompare 2 (by norm_num)).and hdistance).exists
    intro z hz w hw
    have hreverse : h.edist z w ≤ ENNReal.ofReal 2 * (gseq i).edist z w := by
      simpa only [id_eq] using (gseq i).edist_le_mul_of_inner_mfderiv_le h
        (F := id) contMDiff_id (by norm_num : (0 : ℝ) < 2)
        (fun x v => by
          simpa only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply] using (hi x v).2) z w
    have hzw : dist (z : E) (w : E) ≤ a / 32 := by
      have hz0 : dist (z : E) 0 ≤ a / 64 := hz
      have hw0 : dist (w : E) 0 ≤ a / 64 := hw
      have ht := dist_triangle (z : E) 0 (w : E)
      rw [dist_comm (0 : E) (w : E)] at ht
      linarith
    have hscaledBound : ENNReal.ofReal 2 * (gseq i).edist z w ≤
        ENNReal.ofReal 2 * (ENNReal.ofReal (Real.sqrt (9 / 2 : ℝ)) *
          edist (z : E) (w : E)) := by
      gcongr
      exact hd z hz w hw
    refine (hreverse.trans hscaledBound).trans ?_
    rw [edist_dist, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply ENNReal.ofReal_le_ofReal
    calc
      2 * (Real.sqrt (9 / 2 : ℝ) * dist (z : E) (w : E)) ≤
          2 * (3 * (a / 32)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hsqrt hzw (dist_nonneg) (by norm_num)) (by norm_num)
      _ = 3 * a / 16 := by ring
  have huniform := tendstoUniformlyOn_edist_toReal_of_mutual_inner_bounds
    h gseq SK (by positivity : (0 : ℝ) ≤ 3 * a / 16) hdiam hcompare
  have huniformK : TendstoUniformlyOn
      (fun i (p : K × K) => ((gseq i).edist (k p.1) (k p.2)).toReal)
      (fun p => (h.edist (k p.1) (k p.2)).toReal) atTop univ :=
    (huniform.comp (fun p : K × K => (k p.1, k p.2))).mono
      (fun p _ => ⟨p.1.property, p.2.property⟩)
  let x : ℕ → K → U := fun i z =>
    if hin : Psi i '' Metric.ball (0 : E) a ⊆ (U : Set N) then
      ⟨Psi i z, hin ⟨z, (k z).property, rfl⟩⟩
    else q i
  have hx : ∀ᶠ i in atTop, ∀ z : K, (x i z : N) = Psi i z := by
    filter_upwards [hinside] with i hi
    intro z
    simp only [x, dif_pos hi]
  have hreal : ∀ᶠ i in atTop, ∀ z w : K,
      Real.sqrt (R i) * dist (x i z) (x i w) =
        ((gseq i).edist (k z) (k w)).toReal := by
    filter_upwards [hinside, hcoeff] with i hin hb
    intro z w
    have hdist := (canonicalImageMetric_originalOpen_edist
      (M13.scaleSmoothMetric g (R i) (hR i)) (Psi i) U ha
      (hsource i) hin hb (k z) (k w) z.property w.property).1
    have hxz : x i z = ⟨Psi i z, hin ⟨z, (k z).property, rfl⟩⟩ := by
      simp only [x, dif_pos hin]
    have hxw : x i w = ⟨Psi i w, hin ⟨w, (k w).property, rfl⟩⟩ := by
      simp only [x, dif_pos hin]
    rw [hxz, hxw, intrinsicOpenMetricSpace_dist, ← intrinsicOpenMetric_edist,
      ← intrinsicOpenMetric_scaleSmoothMetric_edist_toReal g U (R i) (hR i)]
    exact congrArg ENNReal.toReal hdist
  refine ⟨x, hx, ?_, ?_, ?_⟩
  · intro z w
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hdiam (k z) z.property (k w) w.property)
  · apply huniformK.congr
    exact hreal.mono fun i hi p _ => (hi p.1 p.2).symm
  · let z0 : K := ⟨0, Metric.mem_closedBall_self (by positivity)⟩
    filter_upwards [hx, hreal, hdistance] with i hi hre hd
    intro z
    have hz0 : x i z0 = q i := Subtype.ext ((hi z0).trans (hcenter i))
    rw [← hz0, hre z z0]
    have hbound := hd (k z) z.property (k z0) z0.property
    rw [edist_dist, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hbound
    have hrealBound := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) dist_nonneg)] at hrealBound
    refine hrealBound.trans ?_
    have hz : dist (z : E) 0 ≤ a / 64 := z.property
    calc
      Real.sqrt (9 / 2 : ℝ) * dist (k z : E) (k z0 : E) ≤ 3 * (a / 64) :=
        mul_le_mul hsqrt hz dist_nonneg (by norm_num)
      _ = 3 * a / 64 := by ring

end PoincareConjecture.M28
