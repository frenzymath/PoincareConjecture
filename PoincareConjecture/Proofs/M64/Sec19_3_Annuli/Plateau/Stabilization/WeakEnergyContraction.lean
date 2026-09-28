import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.WeakProjection













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Bundle Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n m k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "H" => EuclideanSpace ℝ (Fin k)
local notation "mu" => volume.restrict (interior m64AnnulusDomain)



theorem auxiliaryCircle_retained_observed_metric_le
    (P : M62.CircleProductData F circumference) (time : ℝ)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (o : P.charts.Point → H) (ho : ContMDiff (𝓡 (n + 1)) (𝓡 k) 1 o)
    (L : H →L[ℝ] E) (hL : ∀ q : P.charts.Point, L (o q) = e q.1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (C : P.charts.Point → H →L[ℝ] H →L[ℝ] ℝ)
    (hB : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        (F.metric time).inner q v v)
    (hC : ∀ (q : P.charts.Point) (v : TangentSpace (𝓡 (n + 1)) q),
      C q (mfderiv (𝓡 (n + 1)) (𝓡 k) o q v) (mfderiv (𝓡 (n + 1)) (𝓡 k) o q v) =
        (P.flow.metric time).inner q v v)
    (q : P.charts.Point) (w : H) (hw : w ∈ range (mfderiv (𝓡 (n + 1)) (𝓡 k) o q)) :
    B q.1 (L w) (L w) ≤ C q w w := by
  obtain ⟨v, rfl⟩ := hw
  rw [← auxiliaryCircle_retained_observation_mfderiv P e he o ho L hL,
    hB, hC, P.metric_eq]
  exact le_add_of_nonneg_right
    ((P.circle.metricOnPoints.toRiemannianMetric.toCore q.2).re_inner_nonneg _)



theorem auxiliaryCircle_projected_weak_weightedEnergy
    (P : M62.CircleProductData F circumference) (time : ℝ)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsEmbedding e)
    (o : P.charts.Point → H) (ho : ContMDiff (𝓡 (n + 1)) (𝓡 k) 1 o) (hoi : IsEmbedding o)
    (L : H →L[ℝ] E) (hL : ∀ q : P.charts.Point, L (o q) = e q.1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hBc : Continuous B)
    (C : P.charts.Point → H →L[ℝ] H →L[ℝ] ℝ) (hCc : Continuous C)
    {KB KC : ℝ} (hBb : ∀ q, ‖B q‖ ≤ KB) (hCb : ∀ q, ‖C q‖ ≤ KC)
    (hB : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        (F.metric time).inner q v v)
    (hC : ∀ (q : P.charts.Point) (v : TangentSpace (𝓡 (n + 1)) q),
      C q (mfderiv (𝓡 (n + 1)) (𝓡 k) o q v) (mfderiv (𝓡 (n + 1)) (𝓡 k) o q v) =
        (P.flow.metric time).inner q v v)
    {c0 c1 : ℝ → P.charts.Point} (hc0 : Continuous c0) (hc1 : Continuous c1)
    (A : M64ObservedWeakAnnulus (n := n + 1) o c0 c1) :
    ∃ D : M64ObservedWeakAnnulus (n := n) e (fun x => (c0 x).1) (fun x => (c1 x).1),
      D.map = (fun p => (A.map p).1) ∧
        (∀ i, ∀ᵐ p ∂mu, D.column i p = L (A.column i p)) ∧
        ∀ r : ℝ, 0 < r → D.weightedEnergy B r ≤ A.weightedEnergy C r := by
  obtain ⟨D, hmap, hcolumn⟩ := auxiliaryCircle_projected_weak_annulus
    P e he o ho L hL hc0 hc1 A
  refine ⟨D, hmap, hcolumn, ?_⟩
  intro r hr
  apply integral_mono_ae
    (D.weightedEnergy_integrable B hBc hei hBb r)
    (A.weightedEnergy_integrable C hCc hoi hCb r)
  filter_upwards [hcolumn 0, hcolumn 1, A.tangent 0, A.tangent 1] with p h0 h1 ht0 ht1
  rw [hmap, h0, h1]
  have hb0 := auxiliaryCircle_retained_observed_metric_le P time e he o ho L hL B C hB hC
    (A.map p) (A.column 0 p) ht0
  have hb1 := auxiliaryCircle_retained_observed_metric_le P time e he o ho L hL B C hB hC
    (A.map p) (A.column 1 p) ht1
  exact div_le_div_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left hb0 hr.le)
      (mul_le_mul_of_nonneg_left hb1 (inv_pos.mpr hr).le)) (by norm_num)

end PoincareConjecture.M64
