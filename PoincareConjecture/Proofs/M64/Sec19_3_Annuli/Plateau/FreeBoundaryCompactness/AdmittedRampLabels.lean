import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.AffineLabelLipschitz
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.RampLabelOscillation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LipschitzRectangleFTC
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.PeriodicRectangleLipschitz
import PoincareConjecture.Proofs.M40.Mathlib.LocalSmoothLipschitz













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Bundle
open scoped Topology Manifold ContDiff NNReal ENNReal Bundle

namespace PoincareConjecture.M64

private theorem periodic_rectangle_trace_locallyLipschitz
    {Y : Type*} [PseudoEMetricSpace Y] {f : LoopPlane → Y}
    (hperiod : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    {K : ℝ≥0} (hLip : LipschitzOnWith K f m64AnnulusDomain)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    LocallyLipschitz (fun x => f (annulusPoint x s)) := by
  intro x
  have hline := m64AnnulusPoint_horizontal_lipschitz s
  obtain ⟨B, U, hU, hB⟩ := m64_periodic_rectangle_locally_lipschitz hperiod hLip
    (show annulusPoint x s ∈ {p : LoopPlane | 0 ≤ p 1 ∧ p 1 ≤ 1} from hs)
  have hlim : Tendsto (fun y => annulusPoint y s) (𝓝 x)
      (𝓝[{p : LoopPlane | 0 ≤ p 1 ∧ p 1 ≤ 1}] annulusPoint x s) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hline.continuous.continuousAt,
      Filter.Eventually.of_forall (fun _ => hs)⟩
  exact ⟨B * 1, (fun y => annulusPoint y s) ⁻¹' U, hlim hU,
    hB.comp hline.lipschitzOnWith (fun _ hy => hy)⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}




theorem admitted_ramp_label_locallyLipschitz
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (gamma : ℝ → P.charts.Point)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma t)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    {sigma : ℝ → ℝ} (hsigma : Continuous sigma) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (htrace : ∀ x, A.map (annulusPoint x s) = gamma (sigma x)) :
    LocallyLipschitz sigma := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin 1)) P.circle.Point := P.circle.chartedSpace
  let : IsManifold (𝓡 1) ∞ P.circle.Point := P.circle.isManifold
  let : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) P.charts.Point := P.charts.chartedSpace
  let : IsManifold (𝓡 (n + 1)) ∞ P.charts.Point := P.charts.isManifold
  let g := P.flow.metric t
  let : LocallyCompactSpace P.charts.Point :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin (n + 1))) P.charts.Point
  let : RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P.charts.Point → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
      (TangentSpace (𝓡 (n + 1)) : P.charts.Point → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace P.charts.Point := EMetricSpace.ofRiemannianMetric (𝓡 (n + 1)) _
  let : IsRiemannianManifold (𝓡 (n + 1)) P.charts.Point := ⟨fun _ _ => rfl⟩
  have hALip : LipschitzOnWith (Real.toNNReal A.lipschitz_constant)
      A.map m64AnnulusDomain := by
    intro x hx y hy
    change g.edist (A.map x) (A.map y) ≤ ENNReal.ofReal A.lipschitz_constant * edist x y
    simpa only [g, edist_dist, dist_eq_norm] using
      A.lipschitz_on_domain ⟨x, hx⟩ ⟨y, hy⟩
  have hT := periodic_rectangle_trace_locallyLipschitz A.periodic hALip hs
  obtain ⟨L⟩ := m63PositiveDegreeLift_nonempty P gamma hperiod hgamma hramp
  obtain ⟨alpha, halpha, hlower⟩ := positive_ramp_lift_uniform_lower_slope P gamma L
  have habs (u v : ℝ) : alpha * |u - v| ≤ |L.lift u - L.lift v| := by
    rcases le_total u v with huv | hvu
    · have h := hlower u v huv
      have hmono : L.lift u ≤ L.lift v := by nlinarith
      rw [abs_of_nonpos (sub_nonpos.mpr huv), abs_of_nonpos (sub_nonpos.mpr hmono)]
      linarith
    · have h := hlower v u hvu
      have hmono : L.lift v ≤ L.lift u := by nlinarith
      rw [abs_of_nonneg (sub_nonneg.mpr hvu), abs_of_nonneg (sub_nonneg.mpr hmono)]
      exact h
  intro x
  let H := P.circle.quotient_local_diffeomorph (L.lift (sigma x))
  let psi : P.charts.Point → ℝ := H.localInverse ∘ Prod.snd
  have hsnd : ContMDiff (𝓡 (n + 1)) (𝓡 1) ∞
      (Prod.snd : P.charts.Point → P.circle.Point) :=
    contMDiff_snd.comp P.charts.to_product_smooth
  have hpsi : ContMDiffAt (𝓡 (n + 1)) 𝓘(ℝ, ℝ) 1 psi (gamma (sigma x)) := by
    have hinv := H.localInverse_contMDiffAt.of_le (m := 1) (by norm_num)
    change ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) 1 H.localInverse
      (P.circle.quotient (L.lift (sigma x))) at hinv
    rw [L.quotient_eq] at hinv
    exact hinv.comp _ (hsnd.of_le (by norm_num)).contMDiffAt
  obtain ⟨C, -, V, hV, hC⟩ := M40.exists_lipschitzOn_nhds_of_contMDiffAt hpsi
  obtain ⟨B, U, hU, hB⟩ := hT x
  have hpre : (fun y => A.map (annulusPoint y s)) ⁻¹' V ∈ 𝓝 x := by
    apply (hB.continuousOn.continuousAt hU).preimage_mem_nhds
    simpa only [htrace] using hV
  have heq : ∀ᶠ y in 𝓝 x, psi (A.map (annulusPoint y s)) = L.lift (sigma y) := by
    have hh := H.localInverse_eventuallyEq_left.comp_tendsto
      (L.regular.continuous.comp hsigma).continuousAt
    filter_upwards [hh] with y hy
    change H.localInverse (P.circle.quotient (L.lift (sigma y))) = L.lift (sigma y) at hy
    rw [L.quotient_eq] at hy
    simpa only [Function.comp_apply, psi, htrace] using hy
  let W := U ∩ (fun y => A.map (annulusPoint y s)) ⁻¹' V ∩
    {y | psi (A.map (annulusPoint y s)) = L.lift (sigma y)}
  have hW : W ∈ 𝓝 x := inter_mem (inter_mem hU hpre) heq
  have hcomp : LipschitzOnWith (C * B) (fun y => psi (A.map (annulusPoint y s))) W :=
    hC.comp (hB.mono (fun _ hy => hy.1.1)) (fun _ hy => hy.1.2)
  refine ⟨(C * B) / ⟨alpha, halpha.le⟩, W, hW, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro u hu v hv
  have hdist := hcomp.dist_le_mul u hu v hv
  rw [Real.dist_eq, hu.2, hv.2, Real.dist_eq] at hdist
  have hbound := (habs (sigma u) (sigma v)).trans hdist
  change |sigma u - sigma v| ≤ ((C : ℝ) * B / alpha) * |u - v|
  calc
    |sigma u - sigma v| ≤ ((C * B : ℝ≥0) : ℝ) * |u - v| / alpha :=
      (le_div_iff₀ halpha).mpr (by simpa only [mul_comm] using hbound)
    _ = _ := by rw [NNReal.coe_mul]; ring




theorem admitted_ramp_label_exists_degreeOneLift
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (gamma : ℝ → P.charts.Point)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma t)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    {sigma : ℝ → ℝ} (hsigma : Continuous sigma) (hmono : Monotone sigma)
    (hshift : ∀ x, sigma (x + curvePeriod) = sigma x + curvePeriod)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (htrace : ∀ x, A.map (annulusPoint x s) = gamma (sigma x)) :
    ∃ S : M64PeriodicDegreeOneLift, S.map = sigma := by
  obtain ⟨K, hK⟩ := monotone_period_shift_lipschitz_of_locallyLipschitz
    (show 0 < curvePeriod by unfold curvePeriod; positivity) hmono hshift
    (admitted_ramp_label_locallyLipschitz P t gamma hgamma hperiod hramp A hsigma hs htrace)
  refine ⟨{
    map := sigma
    monotone := hmono
    period_shift := hshift
    lipschitz_constant := K
    lipschitz_nonnegative := K.property
    lipschitz_on := ?_ }, rfl⟩
  intro x y
  simpa only [Real.dist_eq] using hK.dist_le_mul x y

end PoincareConjecture.M64
