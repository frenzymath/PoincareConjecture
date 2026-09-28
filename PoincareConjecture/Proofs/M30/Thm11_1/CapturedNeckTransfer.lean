import PoincareConjecture.Proofs.M30.Thm11_1.CapturedNeckTransferErrors
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.PartialDiffeomorphPullback
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.VaryingScaleReadout
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.RawError
import PoincareConjecture.Proofs.Ch01.CurvatureConnection











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M30

open PoincareConjecture.M28.tube PoincareConjecture.Proofs.M28.NeckTransfer
open PoincareConjecture.Proofs.M28.NeckAnalysis PoincareConjecture.Proofs.M28.FiniteHessian

private theorem inverse_difference_tendsto_zero
    {R S : ℕ → ℝ} {a : ℝ} (ha : 0 < a) (hR : ∀ k, a ≤ R k)
    (hS : ∀ᶠ k in atTop, a / 2 ≤ S k)
    (herror : ∀ delta : ℝ, 0 < delta → ∀ᶠ k in atTop, |R k - S k| < delta) :
    Tendsto (fun k => (R k)⁻¹ - (S k)⁻¹) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro delta hdelta
  have hbudget : 0 < delta * (a ^ 2 / 2) := by positivity
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hS.and (herror _ hbudget))
  refine ⟨K, ?_⟩
  intro k hk
  have hRpos : 0 < R k := ha.trans_le (hR k)
  have hSpos : 0 < S k := (half_pos ha).trans_le (hK k hk).1
  have hden : a ^ 2 / 2 ≤ R k * S k := by
    have hh := mul_le_mul (hR k) (hK k hk).1 (half_pos ha).le hRpos.le
    nlinarith only [hh]
  have hinv : (R k)⁻¹ - (S k)⁻¹ = (S k - R k) / (R k * S k) := by
    field_simp [hRpos.ne', hSpos.ne']
  rw [Real.dist_eq, sub_zero, hinv, abs_div, abs_mul,
    abs_of_pos hRpos, abs_of_pos hSpos, abs_sub_comm]
  apply (div_lt_iff₀ (mul_pos hRpos hSpos)).mpr
  exact (hK k hk).2.trans_le (mul_le_mul_of_nonneg_left hden hdelta.le)






theorem eventually_exists_neck_of_captured_finite_metric_jets
    {M : Type v} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {X : ℕ → Type u} [∀ k, TopologicalSpace (X k)] [∀ k, T2Space (X k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X k)]
    [∀ k, IsManifold (𝓡 3) ∞ (X k)] {ι : Type w} [Finite ι]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (h : ∀ k, RiemannianMetric 3 (X k)) (Dsrc : ∀ k, LeviCivitaData (h k))
    {epsilon eta : ℝ} (hepsilon : 0 < epsilon) (hepseta : epsilon < eta)
    (heta : eta < 1 / 2) (horder : ⌊eta⁻¹⌋₊ + 1 ≤ ⌊epsilon⁻¹⌋₊)
    (U : Set M) (_hU : IsOpen U)
    (e : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) M (X k) ∞)
    (hsource : ∀ k, (e k).source = U)
    (N : ∀ k, EpsilonNeck (h k)) (heps : ∀ k, (N k).epsilon = epsilon)
    (K : Set M) (_hK : IsCompact K) (hKU : K ⊆ U)
    (hcapture : ∀ k, (N k).carrier ⊆ (e k) '' K)
    (a b : ℝ) (ha : 0 < a)
    (hscalar : ∀ k, a ≤ (Dsrc k).scalarCurvature (N k).center ∧
      (Dsrc k).scalarCurvature (N k).center ≤ b)
    (hscalarConv : TendstoUniformlyOn
      (fun k y => (Dsrc k).scalarCurvature (e k y)) D.scalarCurvature atTop K)
    (q : ι → M) (L : ι → Set (EuclideanSpace ℝ (Fin 3)))
    (hL : ∀ i, IsCompact (L i))
    (htarget : ∀ i, L i ⊆ (extChartAt (𝓡 3) (q i)).target)
    (_hLsource : ∀ i, (extChartAt (𝓡 3) (q i)).symm '' L i ⊆ U)
    (hcover : K ⊆ ⋃ i, (extChartAt (𝓡 3) (q i)).symm '' L i)
    (hjets : ∀ i r, r ≤ ⌊eta⁻¹⌋₊ + 1 → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r
        ((h k).pullbackCoefficients (e k ∘ (extChartAt (𝓡 3) (q i)).symm)))
      (iteratedFDeriv ℝ r (g.pullbackCoefficients (extChartAt (𝓡 3) (q i)).symm))
      atTop (L i)) :
    ∀ᶠ k in atTop, ∃ V : EpsilonNeck g,
      V.epsilon = eta ∧ V.center = (e k).symm (N k).center ∧
        V.connection = D ∧ V.coordinate_map = (e k).symm ∘ (N k).coordinate_map := by
  classical
  let m := ⌊eta⁻¹⌋₊
  let y := fun k => (e k).symm (N k).center
  let R := fun k => (Dsrc k).scalarCurvature (N k).center
  let S := fun k => D.scalarCurvature (y k)
  have hcap (k : ℕ) : (N k).carrier ⊆ (e k).target := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hcapture k hx
    exact (e k).map_source (by rw [hsource]; exact hKU hz)
  have hy (k : ℕ) : y k ∈ K := by
    obtain ⟨z, hz, heq⟩ := hcapture k
      ((N k).central_sphere_subset (N k).center_on_central_sphere)
    have hzy : (e k).symm (N k).center = z :=
      (congrArg (e k).symm heq).symm.trans
        ((e k).left_inv (by rw [hsource]; exact hKU hz))
    change (e k).symm (N k).center ∈ K
    exact hzy.symm ▸ hz
  have hforward (k : ℕ) : e k (y k) = (N k).center :=
    (e k).right_inv (hcap k ((N k).central_sphere_subset (N k).center_on_central_sphere))
  have herror : ∀ delta : ℝ, 0 < delta → ∀ᶠ k in atTop, |R k - S k| < delta := by
    intro delta hdelta
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hscalarConv delta hdelta] with k hk
    have hh := hk (y k) (hy k)
    simpa only [hforward, Real.dist_eq, abs_sub_comm, R, S] using hh
  have hRpos (k : ℕ) : 0 < R k := ha.trans_le (hscalar k).1
  have hb : 0 < b := (hRpos 0).trans_le (hscalar 0).2
  have hSbounds : ∀ᶠ k in atTop, a / 2 ≤ S k ∧ S k ≤ b + 1 := by
    filter_upwards [herror (min (a / 2) 1) (lt_min (half_pos ha) zero_lt_one)] with k hk
    have hh := abs_le.mp hk.le
    have hleft := min_le_left (a / 2) 1
    have hright := min_le_right (a / 2) 1
    constructor <;> linarith [(hscalar k).1, (hscalar k).2]
  have hNscale (k : ℕ) : (N k).scale ^ 2 = (R k)⁻¹ := by
    rw [(N k).scale_eq_scalar, (N k).connection.scalarCurvature_eq (Dsrc k)]
    dsimp only [R]
    rw [← Real.rpow_mul_natCast (hRpos k).le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
    rfl
  have hscales (k : ℕ) : b⁻¹ ≤ (N k).scale ^ 2 ∧ (N k).scale ^ 2 ≤ a⁻¹ := by
    rw [hNscale]
    exact ⟨inv_anti₀ (hRpos k) (hscalar k).2, inv_anti₀ ha (hscalar k).1⟩
  let c := fun k => (R k)⁻¹ - (S k)⁻¹
  have hc : Tendsto c atTop (𝓝 0) := inverse_difference_tendsto_zero ha
    (fun k => (hscalar k).1) (hSbounds.mono fun _ hk => hk.1) herror
  obtain ⟨delta, hdelta, hperturb⟩ :=
    exists_roundCylinderClose_perturbation_tolerance hepsilon hepseta
  obtain ⟨rho, hrho, hraw⟩ := exists_cylinder_raw_error_tolerance m hdelta
  let L0 := cylinderScalarCoordinateEquiv.symm.toContinuousLinearMap
  let F := (b + 1) * (max 1 ‖L0‖) ^ m
  have hF : 0 < F := mul_pos (by linarith)
    (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) m)
  have hbudget : 0 < rho / (2 * F) := div_pos hrho (mul_pos (by norm_num) hF)
  obtain ⟨Kmetric, hKmetric⟩ := CapturedNeckTransfer.exists_metric_error_tail
    g h e N hepsilon hepseta.le heta heps hsource hKU hcapture (inv_pos.mpr hb)
    hscales q L hL htarget hcover m horder hjets (rho / (2 * F)) hbudget
  let I := {z : ℕ × RoundCylinderSpace // z.2.2 ∈ Ioo (-eta⁻¹) eta⁻¹}
  have hs (i : I) : i.1.2.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    cylinderStrip_mono hepsilon hepseta.le i.2
  have hm : m ≤ ⌊epsilon⁻¹⌋₊ := (Nat.le_succ m).trans horder
  have hcoeff := hasUniformJetBoundsAt_cylinderNeckCoefficients (fun i : I => N i.1.1)
    hepsilon (by linarith) (fun i => heps i.1.1) m hm
    (fun i => i.1.2.1) (fun i => i.1.2.2) hs
  have hcoeffSmooth (i : I) : ContDiffAt ℝ ∞
      (cylinderNeckCoefficients (N i.1.1) i.1.2.1 i.1.2.2) 0 := by
    apply (contDiffOn_cylinderNeckCoefficients (N i.1.1) i.1.2.1 i.1.2.2).contDiffAt
    apply (isOpen_cylinderNeckChartDomain (N i.1.1) i.1.2.1 i.1.2.2).mem_nhds
    apply zero_mem_cylinderNeckChartDomain
    simpa only [heps] using hs i
  obtain ⟨Kscale, hKscale⟩ := hcoeff.exists_scalar_error_tail hcoeffSmooth hc
    (fun i => i.1.1) (rho / (2 * F)) hbudget
  filter_upwards [hSbounds, eventually_ge_atTop (max Kmetric Kscale)] with k hk hkK
  have hSpos : 0 < S k := (half_pos ha).trans_le hk.1
  let Neta := (N k).restrict_m28 eta (by rw [heps]; exact hepseta.le) heta
  have hcapEta : Neta.carrier ⊆ (e k).target := fun _ hx => hcap k hx.1
  let V : NeckGeometryCore g eta := pullbackNeckGeometry (e k) Neta hcapEta D hSpos
  have hVscale : V.scale = (S k) ^ (-1 / 2 : ℝ) := rfl
  have hVsq : V.scale ^ 2 = (S k)⁻¹ := by
    rw [hVscale, ← Real.rpow_mul_natCast hSpos.le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
  have hVinv : V.scale⁻¹ ^ 2 = S k := by
    rw [inv_pow, hVsq, inv_inv]
  let T : RoundCylinderTwoTensor := fun z v w => (N k).scale⁻¹ ^ 2 *
    roundCylinderPullback (h k) (N k).coordinate_map z v w
  have hsourceClose : RoundCylinderClose epsilon 0 T := by
    simpa only [heps] using (N k).metric_comparison.close
  have hclose : RoundCylinderClose eta 0 V.tensor := by
    apply hperturb 0 (by norm_num) V.tensor T hsourceClose V.tensor_smooth
    intro z hz
    apply hraw eta V.tensor T V.tensor_smooth
      (hsourceClose.1.mono_epsilon_m28 hepsilon hepseta.le) z hz
    intro r hr i j
    have hsN : z.2 ∈ Ioo (-(N k).epsilon⁻¹) (N k).epsilon⁻¹ := by
      rw [heps]
      exact cylinderStrip_mono hepsilon hepseta.le hz
    have hh := V.norm_frozen_difference_jet_le_of_scale_error
      (N k) 1 (by norm_num) z.1 hz hsN i j r
    have hlocal : V.coordinate_map ∘
        (cylinderSphereParametrization z.1 ∘ cylinderScalarCoordinates z.2) =
          capturedCylinderMap (e k) (N k) z.1 z.2 := by
      funext x
      rfl
    have hunit (f : EuclideanSpace ℝ (Fin 3) → X k) :
        RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric (h k) 1 (by norm_num)) f =
          (h k).pullbackCoefficients f := by
      funext x
      ext v w
      change 1 * (h k).pullbackCoefficients f x v w = _
      rw [one_mul]
    rw [hlocal, hunit, one_mul] at hh
    have hmetric := hKmetric k ((le_max_left _ _).trans hkK) z hz r hr
    have hscaleError : ‖iteratedFDeriv ℝ r (fun x =>
        ((N k).scale ^ 2 - V.scale ^ 2) • cylinderNeckCoefficients (N k) z.1 z.2 x) 0‖ ≤
          rho / (2 * F) := by
      simpa only [c, sub_zero, hNscale, hVsq] using
        hKscale ⟨(k, z), hz⟩ ((le_max_right _ _).trans hkK) r hr
    have hsum := add_le_add hmetric hscaleError
    have hbudgetEq : rho / (2 * F) + rho / (2 * F) = rho / F := by ring
    rw [hbudgetEq] at hsum
    have hpower : ‖L0‖ ^ r ≤ (max 1 ‖L0‖) ^ m :=
      (pow_le_pow_left₀ (norm_nonneg L0) (le_max_right _ _) r).trans
        (pow_le_pow_right₀ (le_max_left _ _) hr)
    have hfactor : V.scale⁻¹ ^ 2 * ‖L0‖ ^ r ≤ F := by
      rw [hVinv]
      exact mul_le_mul hk.2 hpower (pow_nonneg (norm_nonneg _) _) (by linarith)
    exact hh.trans ((mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _))).trans
        ((mul_le_mul_of_nonneg_right hfactor (div_pos hrho hF).le).trans_eq
          (mul_div_cancel₀ rho hF.ne')))
  exact ⟨V.toEpsilonNeck hclose, rfl, rfl, rfl, rfl⟩

end PoincareConjecture.M30
