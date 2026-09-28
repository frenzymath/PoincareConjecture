import PoincareConjecture.Proofs.M47.TerminalCurvatureCompactCoefficients
import PoincareConjecture.Proofs.M47.TerminalCurvatureInverseChart
import PoincareConjecture.Proofs.M47.TerminalCurvatureMovingNeckImage
import PoincareConjecture.Proofs.M47.TerminalCurvatureChartScalar
import PoincareConjecture.Proofs.M47.TerminalCurvatureScalarNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

open M34 SpacetimeBounds SpacetimeBounds.Bootstrap

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilinear" => E →L[ℝ] E →L[ℝ] ℝ

theorem terminalCurvature_eventually_image_neck_on_finite_cover
    {ι : Type*} [Finite ι] [Nonempty ι]
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
    (g : ∀ k, RiemannianMetric 3 (M k)) (h : RiemannianMetric 3 X)
    (D : LeviCivitaData h)
    (psi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) (M k) X ∞)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (K : ι → Set E) (hK : ∀ i, IsCompact (K i))
    (hKtarget : ∀ i, K i ⊆ (c i).target)
    (hsource : ∀ i, ∀ᶠ k in atTop, K i ⊆ ((psi k).trans (c i)).target)
    (hjet : ∀ i j, TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j ((g k).pullbackCoefficients
        ((psi k).trans (c i)).symm))
      (iteratedFDeriv ℝ j (h.pullbackCoefficients (c i).symm)) atTop (K i))
    {epsilon L H : ℝ} (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2)
    (hL : 0 < L) :
    ∀ᶠ k in atTop, ∀ N : EpsilonNeck (g k), N.epsilon = epsilon →
      L ≤ N.connection.scalarCurvature N.center →
      N.connection.scalarCurvature N.center ≤ H →
      N.carrier ⊆ (psi k).source →
      (∀ z ∈ N.carrier, ∃ i, psi k z ∈ (c i).source ∧ c i (psi k z) ∈ K i) →
      ∃ W : EpsilonNeck h,
        W.epsilon = 2 * epsilon ∧ W.center = psi k N.center ∧ W.connection = D ∧
        W.carrier = psi k '' N.region (-(2 * epsilon)⁻¹) (2 * epsilon)⁻¹ ∧
        W.coordinate_map = psi k ∘ N.coordinate_map := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let m := Nat.floor (2 * epsilon)⁻¹
  let B0 : ι → E → Bilinear := fun i => h.pullbackCoefficients (c i).symm
  let B : ι → ℕ → E → Bilinear := fun i k =>
    (g k).pullbackCoefficients ((psi k).trans (c i)).symm
  have hsmooth (i : ι) : ContDiffOn ℝ ∞ (B0 i) (c i).target := by
    intro x hx
    exact (h.contDiffAt_pullbackCoefficients
      ((c i).contMDiffOn_invFun.contMDiffAt
        ((c i).open_target.mem_nhds hx))).contDiffWithinAt
  have hpos (i : ι) (x : E) (hx : x ∈ K i) (v : E) (hv : v ≠ 0) :
      0 < B0 i x v v := by
    have hlocal := (c i).symm.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hKtarget i hx)
    have hinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3) (c i).symm x) :=
      (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective
    apply h.pos
    intro hz
    apply hv
    apply hinj
    rw [map_zero]
    convert! hz using 1
  have hinv (i : ι) (x : E) (hx : x ∈ (c i).target) : (B0 i x).IsInvertible := by
    have hlocal := (c i).symm.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hx
    exact h.isInvertible_pullbackCoefficients
      (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective
  have hbounds (i : ι) := terminalCurvature_eventually_compact_coefficient_bounds
    (c i).open_target (hK i) (hKtarget i) (hsmooth i) (hpos i) (m + 1)
    (fun j _ => hjet i j)
  choose b hb C hC hbounds using hbounds
  let bmin : ℝ := Finset.univ.inf' Finset.univ_nonempty b
  have hbmin : 0 < bmin := (Finset.lt_inf'_iff _).mpr (fun i _ => hb i)
  have hbminle (i : ι) : bmin ≤ b i := Finset.inf'_le b (Finset.mem_univ i)
  obtain ⟨C0, hC0⟩ := Finite.exists_le C
  let Cmax := max 1 C0
  have hCmax : 1 ≤ Cmax := le_max_left _ _
  have hCle (i : ι) : C i ≤ Cmax := (hC0 i).trans (le_max_right _ _)
  let A := max 1 H
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  let bound := max Cmax (A * Cmax)
  have hbound : 1 ≤ bound := hCmax.trans (le_max_left _ _)
  obtain ⟨delta, hdelta, sigma, hsigma, _, himage⟩ :=
    terminalCurvature_exists_moving_neck_image_tolerance.{u, v}
      hepsilon hsmall (mul_pos hL hbmin) hbound
  let eta := delta / (A + 1)
  have heta : 0 < eta := div_pos hdelta (by positivity)
  have hsmallError : A * eta ≤ delta := by
    have heq : (A + 1) * eta = delta := by dsimp only [eta]; field_simp
    nlinarith
  have herrors : ∀ᶠ k in atTop, ∀ i, ∀ j : Fin (m + 1), ∀ x ∈ K i,
      ‖iteratedFDeriv ℝ (j : ℕ) (B i k) x -
        iteratedFDeriv ℝ (j : ℕ) (B0 i) x‖ ≤ eta := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hjet i j)) eta heta]
      with k hk x hx
    have he := hk x hx
    rw [dist_comm, dist_eq_norm] at he
    exact he.le
  have hscalar : ∀ᶠ k in atTop, ∀ i, ∀ x ∈ K i,
      |scalarTwoJet (metricTwoJet (B i k) x) -
        scalarTwoJet (metricTwoJet (B0 i) x)| < sigma * L := by
    apply Filter.eventually_all.mpr
    intro i
    exact terminalCurvature_eventually_uniform_scalar_jet_error
      (c i).open_target (hK i) (hKtarget i) (hsmooth i) (hinv i)
      (fun j _ => hjet i j) (mul_pos hsigma hL)
  filter_upwards [Filter.eventually_all.mpr hbounds, Filter.eventually_all.mpr hsource,
    herrors, hscalar] with k hkbound hksource hkerror hkscalar N hN hlo hhi hNsource hcover
  have hscale := terminalCurvature_neck_scale_window N hL hlo hhi
  have hscaleA : N.scale⁻¹ ^ 2 ≤ A := hscale.2.1.trans (le_max_right _ _)
  have hscale0 : 0 ≤ N.scale⁻¹ ^ 2 := sq_nonneg _
  apply himage (M k) X (g k) h N hN D (psi k) hNsource ?_ ?_
  · intro q s hs
    have hinvE : (2 * epsilon)⁻¹ ≤ epsilon⁻¹ := inv_anti₀ hepsilon (by linarith)
    have hsold : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      rw [hN]
      exact ⟨(neg_le_neg hinvE).trans_lt hs.1, hs.2.trans_le hinvE⟩
    have hz : N.coordinate_map (q, s) ∈ N.carrier :=
      N.coordinate_map_mem_of_axial_mem hsold
    obtain ⟨i, hi, hxi⟩ := hcover _ hz
    let ci := (psi k).trans (c i)
    have hci : N.coordinate_map (q, s) ∈ ci.source := ⟨hNsource hz, hi⟩
    have hx : ci (N.coordinate_map (q, s)) ∈ K i := hxi
    have hxt : ci (N.coordinate_map (q, s)) ∈ ci.target := ci.map_source hci
    obtain ⟨hcoord, hjets, hlow⟩ := hkbound i _ hx
    have hsB := (g k).contDiffAt_pullbackCoefficients
      (ci.contMDiffOn_invFun.contMDiffAt (ci.open_target.mem_nhds hxt))
    refine ⟨ci, hci, hcoord.trans ((hCle i).trans (le_max_left _ _)), ?_, ?_, ?_⟩
    · intro j hj
      have hscaleJet : iteratedFDeriv ℝ j
          (fun y => N.scale⁻¹ ^ 2 • (g k).pullbackCoefficients ci.symm y)
          (ci (N.coordinate_map (q, s))) = N.scale⁻¹ ^ 2 •
          iteratedFDeriv ℝ j ((g k).pullbackCoefficients ci.symm)
            (ci (N.coordinate_map (q, s))) :=
        iteratedFDeriv_const_smul_apply' (hsB.of_le (by exact_mod_cast le_top))
      rw [terminalCurvature_scaled_pullback_coefficients, hscaleJet,
        norm_smul, Real.norm_of_nonneg hscale0]
      exact (mul_le_mul hscaleA ((hjets j hj).trans (hCle i))
        (norm_nonneg _) hA.le).trans (le_max_right _ _)
    · intro v
      change (L * bmin) * ‖v‖ ^ 2 ≤ N.scale⁻¹ ^ 2 * B i k (ci _) v v
      calc
        _ = L * (bmin * ‖v‖ ^ 2) := by ring
        _ ≤ L * (b i * ‖v‖ ^ 2) := by gcongr; exact hbminle i
        _ ≤ N.scale⁻¹ ^ 2 * (b i * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hscale.1 (mul_nonneg (hb i).le (sq_nonneg _))
        _ ≤ _ := mul_le_mul_of_nonneg_left (hlow v) hscale0
    · intro j hj
      rw [terminalCurvature_inverse_chart_error_jet (g k) h (psi k) (c i) hxt,
        norm_smul, Real.norm_of_nonneg hscale0, norm_sub_rev]
      exact (mul_le_mul hscaleA (hkerror i ⟨j, by omega⟩ _ hx)
        (norm_nonneg _) hA.le).trans hsmallError
  · have hz : N.center ∈ N.carrier :=
      N.central_sphere_subset N.center_on_central_sphere
    obtain ⟨i, hi, hxi⟩ := hcover N.center hz
    have hci : N.center ∈ ((psi k).trans (c i)).source := ⟨hNsource hz, hi⟩
    have herr := hkscalar i _ hxi
    have hi0 : (c i).symm (c i (psi k N.center)) = psi k N.center := (c i).left_inv hi
    have hik : ((psi k).trans (c i)).symm (c i (psi k N.center)) = N.center :=
      ((psi k).trans (c i)).left_inv hci
    change |scalarTwoJet (metricTwoJet ((g k).pullbackCoefficients
      ((psi k).trans (c i)).symm) _) -
      scalarTwoJet (metricTwoJet (h.pullbackCoefficients (c i).symm) _)| < sigma * L at herr
    rw [terminalCurvature_partial_chart_scalar N.connection _ (hksource i hxi),
      terminalCurvature_partial_chart_scalar D _ (hKtarget i hxi), hik, hi0] at herr
    apply terminalCurvature_neck_normalization_error N hsigma.le hlo
    exact (abs_sub_comm _ _).trans_le herr.le

end PoincareConjecture.M47
