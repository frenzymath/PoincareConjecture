import PoincareConjecture.Proofs.M32.Cor11_36.Propagation
import PoincareConjecture.Proofs.M32.Cor11_36.Selector
import PoincareConjecture.Proofs.M32.Thm11_31.EndCutClosure

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32

private theorem inverse_sq_lt_half_of_le_half {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s / 2) : s⁻¹ ^ 2 < r⁻¹ ^ 2 / 2 := by
  have hs : 0 < s / 2 := hr.trans_le hrs
  have hi : (s / 2)⁻¹ ≤ r⁻¹ := (inv_le_inv₀ hs hr).2 hrs
  have heq : (s / 2)⁻¹ = 2 * s⁻¹ := by rw [inv_div]; ring
  rw [heq] at hi
  have hs0 : 0 < s := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * s⁻¹) hi 2
  have hpos := sq_pos_of_pos (inv_pos.mpr hr)
  nlinarith

theorem exists_deepHornScaleSelection_of_pointwiseHeight :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 / 200 ∧
      ∀ epsilon C analyticConstant : ℝ,
        terminalAccuracyFactor * epsilon ≤ tau → 0 < C →
        (∀ r₀ rho delta : ℝ, 0 < r₀ → 0 < rho → rho < r₀ → 0 < delta →
          ∃ h : ℝ, 0 < h ∧
            UniformDeepHornHeightAtRadius.{u} epsilon C analyticConstant r₀ rho delta h) →
        Nonempty (M32DeepHornScaleSelection.{u} epsilon C analyticConstant) := by
  obtain ⟨tau, htau, hsmall, hprop⟩ := exists_hornCut_propagation.{u}
  refine ⟨tau, htau, hsmall, ?_⟩
  intro epsilon C analyticConstant hepsilon hC hpointwise
  apply exists_deepHornScaleSelection_of_fixedRadiusIntervals hC
  intro r₀ rho delta hr₀ hrho hrhor₀ hdelta
  let b := rho / (2 * C)
  let r := min (rho / 2) (b / 2)
  let eta := min delta tau
  let alpha := max (terminalAccuracyFactor * epsilon) eta
  have hb : 0 < b := div_pos hrho (mul_pos (by norm_num) hC)
  have hr : 0 < r := lt_min (half_pos hrho) (half_pos hb)
  have hrhohalf : r ≤ rho / 2 := min_le_left _ _
  have hbhalf : r ≤ b / 2 := min_le_right _ _
  have hrrho : r < rho := hrhohalf.trans_lt (half_lt_self hrho)
  have heta : 0 < eta := lt_min hdelta htau
  have hetadelta : eta ≤ delta := min_le_left _ _
  have hetatau : eta ≤ tau := min_le_right _ _
  have hetaone : eta < 1 := hetatau.trans_lt (hsmall.trans_lt (by norm_num))
  have hetahalf : eta < 1 / 2 := hetatau.trans_lt (hsmall.trans_lt (by norm_num))
  have healpha : terminalAccuracyFactor * epsilon ≤ alpha := le_max_left _ _
  have hetaalpha : eta ≤ alpha := le_max_right _ _
  have halphatau : alpha ≤ tau := max_le hepsilon hetatau
  have hlow : rho⁻¹ ^ 2 < r⁻¹ ^ 2 / 2 := inverse_sq_lt_half_of_le_half hr hrhohalf
  have hboundary : b⁻¹ ^ 2 < r⁻¹ ^ 2 / 2 := inverse_sq_lt_half_of_le_half hr hbhalf
  obtain ⟨h0, hh0, hpoint⟩ := hpointwise r₀ r eta hr₀ hr (hrrho.trans hrhor₀) heta
  have hh0r : h0 < r := (hpoint.1.trans (min_le_left _ _)).trans_lt (by
    calc
      r * eta < r * 1 := mul_lt_mul_of_pos_left hetaone hr
      _ = r := mul_one r)
  refine ⟨h0, hh0, ?_⟩
  intro a ha hah0
  have hupper : a ≤ min (rho * delta) (rho / (2 * C)) :=
    hah0.trans (hpoint.1.trans (min_le_min
      (mul_le_mul hrrho.le hetadelta heta.le hrho.le)
      (div_le_div_of_nonneg_right hrrho.le (by positivity))))
  refine ⟨hupper, ?_⟩
  intro F T M _ _ _ _ _ _ _ _ H hcanonical he hconstant hanalytic Q horn hbound
  have hden : 0 < 2 * H.constant := mul_pos (by norm_num) H.constant_pos
  obtain ⟨D⟩ := hpoint.2 H hcanonical he hconstant hanalytic Q horn
    (hornBoundaryBelow_of_le (div_pos hr hden)
      (div_le_div_of_nonneg_right hrrho.le hden.le) hbound)
  by_cases heq : a = h0
  · subst a
    exact ⟨deepHornConclusion_mono D H.constant_pos hr hrrho.le heta hetadelta⟩
  have halt : a < h0 := lt_of_le_of_ne hah0 heq
  have hlevel : h0⁻¹ ^ 2 < a⁻¹ ^ 2 :=
    pow_lt_pow_left₀ ((inv_lt_inv₀ hh0 ha).2 halt)
      (inv_nonneg.mpr hh0.le) (by decide)
  obtain ⟨N0, hN0, hN0carrier, hR0, ⟨cut⟩⟩ := D.selected_neck
  have hclosure := hornCut_center_mem_closure horn N0 cut hetahalf hN0carrier
  have hcutH : cut.carrier ⊆ horn.carrier := by
    rw [cut.component_eq]
    exact (connectedComponentIn_subset _ _).trans sdiff_subset
  have hR0high : r⁻¹ ^ 2 < (Q.extension.extended.connection T).scalarCurvature N0.center := by
    rw [hR0]
    exact pow_lt_pow_left₀ ((inv_lt_inv₀ hr hh0).2 hh0r)
      (inv_nonneg.mpr hr.le) (by decide)
  let s := insert N0.center cut.carrier
  have hs : IsPreconnected s := by
    have hcut : IsPreconnected cut.carrier := by
      rw [cut.component_eq]
      exact isPreconnected_connectedComponentIn
    exact hcut.subset_closure (subset_insert _ _) (insert_subset hclosure subset_closure)
  have hsH : s ⊆ horn.carrier := insert_subset hN0 hcutH
  have hsR : ∀ z ∈ s, r⁻¹ ^ 2 <
      (Q.extension.extended.connection T).scalarCurvature z := by
    intro z hz
    rcases hz with rfl | hz
    · exact hR0high
    · exact lt_of_not_ge (fun hlowz => disjoint_left.mp cut.disjoint_low_curvature hz hlowz)
  have hboundary' : ∀ z ∈ horn.boundary_sphere,
      (Q.extension.extended.connection T).scalarCurvature z ≤ r⁻¹ ^ 2 / 2 := by
    intro z hz
    have hzbound := hbound z hz
    rw [hconstant] at hzbound
    exact hzbound.trans hboundary.le
  have healpha' : terminalAccuracyFactor * H.epsilon ≤ alpha := by
    simpa only [he] using healpha
  let seed := restrictNeckAccuracy N0 hetaalpha
  have hseed : Nonempty (HornEndCut horn seed rho) :=
    ⟨enlargeHornCutRadius (restrictHornCutAccuracy cut hetaalpha) hr hrrho.le⟩
  obtain ⟨x, hx, hxR⟩ := hornCut_exists_scalar_eq_of_mem_closure Q cut hclosure
    (by rw [hR0]; exact hlevel)
  obtain ⟨Nx, hNx, hNxcarrier⟩ := D.deep_neck x (hcutH hx) (by rw [hxR]; exact hlevel.le)
  have hNxs : (restrictNeckAccuracy Nx hetaalpha).center ∈ s := by
    change Nx.center ∈ s
    rw [hNx]
    exact mem_insert_of_mem _ hx
  obtain ⟨cutAlpha⟩ := hprop horn healpha' halphatau hlow.le hboundary' hs hsH hsR
    seed (by change N0.center ∈ insert N0.center cut.carrier; simp) hseed
      (restrictNeckAccuracy Nx hetaalpha) hNxs
  let cutEta := hornEndCut_of_centralSphere_eq horn
    (restrictNeckAccuracy Nx hetaalpha) Nx rfl cutAlpha
  refine ⟨{
    h_pos := ha
    h_upper := by simpa only [hconstant] using hupper
    deep_neck := ?_
    selected_neck := ?_ }⟩
  · intro y hy hRy
    obtain ⟨Ny, hNy, hNycarrier⟩ := D.deep_neck y hy (hlevel.le.trans hRy)
    exact ⟨restrictNeckAccuracy Ny hetadelta, hNy,
      (restrictNeckAccuracy_carrier_subset Ny hetadelta).trans hNycarrier⟩
  · refine ⟨restrictNeckAccuracy Nx hetadelta, ?_,
      (restrictNeckAccuracy_carrier_subset Nx hetadelta).trans hNxcarrier, ?_,
      ⟨restrictHornCutAccuracy cutEta hetadelta⟩⟩
    · change Nx.center ∈ horn.carrier
      rw [hNx]
      exact hcutH hx
    · change (Q.extension.extended.connection T).scalarCurvature Nx.center = a⁻¹ ^ 2
      rw [hNx]
      exact hxR

end PoincareConjecture.M32
