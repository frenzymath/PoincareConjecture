import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialJacobiField
import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialGaugeDifferential
import PoincareConjecture.Proofs.M14.Sec6_3_GaugeFamilyNeighborhood
import PoincareConjecture.Proofs.M14.Sec6_3_JacobiGaugeSecond
import PoincareConjecture.Proofs.M14.Mathlib.ClosedParameterDerivative










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_zero_of_heq {q r : G.Point} (h : q = r)
    {v : G.Horizontal q} (hv : HEq v (0 : G.Horizontal r)) : v = 0 := by
  cases h
  exact eq_of_heq hv




theorem exponentialJacobiField_zero_of_coordinate_phase
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (Z W : G.Horizontal x)
    {b c : ℝ} (hb : (Z, b) ∈ E.domain) (hc : c ∈ Ioo 0 b)
    {U : Set ℝ} (hU : IsOpen U) (hzero : 0 ∈ U)
    (hsurv : ∀ r ∈ U, (Z + r • W, b) ∈ E.domain)
    (j : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
      G.gaugeCover.spatial j) {V : Set G.Point} (hV : IsOpen V)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift V)
    (hright : ∀ q ∈ V, (G.gaugeCover.cylinder j).toSpacetime (lift q) = q)
    (hcenter : E.gamma Z c ∈ V)
    (hcoordinate : deriv (fun r : ℝ => (lift (E.gamma (Z + r • W) c)).2.val) 0 = 0)
    (hvelocity : deriv (fun r : ℝ =>
      deriv (fun s => (lift (E.gamma (Z + r • W) s)).2.val) c) 0 = 0) :
    let Q := initialValuePath_differentialData hM04 hM12
      (exponentialInitialValuePath E Z b hb (hc.1.trans hc.2)) W
    Q.field c = 0 ∧ M14JacobiFirstDerivative Q c = 0 := by
  let P := exponentialInitialValuePath E Z b hb (hc.1.trans hc.2)
  let Q := initialValuePath_differentialData hM04 hM12 P W
  let γ := fun z : ℝ × ℝ => E.gamma (Z + z.1 • W) z.2
  have hγ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ γ
      (U ×ˢ Icc 0 b) :=
    (exponentialLine_contMDiffOn E Z W hsurv).comp
      (contMDiff_snd.prodMk contMDiff_fst).contMDiffOn (fun _ hz => ⟨hz.2, hz.1⟩)
  have hnear : γ ⁻¹' V ∈ 𝓝[U ×ˢ Icc 0 b] (0, c) :=
    (hγ.continuousOn (0, c) ⟨hzero, hc.1.le, hc.2.le⟩).preimage_mem_nhdsWithin
      (hV.mem_nhds (by simpa only [γ, zero_smul, add_zero] using hcenter))
  obtain ⟨N, hN, hzeroN, hNU, l, r, h0l, hlc, hcr, hrb, hmap, htime⟩ :=
    exists_open_closed_family_neighborhood hU hzero hc.1 hc.2.le hnear
  have hcr' : c < r := right_lt_of_Icc_mem_nhdsWithin hc.1.le hc.2 htime
  have hlr : l < r := hlc.trans hcr'
  have hcC : c ∈ Icc l r := ⟨hlc.le, hcr⟩
  have hcNear : Icc l r ∈ 𝓝 c := Icc_mem_nhds hlc hcr'
  have hC : M14SqrtParameterInterval 0 (b ^ 2) = Icc 0 b := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq (hc.1.trans hc.2).le]
  have hsub : Icc l r ⊆ M14SqrtParameterInterval 0 (b ^ 2) := by
    rw [hC]
    exact Icc_subset_Icc h0l.le hrb
  let β := lift ∘ γ
  have hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β
      (N ×ˢ Icc l r) :=
    hlift.comp (hγ.mono (prod_mono hNU (Icc_subset_Icc h0l.le hrb))) hmap
  let q := fun z : ℝ × ℝ => (β (z.2, z.1)).2.val
  have hq : ContDiffOn ℝ ∞ q (Icc l r ×ˢ N) := by
    have hval : ContMDiff (𝓡 n) (𝓡 n) ∞
        (Subtype.val : G.gaugeCover.spatial j → EuclideanSpace ℝ (Fin n)) :=
      contMDiff_subtype_val
    have h := hval.comp_contMDiffOn (fun z hz => (hβ z hz).snd)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    have hswap : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => (z.2, z.1)) (Icc l r ×ˢ N) :=
      (contDiff_snd.prodMk contDiff_fst).contDiffOn
    have hmem : MapsTo (fun z : ℝ × ℝ => (z.2, z.1)) (Icc l r ×ˢ N) (N ×ˢ Icc l r) :=
      fun _ hz => ⟨hz.2, hz.1⟩
    have hcomp := h.contDiffOn.comp hswap hmem
    exact hcomp
  let Y := fun s => fderiv ℝ (fun v => q (s, v)) 0 (1 : ℝ)
  have hY0 : Y c = 0 := fderiv_apply_one_eq_deriv.trans hcoordinate
  have hYd : derivWithin Y (Icc l r) c = 0 := by
    have h := (hasDerivWithinAt_parameterDerivative_Icc hlr hN q hq hcC hzeroN (1 : ℝ)).derivWithin
      (uniqueDiffOn_Icc hlr c hcC)
    have hv : (fun v => derivWithin (fun s => q (s, v)) (Icc l r) c) =
        (fun v => deriv (fun s => q (s, v)) c) :=
      funext (fun _ => derivWithin_of_mem_nhds hcNear)
    rw [hv, fderiv_apply_one_eq_deriv] at h
    exact h.trans hvelocity
  have hβ0 : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (fun s => β (0, s)) (Icc l r) :=
    hβ.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun _ hs => ⟨hzeroN, hs⟩)
  have hrecP (s : ℝ) (hs : s ∈ Icc l r) :
      (G.gaugeCover.cylinder j).toSpacetime (β (0, s)) = P.square_path.curve s := by
    have h := hright _ (hmap (show (0, s) ∈ N ×ˢ Icc l r from ⟨hzeroN, hs⟩))
    have hbase := exponential_square_curve_eq E Z hb (hc.1.trans hc.2) (hsub hs)
    have hbase' : γ (0, s) = P.square_path.curve s := by
      change E.gamma (Z + (0 : ℝ) • W) s = (E.square_path Z b hb (hc.1.trans hc.2)).curve s
      rw [zero_smul, add_zero]
      exact hbase.symm
    exact h.trans hbase'
  have hclock (s : ℝ) (hs : s ∈ Icc l r) : (β (0, s)).1.val = T - s ^ 2 :=
    ((G.gaugeCover.cylinder j).time_eq (β (0, s))).symm.trans
      ((congrArg G.spacetime.timeFunction (hrecP s hs)).trans
        (P.square_path.curve_time s (hsub hs)))
  have hfield (s : ℝ) (hs : s ∈ Icc l r) : HEq (Q.field s)
      ((G.gaugeCover.metric j).spatialTangentEquiv (β (0, s)).1 (β (0, s)).2 (Y s)) := by
    have hsurvS : (Z, s) ∈ E.domain :=
      (E.maximal_lifetime Z).out (E.domain_zero Z) hb ⟨h0l.le.trans hs.1, hs.2.trans hrb⟩
    have hp : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (fun v => β (v, s)) N :=
      hβ.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hv => ⟨hv, hs⟩)
    have hrec : (fun v : ℝ => E.gamma (Z + v • W) s) =ᶠ[𝓝 0]
        (fun v => (G.gaugeCover.cylinder j).toSpacetime (β (v, s))) := by
      filter_upwards [hN.mem_nhds hzeroN] with v hv
      exact (hright _ (hmap (show (v, s) ∈ N ×ˢ Icc l r from ⟨hv, hs⟩))).symm
    exact (exponentialJacobiField_heq_differential hM04 hM12 E Z W hb (hc.1.trans hc.2)
      (hsub hs) hsurvS).trans (exponentialLine_differential_gauge E Z W hsurvS j
        (fun v => β (v, s))
        ((hp.contMDiffAt (hN.mem_nhds hzeroN)).mdifferentiableAt (by simp)) hrec)
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  let F := Classical.choice (ordinaryGaugeWitness_nonempty j hCoordinates)
  have hR := P.square_path.smooth.mono P.square_path.interval_subset
  have hrestrict := horizontalCovariantDerivative_restrict_subset Q.extension hsub
    (uniqueDiffOn_Icc hlr c hcC) ((hR c (hsub hcC)).mdifferentiableWithinAt (by simp))
  have hfirst := (heq_of_eq hrestrict).trans
    (horizontalCovariantDerivative_lifted_gauge j hCoordinates F T (β (0, c)).2 hβ0 hrecP hclock
      (pullbackExtensionRestrict Q.extension hsub) Y hfield hcC (uniqueDiffOn_Icc hlr c hcC))
  have hvalue := hfield c hcC
  rw [hY0, map_zero] at hvalue
  rw [hY0, hYd, map_zero, zero_add, map_zero] at hfirst
  exact ⟨horizontal_zero_of_heq (hrecP c hcC).symm hvalue,
    horizontal_zero_of_heq (hrecP c hcC).symm hfirst⟩

end PoincareConjecture.M14
