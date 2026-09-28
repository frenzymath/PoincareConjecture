import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverPeriod















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)







def scalarCoverJacobian (H : Plane → ℝ) (z : Cover) : ℝ :=
  fderiv ℝ (H ∘ scalarCoverMap) z (1, 0) * scalarCoverForm D H z (0, 1) -
    fderiv ℝ (H ∘ scalarCoverMap) z (0, 1) * scalarCoverForm D H z (1, 0)






def scalarCoverWeightedFlux (H : Plane → ℝ) (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, H (scalarCoverMap (r, t)) * scalarCoverForm D H (r, t) (0, 1)

private theorem product_form_derivative {U : Cover → ℝ} {beta : Cover → Cover →L[ℝ] ℝ}
    {z : Cover} (hU : DifferentiableAt ℝ U z) (hbeta : DifferentiableAt ℝ beta z)
    (a b : Cover) :
    fderiv ℝ (fun y => U y * beta y b) z a =
      fderiv ℝ U z a * beta z b + U z * fderiv ℝ beta z a b := by
  change fderiv ℝ (U * fun y => beta y b) z a = _
  rw [fderiv_mul hU (hbeta.clm_apply (differentiableAt_const b)),
    fderiv_clm_apply hbeta (differentiableAt_const b)]
  have hconst : fderiv ℝ (fun _ : Cover => b) z = 0 := (hasFDerivAt_const b z).fderiv
  rw [hconst]
  simp only [ContinuousLinearMap.comp_zero, zero_add,
    add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.flip_apply]
  ring






theorem scalarCoverPotential_smooth {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus) :
    ContDiffOn ℝ ∞ (H ∘ scalarCoverMap) scalarCoverStrip :=
  (contMDiffOn_iff_contDiffOn.mp hHs).comp scalarCoverMap_smooth.contDiffOn
    (fun _ hz => scalarCoverMap_mem hz)







theorem scalarCover_green_identity {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    {r s : ℝ} (hr : r ∈ Ioo (1 : ℝ) 2) (hs : s ∈ Ioo (1 : ℝ) 2) (hrs : r ≤ s) :
    (∫ z in Icc (r, (0 : ℝ)) (s, 1), scalarCoverJacobian D H z) =
      scalarCoverWeightedFlux D H s - scalarCoverWeightedFlux D H r := by
  let U := H ∘ scalarCoverMap
  let beta := scalarCoverForm D H
  let A : Cover → ℝ := fun z => U z * beta z (0, 1)
  let B : Cover → ℝ := fun z => -(U z * beta z (1, 0))
  have hUs : ContDiffOn ℝ ∞ U scalarCoverStrip := scalarCoverPotential_smooth hHs
  obtain ⟨hbs, hbclosed⟩ := scalarCoverForm_smooth_closed D hHs hlap
  have hAs : ContDiffOn ℝ ∞ A scalarCoverStrip := hUs.mul (hbs.clm_apply contDiffOn_const)
  have hBs : ContDiffOn ℝ ∞ B scalarCoverStrip :=
    (hUs.mul (hbs.clm_apply contDiffOn_const)).neg
  have hband : Icc (r, (0 : ℝ)) (s, 1) ⊆ scalarCoverStrip := by
    intro z hz
    exact ⟨hr.1.trans_le hz.1.1, hz.2.1.trans_lt hs.2⟩
  have hinterior : Ioo r s ×ˢ Ioo (0 : ℝ) 1 ⊆ scalarCoverStrip := by
    intro z hz
    exact ⟨hr.1.trans hz.1.1, hz.1.2.trans hs.2⟩
  have hdiv (z : Cover) (hz : z ∈ scalarCoverStrip) :
      fderiv ℝ A z (1, 0) + fderiv ℝ B z (0, 1) = scalarCoverJacobian D H z := by
    have hUd := (hUs.contDiffAt (scalarCoverStrip_isOpen.mem_nhds hz)).differentiableAt
      (by simp)
    have hbd := (hbs.contDiffAt (scalarCoverStrip_isOpen.mem_nhds hz)).differentiableAt
      (by simp)
    have hneg : fderiv ℝ (fun y => -(U y * beta y (1, 0))) z =
        -fderiv ℝ (fun y => U y * beta y (1, 0)) z := fderiv_neg
    change fderiv ℝ A z (1, 0) + fderiv ℝ (fun y => -(U y * beta y (1, 0))) z (0, 1) = _
    rw [hneg]
    change fderiv ℝ (fun y => U y * beta y (0, 1)) z (1, 0) -
      fderiv ℝ (fun y => U y * beta y (1, 0)) z (0, 1) = _
    rw [product_form_derivative hUd hbd, product_form_derivative hUd hbd,
      hbclosed z hz (1, 0) (0, 1)]
    dsimp only [scalarCoverJacobian, U, beta]
    ring
  have hint : IntegrableOn
      (fun z => fderiv ℝ A z (1, 0) + fderiv ℝ B z (0, 1)) (Icc (r, (0 : ℝ)) (s, 1)) :=
    ((((hAs.continuousOn_fderiv_of_isOpen scalarCoverStrip_isOpen (by simp)).clm_apply
      continuousOn_const).add
      ((hBs.continuousOn_fderiv_of_isOpen scalarCoverStrip_isOpen (by simp)).clm_apply
        continuousOn_const)).mono hband).integrableOn_compact isCompact_Icc
  have hgreen := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    A B (fderiv ℝ A) (fderiv ℝ B) (r, (0 : ℝ)) (s, 1) ⟨hrs, zero_le_one⟩
    (hAs.continuousOn.mono hband) (hBs.continuousOn.mono hband)
    (fun z hz => ((hAs.contDiffAt
      (scalarCoverStrip_isOpen.mem_nhds (hinterior hz))).differentiableAt (by simp)).hasFDerivAt)
    (fun z hz => ((hBs.contDiffAt
      (scalarCoverStrip_isOpen.mem_nhds (hinterior hz))).differentiableAt (by simp)).hasFDerivAt)
    hint
  have hside : (fun t : ℝ => B (t, 1)) = fun t => B (t, 0) := by
    funext t
    have hp := scalarCoverMap_periodic (t, 0)
    have hb := scalarCoverForm_periodic D H (t, 0)
    norm_num only [Prod.mk_add_mk, add_zero, zero_add] at hp hb
    change -(H (scalarCoverMap (t, 1)) * scalarCoverForm D H (t, 1) (1, 0)) =
      -(H (scalarCoverMap (t, 0)) * scalarCoverForm D H (t, 0) (1, 0))
    rw [hp, hb]
  simp only [hside, sub_self, zero_add] at hgreen
  calc
    _ = ∫ z in Icc (r, (0 : ℝ)) (s, 1), fderiv ℝ A z (1, 0) + fderiv ℝ B z (0, 1) := by
      apply setIntegral_congr_fun measurableSet_Icc
      exact fun z hz => (hdiv z (hband hz)).symm
    _ = _ := hgreen

end PoincareConjecture.M64Uniformization
