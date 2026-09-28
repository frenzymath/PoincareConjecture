import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarFluxPeriod















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ






def scalarCoverStrip : Set Cover := {z | z.1 ∈ Ioo (1 : ℝ) 2}






theorem scalarCoverStrip_isOpen : IsOpen scalarCoverStrip :=
  isOpen_Ioo.preimage continuous_fst






theorem scalarCoverStrip_convex : Convex ℝ scalarCoverStrip :=
  (convex_Ioo (1 : ℝ) 2).linear_preimage (LinearMap.fst ℝ ℝ ℝ)






def scalarCoverMap (z : Cover) : Plane := scalarCirclePoint z.1 z.2






theorem scalarCoverMap_smooth : ContDiff ℝ ∞ scalarCoverMap := by
  unfold scalarCoverMap scalarCirclePoint
  fun_prop






theorem scalarCoverMap_mem {z : Cover} (hz : z ∈ scalarCoverStrip) :
    scalarCoverMap z ∈ scalarAnnulus := by
  change 1 < ‖scalarCirclePoint z.1 z.2‖ ∧ ‖scalarCirclePoint z.1 z.2‖ < 2
  rw [scalarCirclePoint_norm, abs_of_pos (lt_trans zero_lt_one hz.1)]
  exact hz






theorem scalarCoverMap_periodic (z : Cover) :
    scalarCoverMap (z + (0, 1)) = scalarCoverMap z := by
  have hangle : 2 * Real.pi * (z.2 + 1) = 2 * Real.pi * z.2 + 2 * Real.pi := by ring
  simp [scalarCoverMap, scalarCirclePoint, hangle]

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)






def scalarCoverForm (H : Plane → ℝ) (z : Cover) : Cover →L[ℝ] ℝ :=
  (scalarConjugateForm D H (scalarCoverMap z)).comp (fderiv ℝ scalarCoverMap z)







theorem scalarCoverForm_smooth_closed {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0) :
    ContDiffOn ℝ ∞ (scalarCoverForm D H) scalarCoverStrip ∧
      ∀ z ∈ scalarCoverStrip, ∀ v w : Cover,
        fderiv ℝ (scalarCoverForm D H) z v w =
          fderiv ℝ (scalarCoverForm D H) z w v := by
  have hlocal (z : Cover) (hz : z ∈ scalarCoverStrip) :
      ∃ V : Cover → ℝ, ContDiff ℝ ∞ V ∧
        fderiv ℝ V =ᶠ[𝓝 z] scalarCoverForm D H := by
    obtain ⟨r, V, hr, -, hV, hdV⟩ := exists_local_annular_conjugate D hHs hlap
      (scalarCoverMap_mem hz)
    refine ⟨V ∘ scalarCoverMap, hV.comp scalarCoverMap_smooth, ?_⟩
    filter_upwards [scalarCoverMap_smooth.continuous.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (scalarCoverMap z) hr)] with y hy
    exact ((hdV _ hy).comp y
      (scalarCoverMap_smooth.differentiable (by simp) y).hasFDerivAt).fderiv
  constructor
  · intro z hz
    obtain ⟨V, hV, heq⟩ := hlocal z hz
    exact (((hV.fderiv_right (m := ∞) (by simp)).contDiffAt).congr_of_eventuallyEq
      heq.symm).contDiffWithinAt
  · intro z hz v w
    obtain ⟨V, hV, heq⟩ := hlocal z hz
    rw [← heq.fderiv_eq]
    exact (hV.contDiffAt.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)).eq v w






theorem scalarCoverForm_periodic (H : Plane → ℝ) (z : Cover) :
    scalarCoverForm D H (z + (0, 1)) = scalarCoverForm D H z := by
  have heq : (fun y : Cover => scalarCoverMap (y + (0, 1))) = scalarCoverMap :=
    funext scalarCoverMap_periodic
  have hd := ((scalarCoverMap_smooth.differentiable (by simp) (z + (0, 1))).hasFDerivAt.comp
    z ((hasFDerivAt_id z).add_const (0, 1))).fderiv
  simp only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id, heq] at hd
  simp only [scalarCoverForm, scalarCoverMap_periodic, ← hd]








theorem exists_annular_cover_conjugate {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0) :
    ∃ (V : Cover → ℝ) (P : ℝ),
      ContDiffOn ℝ ∞ V scalarCoverStrip ∧
      (∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z) ∧
      ∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P := by
  obtain ⟨hβs, hβclosed⟩ := scalarCoverForm_smooth_closed D hHs hlap
  obtain ⟨V, hdV⟩ := scalarCoverStrip_convex.exists_forall_hasFDerivAt_of_fderiv_symmetric
    scalarCoverStrip_isOpen (hβs.differentiableOn (by simp)) hβclosed
  have hVs : ContDiffOn ℝ ∞ V scalarCoverStrip := by
    rw [contDiffOn_infty_iff_fderiv_of_isOpen scalarCoverStrip_isOpen]
    refine ⟨fun z hz => (hdV z hz).differentiableAt.differentiableWithinAt, ?_⟩
    exact hβs.congr (fun z hz => (hdV z hz).fderiv)
  have hd (z : Cover) (hz : z ∈ scalarCoverStrip) :
      HasFDerivAt (fun y => V (y + (0, 1)) - V y) (0 : Cover →L[ℝ] ℝ) z := by
    have hshift : z + (0, 1) ∈ scalarCoverStrip := by simpa [scalarCoverStrip] using hz
    have h := ((hdV _ hshift).comp z ((hasFDerivAt_id z).add_const (0, 1))).sub (hdV z hz)
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id, scalarCoverForm_periodic,
      sub_self, Pi.sub_apply] using! h
  obtain ⟨P, hP⟩ := scalarCoverStrip_isOpen.exists_is_const_of_fderiv_eq_zero
    scalarCoverStrip_convex.isPreconnected
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).fderiv)
  refine ⟨V, P, hVs, hdV, fun z hz => ?_⟩
  have h := hP z hz
  linarith

end PoincareConjecture.M64Uniformization
