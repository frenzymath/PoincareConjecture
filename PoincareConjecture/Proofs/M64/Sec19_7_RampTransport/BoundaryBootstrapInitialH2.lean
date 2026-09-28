import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapCoordinateChange
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapHalfBall

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Complex
open scoped ContDiff ENNReal Topology

namespace PoincareConjecture.M64.RampTransport

open M65Branch
open Poincare.Analysis.Sobolev.Euclidean (MemWkp)

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {m n : ℕ}
local notation "Source" => EuclideanSpace ℝ (Fin m)
local notation "Target" => EuclideanSpace ℝ (Fin n)

theorem closedHalfDisk_coordinate_change_memWkp_two
    {R : ℝ} (hR : 0 < R) {H : ℂ → Source} {F : Source → Target} {T : Set Source}
    (hT : IsOpen T) (hF : ContDiffOn ℝ ∞ F T)
    (hc : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}))
    (hs : ContDiffOn ℝ ∞ H (ball (0 : ℂ) R ∩ {z | 0 < z.im}))
    (hHT : MapsTo H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) T)
    (h1 : MemLp (fun z => fderiv ℝ (complexGradient H) z 1) 2
      (volume.restrict (ball (0 : ℂ) R ∩ {z | 0 < z.im})))
    (hI : MemLp (fun z => fderiv ℝ (complexGradient H) z I) 2
      (volume.restrict (ball (0 : ℂ) R ∩ {z | 0 < z.im}))) :
    ∀ j, MemWkp 2 2 (fun p => (F (H (boundaryComplexCoordinates p))) j) (boundaryHalfBall R) := by
  let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
  let W := ball (0 : ℂ) R ∩ {z | 0 < z.im}
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) R).inter_right
    (isClosed_le continuous_const continuous_im)
  have hW : IsOpen W := (M65StrictTrace.halfDisk_differential_domain hR).1
  have hWK : W ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  have hKD : UniqueDiffOn ℝ K := (M65StrictTrace.halfDisk_differential_domain hR).2.2.1
  have hfinite : volume W < ⊤ := lt_of_le_of_lt (measure_mono hWK) hK.measure_lt_top
  let : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.mpr hfinite.ne
  have hD : ContinuousOn (fderivWithin ℝ H K) K := hc.continuousOn_fderivWithin hKD le_rfl
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hD
  have hDactual (z : ℂ) (hz : z ∈ W) : fderiv ℝ H z = fderivWithin ℝ H K z := by
    rw [fderivWithin_of_mem_nhds (mem_of_superset (hW.mem_nhds hz) hWK)]
  have hcolBound (v : ℂ) (hv : ‖v‖ = 1) (z : ℂ) (hz : z ∈ W) :
      ‖fderiv ℝ H z v‖ ≤ A := by
    rw [hDactual z hz]
    exact ((fderivWithin ℝ H K z).le_opNorm v).trans
      (by simpa only [hv, mul_one] using hA z (hWK hz))
  have hcolLp (v : ℂ) (hv : ‖v‖ = 1) :
      MemLp (fun z => fderiv ℝ H z v) 2 (volume.restrict W) := by
    have hcont : ContinuousOn (fun z => fderiv ℝ H z v) W :=
      (hs.continuousOn_fderiv_of_isOpen hW (by simp)).clm_apply continuousOn_const
    apply MemLp.mono_exponent (q := ⊤) _ le_top
    apply memLp_top_of_bound (hcont.aestronglyMeasurable hW.measurableSet) A
    filter_upwards [ae_restrict_mem hW.measurableSet] with z hz
    exact hcolBound v hv z hz
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hHLp : MemLp H 2 (volume.restrict W) := by
    apply MemLp.mono_exponent (q := ⊤) _ le_top
    apply memLp_top_of_bound (hs.continuousOn.aestronglyMeasurable hW.measurableSet) C
    filter_upwards [ae_restrict_mem hW.measurableSet] with z hz
    exact hC z (hWK hz)
  have hbase := boundaryComplexCoordinates_memWkp_two hW hs hHLp
    (hcolLp 1 (by simp)) (hcolLp I (by simp)) h1 hI
  have hpre : boundaryComplexCoordinates ⁻¹' W = boundaryHalfBall R :=
    boundaryComplexCoordinates_preimage_open R
  rw [hpre] at hbase
  have hPK (p : Plane) (hp : p ∈ boundaryHalfBall R) : boundaryComplexCoordinates p ∈ K :=
    hWK (show boundaryComplexCoordinates p ∈ W from by rw [← hpre] at hp; exact hp)
  have hPW (p : Plane) (hp : p ∈ boundaryHalfBall R) : boundaryComplexCoordinates p ∈ W := by
    rw [← hpre] at hp
    exact hp
  have hps : ContDiffOn ℝ ∞ (H ∘ boundaryComplexCoordinates) (boundaryHalfBall R) := by
    rw [← hpre]
    exact boundaryComplexCoordinates.toContinuousLinearEquiv.contDiffOn_comp_iff.mpr hs
  have hgeom := boundaryHalfBall_geometry hR
  have hpfinite : volume (boundaryHalfBall R) < ⊤ :=
    lt_of_le_of_lt (measure_mono subset_closure) (by
      rw [hgeom.2.2.2.2]
      exact hgeom.2.2.1.measure_lt_top)
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn
    (hF.continuousOn.comp hc.continuousOn hHT)
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn
    ((hF.continuousOn_fderiv_of_isOpen hT (by simp)).comp hc.continuousOn hHT)
  have hDF1 : ContDiffOn ℝ 1 (fderiv ℝ F) T :=
    hF.fderiv_of_isOpen hT (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn
    ((hDF1.continuousOn_fderiv_of_isOpen hT le_rfl).comp hc.continuousOn hHT)
  apply coordinate_change_memWkp_two (A := A) hgeom.1 hpfinite hT hps hbase hF
    (fun p hp => hHT (hPK p hp))
    (fun p hp => hC0 _ (hPK p hp)) (fun p hp => hC1 _ (hPK p hp))
    (fun p hp => hC2 _ (hPK p hp))
  intro i p hp
  change ‖fderiv ℝ (H ∘ boundaryComplexCoordinates) p (EuclideanSpace.single i 1)‖ ≤ A
  have hd : fderiv ℝ (H ∘ boundaryComplexCoordinates) p =
      (fderiv ℝ H (boundaryComplexCoordinates p)).comp
        boundaryComplexCoordinates.toContinuousLinearEquiv.toContinuousLinearMap :=
    boundaryComplexCoordinates.toContinuousLinearEquiv.comp_right_fderiv
  rw [hd]
  change ‖fderiv ℝ H (boundaryComplexCoordinates p)
    (boundaryComplexCoordinates (EuclideanSpace.single i 1))‖ ≤ A
  exact hcolBound _ (by simp) _ (hPW p hp)

end PoincareConjecture.M64.RampTransport
