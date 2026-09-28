import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapInitialH2
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapSourceTransport
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapTargetEquation
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapNormalTrace

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Complex
open scoped ContDiff ENNReal Topology

namespace PoincareConjecture.M64.RampTransport

open M65Branch

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {n : ℕ}
local notation "Target" => EuclideanSpace ℝ (Fin (n + 1))

theorem harmonic_normal_chart_contDiffOn_two
    {g : RiemannianMetric (n + 1) Target} (D : LeviCivitaData g)
    {R : ℝ} (hR : 0 < R) {H : ℂ → Target}
    (hc : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}))
    (hs : ContDiffOn ℝ ∞ H (ball (0 : ℂ) R ∩ {z | 0 < z.im}))
    (h1 : MemLp (fun z => fderiv ℝ (complexGradient H) z 1) 2
      (volume.restrict (ball (0 : ℂ) R ∩ {z | 0 < z.im})))
    (hI : MemLp (fun z => fderiv ℝ (complexGradient H) z I) 2
      (volume.restrict (ball (0 : ℂ) R ∩ {z | 0 < z.im})))
    (heq : ∀ z ∈ ball (0 : ℂ) R ∩ {z | 0 < z.im},
      dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z))
    (Phi : OpenPartialHomeomorph Target Target)
    (hPhi : ContDiffOn ℝ ∞ Phi Phi.source) (hPsi : ContDiffOn ℝ ∞ Phi.symm Phi.target)
    (hHT : MapsTo H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) Phi.target)
    (ht : ∀ s : ℝ, |s| ≤ R → ∀ j : Fin (n + 1), j ≠ 0 → (Phi.symm (H (s : ℂ))) j = 0)
    (hn : ∀ s : ℝ, |s| ≤ R →
      (fderivWithin ℝ (Phi.symm ∘ H) (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im})
        (s : ℂ) I) 0 = 0) :
    ContDiffOn ℝ 2 H (closedBall (0 : ℂ) (R / 16) ∩ {z | 0 ≤ z.im}) := by
  let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
  let W := ball (0 : ℂ) R ∩ {z | 0 < z.im}
  let U := Phi.symm ∘ H
  let Gamma := M65Gauss.connectionCoefficient D
  have hW : IsOpen W := (M65StrictTrace.halfDisk_differential_domain hR).1
  have hWK : W ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  have hUc : ContDiffOn ℝ 1 U K := (hPsi.of_le (by simp)).comp hc hHT
  have hUs : ContDiffOn ℝ ∞ U W := hPsi.comp hs (fun _ hz => hHT (hWK hz))
  obtain ⟨hpc, hps, hpt, hpn⟩ := boundaryComplexCoordinates_mixed_data hR hUc hUs ht hn
  have hH2 := closedHalfDisk_coordinate_change_memWkp_two hR Phi.open_target hPsi hc hs hHT h1 hI
  have hGamma : ContDiffOn ℝ ∞ Gamma Phi.target :=
    (M65Gauss.contDiff_connectionCoefficient D).contDiffOn
  have hB (j : Fin (n + 1)) :
      ContDiffOn ℝ 2 (boundaryTargetQuadraticCoordinate Phi Gamma j) Phi.source :=
    (boundaryTargetQuadraticCoordinate_contDiffOn Phi hPhi hPsi hGamma j).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hPK (p : Plane) (hp : p ∈ boundaryClosedHalfBall R) : boundaryComplexCoordinates p ∈ K := by
    rw [← boundaryComplexCoordinates_preimage_closed] at hp
    exact hp
  have hPW (p : Plane) (hp : p ∈ boundaryHalfBall R) : boundaryComplexCoordinates p ∈ W := by
    rw [← boundaryComplexCoordinates_preimage_open] at hp
    exact hp
  have hup : ContDiffOn ℝ 2 (U ∘ boundaryComplexCoordinates)
      (boundaryClosedHalfBall (R / 16)) := by
    apply mixed_quadratic_halfBall_contDiffOn_two hR Phi.open_source hpc hps hH2 hB
      (fun p hp => Phi.map_target (hHT (hPK p hp))) hpn hpt
    intro j p hp
    have hHp := hs.contDiffAt (hW.mem_nhds (hPW p hp))
    exact boundaryTargetQuadraticCoordinate_equation Phi hPhi hPsi
      ((hHp.comp p boundaryComplexCoordinates.toContinuousLinearEquiv.contDiff.contDiffAt).of_le
        (WithTop.coe_le_coe.mpr le_top)) (hHT (hWK (hPW p hp)))
      (boundaryComplexCoordinates_harmonic_equation D hHp (heq _ (hPW p hp))) j
  have hu2 := contDiffOn_closedHalfDisk_of_boundaryComplexCoordinates hup
  have hsub : closedBall (0 : ℂ) (R / 16) ∩ {z | 0 ≤ z.im} ⊆ K := by
    intro z hz
    exact ⟨closedBall_subset_closedBall (by linarith : R / 16 ≤ R) hz.1, hz.2⟩
  have hmap : MapsTo U (closedBall (0 : ℂ) (R / 16) ∩ {z | 0 ≤ z.im}) Phi.source :=
    fun _ hz => Phi.map_target (hHT (hsub hz))
  apply ((hPhi.of_le (WithTop.coe_le_coe.mpr le_top)).comp hu2 hmap).congr
  intro z hz
  exact (Phi.right_inv (hHT (hsub hz))).symm

theorem harmonic_regular_trace_exists_closed_c2
    {g : RiemannianMetric (n + 1) Target} (D : LeviCivitaData g)
    {R : ℝ} (hR : 0 < R) {H : ℂ → Target}
    (hc : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}))
    (hs : ContDiffOn ℝ ∞ H (ball (0 : ℂ) R ∩ {z | 0 < z.im}))
    (h1 : MemLp (fun z => fderiv ℝ (complexGradient H) z 1) 2
      (volume.restrict (ball (0 : ℂ) R ∩ {z | 0 < z.im})))
    (hI : MemLp (fun z => fderiv ℝ (complexGradient H) z I) 2
      (volume.restrict (ball (0 : ℂ) R ∩ {z | 0 < z.im})))
    (heq : ∀ z ∈ ball (0 : ℂ) R ∩ {z | 0 < z.im},
      dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z))
    {c : ℝ → Target} {J : Set ℝ} (hJ : IsOpen J) (hcs : ContDiffOn ℝ ∞ c J)
    (hcv : ∀ t ∈ J, deriv c t ≠ 0) {sigma : ℝ → ℝ}
    (hsigma : ContDiff ℝ 1 sigma) (hsigma0 : sigma 0 ∈ J)
    (htrace : ∀ s : ℝ, |s| ≤ R → H (s : ℂ) = c (sigma s))
    (himm : ∀ s : ℝ, |s| ≤ R → Function.Injective
      (fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) (s : ℂ)))
    (hconf : ∀ s : ℝ, |s| ≤ R →
      g.inner (H (s : ℂ))
        (fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) (s : ℂ) 1)
        (fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) (s : ℂ) I) = 0) :
    ∃ d : ℝ, 0 < d ∧ d < R ∧
      ContDiffOn ℝ 2 H (closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) := by
  have hG : ContDiffOn ℝ ∞ g.euclideanCoefficients univ :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).contDiffOn
  obtain ⟨Phi, d, hd, hdR, _, hPhi, hPsi, hHT, _, _, hboundary⟩ :=
    exists_metric_normal_mixed_trace hR hc hs hJ hcs hsigma hsigma0 isOpen_univ
      g.euclideanCoefficients hG (mapsTo_univ _ _)
      (fun t ht => g.pos (c t) (deriv c t) (hcv t ht)) htrace himm hconf
  have hKsub : closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im} ⊆
      closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im} :=
    fun _ hz => ⟨closedBall_subset_closedBall hdR.le hz.1, hz.2⟩
  have hWsub : ball (0 : ℂ) d ∩ {z | 0 < z.im} ⊆
      ball (0 : ℂ) R ∩ {z | 0 < z.im} :=
    fun _ hz => ⟨ball_subset_ball hdR.le hz.1, hz.2⟩
  refine ⟨d / 16, by positivity, by linarith, ?_⟩
  exact harmonic_normal_chart_contDiffOn_two D hd (hc.mono hKsub) (hs.mono hWsub)
    (h1.mono_measure (Measure.restrict_mono_set volume hWsub))
    (hI.mono_measure (Measure.restrict_mono_set volume hWsub))
    (fun z hz => heq z (hWsub hz)) Phi hPhi hPsi hHT
    (fun s hs => (hboundary s hs).1) (fun s hs => (hboundary s hs).2)

end PoincareConjecture.M64.RampTransport
