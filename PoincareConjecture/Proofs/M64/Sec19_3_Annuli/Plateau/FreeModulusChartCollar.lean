import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusChartDisplacement
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LipschitzAnnulusAdapter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Topology Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareConjecture.M64

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem exists_chart_displaced_boundary_collar
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M}
    {cchart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hn : 3 ≤ n) {eps : ℝ} (heps : 0 < eps)
    {d c : ℝ → M}
    (hsourceD : ∀ x, d x ∈ cchart.source)
    (hsourceC : ∀ x, c x ∈ cchart.source)
    (hcoordD : ContDiff ℝ 1 (fun x => cchart (d x)))
    (hcoordC : ContDiff ℝ 1 (fun x => cchart (c x)))
    (hperiodD : Function.Periodic d curvePeriod)
    (hperiodC : Function.Periodic c curvePeriod)
    (hchartSymm : ContMDiffOn (𝓡 n) (𝓡 n) 1 cchart.symm cchart.target) :
    ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ < eps ∧
      (∀ x, cchart (c x) + v ∈ cchart.target) ∧
      Function.Periodic (fun x => cchart.symm (cchart (c x) + v)) curvePeriod ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1
        (fun x => cchart.symm (cchart (c x) + v)) ∧
      Disjoint (range d)
        (range (fun x => cchart.symm (cchart (c x) + v))) ∧
      ∃ A : M64Annulus g c
          (fun x => cchart.symm (cchart (c x) + v)),
        A.map = (fun p : Plane =>
          cchart.symm (cchart (c (p 0)) + (p 1) • v)) := by
  let uD : ℝ → EuclideanSpace ℝ (Fin n) := fun x => cchart (d x)
  let uC : ℝ → EuclideanSpace ℝ (Fin n) := fun x => cchart (c x)
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have huC : ContDiff ℝ 1 uC := hcoordC
  have hpuC : Function.Periodic uC curvePeriod := by
    intro x
    exact congrArg (fun z : M => cchart z) (hperiodC x)
  have huCtarget : ∀ x ∈ Icc (0 : ℝ) curvePeriod, uC x ∈ cchart.target := by
    intro x hx
    exact cchart.map_source (hsourceC x)
  obtain ⟨δ, hδ, hδε, hroom⟩ :=
    exists_translation_radius_subset_open cchart.open_target hP huC.continuous hpuC
      huCtarget heps
  obtain ⟨v, hv, hvtarget, hvperiod, -, hvregular, hvdisjoint⟩ :=
    exists_small_chart_displacement_disjoint hn hP hδ hsourceD hsourceC
      hcoordD hcoordC hperiodD hperiodC
  have hvsmall : ‖v‖ < eps := hv.trans_le hδε
  have hcprimeMD : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1
      (fun x => cchart.symm (cchart (c x) + v)) := by
    have hcoordCurve : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1
        (fun x => cchart (c x) + v) :=
      contMDiff_iff_contDiff.mpr hvregular
    exact hchartSymm.comp_contMDiff hcoordCurve hvtarget
  let coord : Plane → EuclideanSpace ℝ (Fin n) := fun p => uC (p 0) + (p 1) • v
  let F : Plane → M := fun p => cchart.symm (coord p)
  have hcoordDiff : ContDiff ℝ 1 coord := by
    dsimp [coord]
    fun_prop
  have hcoordT : ∀ p ∈ m64AnnulusDomain, coord p ∈ cchart.target := by
    intro p hp
    have hp1 : p 1 ∈ Icc (0 : ℝ) 1 := ⟨hp.2.2.1, hp.2.2.2⟩
    have hnorm : ‖(p 1) • v‖ < δ := by
      rw [norm_smul]
      have hpabs : |p 1| ≤ 1 := by
        rw [abs_of_nonneg hp1.1]
        exact hp1.2
      calc
        ‖p 1‖ * ‖v‖ ≤ 1 * ‖v‖ :=
          mul_le_mul_of_nonneg_right hpabs (norm_nonneg v)
        _ < δ := by simpa only [one_mul] using hv
    have h := hroom ((p 1) • v) hnorm (p 0)
    simpa only [coord] using h
  have hT : IsOpen (coord ⁻¹' cchart.target) := by
    exact cchart.open_target.preimage hcoordDiff.continuous
  have hcoordMD : ContMDiff (𝓡 2) (𝓡 n) 1 coord :=
    contMDiff_iff_contDiff.mpr hcoordDiff
  have hFMD : ContMDiffOn (𝓡 2) (𝓡 n) 1 F (coord ⁻¹' cchart.target) := by
    intro p hp
    apply ContMDiffAt.contMDiffWithinAt
    simpa only [F, Function.comp_def] using
      (hchartSymm.contMDiffAt (cchart.open_target.mem_nhds hp)).comp p
        hcoordMD.contMDiffAt
  have hFcont : ContinuousOn F m64AnnulusDomain := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    simpa only [F, Function.comp_def] using
      (cchart.continuousOn_symm.continuousAt
        (cchart.open_target.mem_nhds (hcoordT p hp))).comp
        hcoordDiff.continuous.continuousAt
  have hFperiod : ∀ x s : ℝ,
      F (annulusPoint (x + curvePeriod) s) = F (annulusPoint x s) := by
    intro x s
    change cchart.symm (uC (x + curvePeriod) + s • v) =
      cchart.symm (uC x + s • v)
    rw [hpuC x]
  have hFlower : ∀ x : ℝ, F (annulusPoint x 0) = c x := by
    intro x
    dsimp [F, coord, uC, annulusPoint]
    rw [zero_smul, add_zero, cchart.left_inv (hsourceC x)]
  have hFupper : ∀ x : ℝ,
      F (annulusPoint x 1) = cchart.symm (cchart (c x) + v) := by
    intro x
    dsimp [F, coord, uC, annulusPoint]
    rw [one_smul]
  have hlocal : ∀ x ∈ m64AnnulusDomain, ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x,
      ∀ y ∈ U, ∀ z ∈ U,
        g.edist (F y) (F z) ≤ (K : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖ := by
    intro x hx
    obtain ⟨K, U, hU, hK⟩ := m64_lipschitzOn_nhds_of_contMDiffAt g
      (hFMD.contMDiffAt (hT.mem_nhds (hcoordT x hx)))
    exact ⟨K, U, hU, hK⟩
  obtain ⟨K, hK⟩ := m64Annulus_hLip_of_local g hFcont hlocal
  have hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal) := by
    rw [← MeasureTheory.measure_congr m64AnnulusDomain_ae_eq_interior]
    exact m64AnnulusDomain_volume_ne_top
  obtain ⟨A, hAmap, -⟩ := m64Annulus_of_lipschitz g F hFcont hFperiod hFlower hFupper
    K.coe_nonneg (by simpa only [ENNReal.ofReal_coe_nnreal] using hK) hfinite
    (lt_add_one (∫ z in m64AnnulusDomain, m60AreaDensity g F z))
  refine ⟨v, hvsmall, hvtarget, hvperiod, hcprimeMD, hvdisjoint, A, ?_⟩
  exact hAmap

end PoincareConjecture.M64
