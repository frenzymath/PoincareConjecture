import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryContinuous














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology InnerProductSpace

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)








theorem exists_annular_continuous_harmonic_potential :
    ∃ (H : Plane → ℝ) (u : H1Zero D scalarAnnulus),
      Continuous H ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
        (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact u : Plane → ℝ) ∧
      (∀ x ∈ scalarAnnulus, D.laplacian H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 1 → H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 2 → H x = 1) ∧
      ∀ v : H1Zero D scalarAnnulus,
        gradientEnergy D scalarAnnulus u v = boundaryForcing D scalarAnnulus
          annularBoundaryExtension annularBoundaryExtension_smooth
          annularBoundaryExtension_compact v := by
  obtain ⟨u, hforce, hboundary⟩ := exists_annular_boundary_continuous_correction D
  let q := annularBoundaryExtension
  let hq := annularBoundaryExtension_smooth
  let hqc := annularBoundaryExtension_compact
  let f := boundaryLaplacianL2 D q hq hqc
  have hfae : (f : Plane → ℝ) =ᵐ[g.volumeMeasure] D.laplacian q :=
    ((D.continuous_laplacian hq).memLp_of_hasCompactSupport
      (D.hasCompactSupport_laplacian hqc)).coeFn_toLp
  obtain ⟨W, hWs, hWae⟩ := M60.exists_smooth_poisson_representative
    (D := D) (by norm_num : 0 < 2) scalarAnnulus_isOpen u f (D.laplacian q)
    (D.contMDiff_laplacian hq) hfae hforce
  have hglobal : scalarAnnulus.indicator W =ᵐ[g.volumeMeasure]
      scalarAnnulus.indicator (toL2 D scalarAnnulus u : Plane → ℝ) := by
    filter_upwards [(ae_restrict_iff' scalarAnnulus_isOpen.measurableSet).mp hWae] with y hy
    by_cases hya : y ∈ scalarAnnulus
    · simp only [indicator_of_mem hya, hy hya]
    · simp only [indicator_of_notMem hya]
  let Z := scalarAnnulus.indicator W
  have hZc : Continuous Z := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ closure scalarAnnulus
    · obtain ⟨e, V, F, hxe, hxV, hV, hVc, hVs, he, hei, hflat, hF, hUF, hzero⟩ :=
        hboundary ⟨x, hx⟩
      let Half : Set Plane := {z | 0 < z 0}
      have hH : IsOpen Half := isOpen_lt continuous_const (by fun_prop)
      have hVH : IsOpen (V ∩ Half) := hV.inter hH
      have hcomp := (ae_restrict_iff' hVc.measurableSet).mp
        (g.ae_comp_on_compact e he hei hVc hVs hglobal)
      have hWFa : (fun z => W (e z)) =ᵐ[volume.restrict (V ∩ Half)] F := by
        filter_upwards [ae_restrict_of_ae hcomp, hUF, ae_restrict_mem hVH.measurableSet]
          with z hz hzF hzV
        have hze : e z ∈ scalarAnnulus :=
          (hflat z (hVs (subset_closure hzV.1))).mpr hzV.2
        have heq := hz (subset_closure hzV.1)
        simp only [indicator_of_mem hze] at heq
        exact heq.trans hzF
      have hWc : ContinuousOn (fun z => W (e z)) (V ∩ Half) :=
        hWs.continuousOn.comp
          (e.continuousOn.mono (fun z hz => hVs (subset_closure hz.1)))
          (fun z hz => (hflat z (hVs (subset_closure hz.1))).mpr hz.2)
      have hWF : EqOn (fun z => W (e z)) F (V ∩ Half) :=
        Measure.eqOn_open_of_ae_eq hWFa hVH hWc hF.continuousOn
      have hZF (z : Plane) (hz : z ∈ V) : Z (e z) = F z := by
        have hzs : z ∈ e.source := hVs (subset_closure hz)
        by_cases hzH : 0 < z 0
        · rw [show Z (e z) = W (e z) from indicator_of_mem ((hflat z hzs).mpr hzH) W]
          exact hWF ⟨hz, hzH⟩
        · have hzA : e z ∉ scalarAnnulus := fun h => hzH ((hflat z hzs).mp h)
          change scalarAnnulus.indicator W (e z) = F z
          rw [indicator_of_notMem hzA, hzero z (le_of_not_gt hzH)]
      have heiC : ContinuousAt e.symm x :=
        e.symm.continuousOn.continuousAt (e.open_target.mem_nhds hxe)
      have hZFe : Z =ᶠ[𝓝 x] (fun y => F (e.symm y)) := by
        filter_upwards [e.open_target.mem_nhds hxe,
          heiC.preimage_mem_nhds (hV.mem_nhds hxV)] with y hy hyV
        calc
          Z y = Z (e (e.symm y)) := by rw [e.right_inv hy]
          _ = F (e.symm y) := hZF (e.symm y) hyV
      exact (hF.continuousAt.comp heiC).congr_of_eventuallyEq hZFe
    · have hZzero : Z =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
        exact indicator_of_notMem (fun h => hy (subset_closure h)) W
      exact continuousAt_const.congr_of_eventuallyEq hZzero
  let H : Plane → ℝ := fun x => q x + Z x
  have hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus := by
    apply (hq.contMDiffOn.add hWs).congr
    intro x hx
    simp only [H, Z, indicator_of_mem hx, Pi.add_apply, q]
  have hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus q hq hqc u : Plane → ℝ) := by
    filter_upwards [hWae, ae_restrict_mem scalarAnnulus_isOpen.measurableSet,
      ae_restrict_of_ae (Lp.coeFn_add ((hq.continuous.memLp_of_hasCompactSupport hqc).toLp q)
        (toL2 D scalarAnnulus u)),
      ae_restrict_of_ae ((hq.continuous.memLp_of_hasCompactSupport hqc).coeFn_toLp)]
      with x hxW hx hxadd hxq
    change q x + Z x = _
    change _ = ((((hq.continuous.memLp_of_hasCompactSupport hqc).toLp q) +
      toL2 D scalarAnnulus u : Lp ℝ 2 g.volumeMeasure) : Plane → ℝ) x
    rw [hxadd, Pi.add_apply, hxq, show Z x = W x from indicator_of_mem hx W, hxW]
  refine ⟨H, u, hq.continuous.add hZc, hHs, hHae, ?_, ?_, ?_, hforce⟩
  · apply laplacian_zero_of_smooth_distribution D scalarAnnulus_isOpen hHs
    intro φ
    rw [integral_mul_eq_of_ae_eq_on scalarAnnulus_isOpen hHae
      ((D.tsupport_laplacian_subset φ).trans φ.support_subset)]
    have h := scalarPotential_laplacian_pairing D q hq hqc u φ
    rw [hforce, sub_self] at h
    simpa only [mul_comm] using h
  · intro x hx
    have hxA : x ∉ scalarAnnulus := by
      intro h
      have h1 := h.1
      rw [hx] at h1
      exact lt_irrefl _ h1
    change q x + scalarAnnulus.indicator W x = 0
    rw [indicator_of_notMem hxA, add_zero]
    exact annularBoundaryExtension_inner hx
  · intro x hx
    have hxA : x ∉ scalarAnnulus := by
      intro h
      have h2 := h.2
      rw [hx] at h2
      exact lt_irrefl _ h2
    change q x + scalarAnnulus.indicator W x = 1
    rw [indicator_of_notMem hxA, add_zero]
    exact annularBoundaryExtension_outer hx

end PoincareConjecture.M64Uniformization
