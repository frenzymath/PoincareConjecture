import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryClassicalGradient
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryValues













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => Set.preimage (fun p : Plane => p 0) (Ioi (0 : ℝ))

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)







theorem annular_potential_boundary_differential
    (u : H1Zero D scalarAnnulus) {H : Plane → ℝ}
    (hHc : Continuous H) (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
        annularBoundaryExtension_smooth annularBoundaryExtension_compact u : Plane → ℝ))
    (hforce : ∀ v : H1Zero D scalarAnnulus,
      gradientEnergy D scalarAnnulus u v = boundaryForcing D scalarAnnulus
        annularBoundaryExtension annularBoundaryExtension_smooth
        annularBoundaryExtension_compact v)
    (x : closure scalarAnnulus) :
    ∃ (e : OpenPartialHomeomorph Plane Plane) (O : Set Plane)
      (J : Plane → Plane →L[ℝ] ℝ),
      (x : Plane) ∈ e.target ∧ e.symm x ∈ closure O ∧ IsOpen O ∧ Convex ℝ O ∧
      IsCompact (closure O) ∧ closure O ⊆ e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      (∀ z ∈ e.source, e z ∈ scalarAnnulus ↔ 0 < z 0) ∧
      (∃ r : ℝ, 0 < r ∧ O = Metric.ball (e.symm (x : Plane)) r ∩ Half) ∧
      ContinuousOn J e.source ∧ EqOn (fderiv ℝ (H ∘ e)) J O ∧
      ∀ z ∈ closure O, HasFDerivWithinAt (H ∘ e) (J z) (closure O) z := by
  let q := annularBoundaryExtension
  let hq := annularBoundaryExtension_smooth
  let hqc := annularBoundaryExtension_compact
  let W0 : Plane → ℝ := fun y => H y - q y
  have hW0ae : W0 =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (toL2 D scalarAnnulus u : Plane → ℝ) := by
    filter_upwards [hHae, ae_restrict_of_ae (Lp.coeFn_add
      ((hq.continuous.memLp_of_hasCompactSupport hqc).toLp q)
      (toL2 D scalarAnnulus u)),
      ae_restrict_of_ae ((hq.continuous.memLp_of_hasCompactSupport hqc).coeFn_toLp)]
      with y hy hyadd hyq
    change H y = ((((hq.continuous.memLp_of_hasCompactSupport hqc).toLp q) +
      toL2 D scalarAnnulus u : Lp ℝ 2 g.volumeMeasure) : Plane → ℝ) y at hy
    rw [hyadd, Pi.add_apply, hyq] at hy
    change H y - q y = _
    linarith
  let S := Classical.choice nonempty_scalarAnnulus_smoothDomain
  obtain ⟨e, chi, V, hx, hxV, hV, hVc, hVs, he, hei, hchi, hchic, hchis,
    hchione, hflat, hreg⟩ := exists_local_memWkp_three_of_smooth_forcing D S x
  have hu3 : Euclidean.MemWkp 3 2
      (chartPullback e (fun y => chi y * toL2 D scalarAnnulus u y)) (V ∩ Half) := by
    apply hreg u (boundaryLaplacianL2 D q hq hqc) (D.laplacian q)
      (D.contMDiff_laplacian hq)
    · exact ((D.continuous_laplacian hq).memLp_of_hasCompactSupport
        (D.hasCompactSupport_laplacian hqc)).coeFn_toLp
    · exact hforce
  obtain ⟨r, hr, hKV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hxV)
  let K := Metric.closedBall (e.symm (x : Plane)) r
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKs : K ⊆ e.source := hKV.trans (subset_closure.trans hVs)
  obtain ⟨psi, hpsi, hpsic, -, hpsione, hpsis⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hKc hV hKV
  let w : Plane → ℝ := fun z => psi z *
    chartPullback e (fun y => chi y * toL2 D scalarAnnulus u y) z
  have hw3 : Euclidean.MemWkp 3 2 w Half :=
    BoundaryLocalization.memWkp_mul_smooth_of_tsupport_subset 3
      BoundaryTangential.isOpen_halfSpace hV hu3 hpsi hpsic hpsis
  let O := Metric.ball (e.symm (x : Plane)) r ∩ Half
  have hO : IsOpen O := Metric.isOpen_ball.inter BoundaryTangential.isOpen_halfSpace
  have hconv : Convex ℝ O := (convex_ball _ _).inter
    (convex_halfSpace_gt (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).isLinear 0)
  have hOK : closure O ⊆ K := by
    have h := closure_mono (inter_subset_left (s := Metric.ball (e.symm (x : Plane)) r)
      (t := Half))
    rwa [closure_ball (e.symm (x : Plane)) hr.ne'] at h
  have hOs : closure O ⊆ e.source := hOK.trans hKs
  have hzHalf : e.symm (x : Plane) ∈ closure Half := by
    have hxx : (x : Plane) ∈ closure (e.target ∩ scalarAnnulus) :=
      e.open_target.inter_closure ⟨hx, x.property⟩
    have hec := e.symm.continuousOn.continuousAt (e.open_target.mem_nhds hx)
    apply closure_mono (s := e.symm '' (e.target ∩ scalarAnnulus)) ?_
      (mem_closure_image hec hxx)
    rintro z ⟨y, hy, rfl⟩
    apply (hflat (e.symm y) (e.map_target hy.1)).mp
    rw [e.right_inv hy.1]
    exact hy.2
  have hxO : e.symm (x : Plane) ∈ closure O :=
    Metric.isOpen_ball.inter_closure ⟨Metric.mem_ball_self hr, hzHalf⟩
  let W := W0 ∘ e
  have hWc : ContinuousOn W (closure O) :=
    (hHc.sub hq.continuous).comp_continuousOn (e.continuousOn.mono hOs)
  have hWs : ContDiffOn ℝ ∞ W O := by
    apply contMDiffOn_iff_contDiffOn.mp
    apply (hHs.sub hq.contMDiffOn).comp
      (he.mono (subset_closure.trans hOs))
    intro z hz
    exact (hflat z (hOs (subset_closure hz))).mpr hz.2
  have hglobal := (ae_eq_restrict_iff_indicator_ae_eq scalarAnnulus_isOpen.measurableSet).mp hW0ae
  have hcomp := (ae_restrict_iff' hKc.measurableSet).mp
    (g.ae_comp_on_compact e he hei hKc hKs hglobal)
  have hWae : W =ᵐ[volume.restrict O] w := by
    filter_upwards [ae_restrict_of_ae hcomp, ae_restrict_mem hO.measurableSet] with z hz hzO
    have hzK : z ∈ K := Metric.ball_subset_closedBall hzO.1
    have hzV : z ∈ V := hKV hzK
    have hzA : e z ∈ scalarAnnulus := (hflat z (hKs hzK)).mpr hzO.2
    have h := hz hzK
    simp only [indicator_of_mem hzA] at h
    simpa only [W, w, Function.comp_apply, hpsione z hzK, one_mul,
      chartPullback_apply e _ (hKs hzK), hchione z hzV] using h
  obtain ⟨J, hJ, hWJ, hWbd⟩ := scalar_halfSpace_H3_boundary_derivative
    hpsic.mul_right hw3 hO hconv inter_subset_right hWs hWae hWc
  let Q := q ∘ e
  have hQs : ContDiffOn ℝ ∞ Q e.source :=
    contMDiffOn_iff_contDiffOn.mp (hq.comp_contMDiffOn he)
  let L : Plane → Plane →L[ℝ] ℝ := fun z => J z + fderiv ℝ Q z
  have hLc : ContinuousOn L e.source :=
    hJ.continuousOn.add (hQs.continuousOn_fderiv_of_isOpen e.open_source (by simp))
  have hsum : H ∘ e = W + Q := by
    funext z
    simp only [W, W0, Q, Function.comp_apply, Pi.add_apply, sub_add_cancel]
  refine ⟨e, O, L, hx, hxO, hO, hconv,
    hKc.of_isClosed_subset isClosed_closure hOK, hOs, he, hei, hflat,
    ⟨r, hr, rfl⟩, hLc, ?_, ?_⟩
  · intro z hz
    have hQd := (hQs.contDiffAt (e.open_source.mem_nhds
      (hOs (subset_closure hz)))).differentiableAt (by simp)
    rw [hsum, fderiv_add ((hWs.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)) hQd,
      hWJ hz]
  · intro z hz
    have hQd := (hQs.contDiffAt (e.open_source.mem_nhds (hOs hz))).differentiableAt (by simp)
    rw [hsum]
    exact (hWbd z).add hQd.hasFDerivAt.hasFDerivWithinAt








theorem exists_annular_harmonic_potential_boundary_differential :
    ∃ H : Plane → ℝ,
      Continuous H ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      (∀ x ∈ scalarAnnulus, D.laplacian H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 1 → H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 2 → H x = 1) ∧
      ∀ x : closure scalarAnnulus,
        ∃ (e : OpenPartialHomeomorph Plane Plane) (O : Set Plane)
          (J : Plane → Plane →L[ℝ] ℝ),
          (x : Plane) ∈ e.target ∧ e.symm x ∈ closure O ∧ IsOpen O ∧ Convex ℝ O ∧
          IsCompact (closure O) ∧ closure O ⊆ e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
          (∀ z ∈ e.source, e z ∈ scalarAnnulus ↔ 0 < z 0) ∧
          (∃ r : ℝ, 0 < r ∧ O = Metric.ball (e.symm (x : Plane)) r ∩ Half) ∧
          ContinuousOn J e.source ∧ EqOn (fderiv ℝ (H ∘ e)) J O ∧
          ∀ z ∈ closure O, HasFDerivWithinAt (H ∘ e) (J z) (closure O) z := by
  obtain ⟨H, u, hHc, hHs, hHae, hlap, hinner, houter, hforce⟩ :=
    exists_annular_continuous_harmonic_potential D
  exact ⟨H, hHc, hHs, hlap, hinner, houter,
    annular_potential_boundary_differential D u hHc hHs hHae hforce⟩

end PoincareConjecture.M64Uniformization
