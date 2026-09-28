import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityRepresentative
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.MinimalDiskHarmonicChart
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceHarmonicPullback










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Complex
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Boundary

open M65Branch M65StrictTrace






theorem continuous_boundary_harmonic_chart
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) {f q : LoopPlane → M} {R : ℝ} (hR : 0 < R)
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) ∞ f (ball (0 : LoopPlane) 1))
    (hharm : ∀ z ∈ ball (0 : LoopPlane) 1, m65PlaneTension D f z = 0)
    (hq : ContinuousOn q (closedBall (0 : LoopPlane) R))
    {p : ℂ} (hp : ‖p‖ = 1)
    (heq : EqOn q (f ∘ diskBoundaryCoordinate p)
      (ball (0 : LoopPlane) R ∩ {z | 0 < z 1})) :
    let c := chartAt LoopAmbient (q 0)
    let H := c ∘ q
    let K := H ∘ orthonormalBasisOneI.repr
    ∃ (gE : RiemannianMetric 3 LoopAmbient) (DE : LeviCivitaData gE) (r : ℝ),
      0 < r ∧ r ≤ R ∧ MapsTo q (closedBall (0 : LoopPlane) r) c.source ∧
      ContinuousOn H (closedBall (0 : LoopPlane) r) ∧
      ContDiffOn ℝ ∞ H (ball (0 : LoopPlane) r ∩ {z | 0 < z 1}) ∧
      (∀ z ∈ closedBall (0 : LoopPlane) r, ∀ᶠ y in 𝓝 (H z), ∀ a b : LoopAmbient,
        gE.inner y a b = g.inner (c.symm y)
          (mfderiv (𝓡 3) (𝓡 3) c.symm y a)
          (mfderiv (𝓡 3) (𝓡 3) c.symm y b)) ∧
      ∀ z ∈ ball (0 : ℂ) r ∩ {z | 0 < z.im},
        dbar (complexGradient K) z = harmonicMatrix DE K z (complexGradient K z) := by
  let c := chartAt LoopAmbient (q 0)
  let H := c ∘ q
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let K := H ∘ e
  obtain ⟨gE, DE, hE⟩ := m65Exists_chartMetric g (q 0)
  have hmetric : ∀ᶠ y in 𝓝 (H 0), ∀ a b : LoopAmbient,
      gE.inner y a b = g.inner (c.symm y)
        (mfderiv (𝓡 3) (𝓡 3) c.symm y a)
        (mfderiv (𝓡 3) (𝓡 3) c.symm y b) := by
    simpa only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, c, H,
      Function.comp_apply, id_eq] using hE
  obtain ⟨V, hVsub, hVopen, h0V⟩ := _root_.mem_nhds_iff.mp hmetric
  have h0R : (0 : LoopPlane) ∈ closedBall 0 R := mem_closedBall_self hR.le
  have h0source : q 0 ∈ c.source := mem_chart_source LoopAmbient (q 0)
  have hc0 : ContinuousAt c (q 0) :=
    c.continuousOn.continuousAt (c.open_source.mem_nhds h0source)
  have hsource : ∀ᶠ z in 𝓝[closedBall (0 : LoopPlane) R] 0, q z ∈ c.source :=
    hq 0 h0R (c.open_source.mem_nhds h0source)
  have htarget : ∀ᶠ z in 𝓝[closedBall (0 : LoopPlane) R] 0, H z ∈ V :=
    (hc0.comp_continuousWithinAt (hq 0 h0R)) (hVopen.mem_nhds h0V)
  obtain ⟨O, hO, hOsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
    (hsource.and htarget)
  obtain ⟨eta, heta, hetasub⟩ := Metric.mem_nhds_iff.mp hO
  let r := min R (eta / 2)
  have hr : 0 < r := lt_min hR (half_pos heta)
  have hrR : r ≤ R := min_le_left _ _
  have hreta : r < eta := (min_le_right _ _).trans_lt (by linarith)
  have hcap (z : LoopPlane) (hz : z ∈ closedBall 0 r) : q z ∈ c.source ∧ H z ∈ V :=
    hOsub ⟨hetasub (closedBall_subset_ball hreta hz), closedBall_subset_closedBall hrR hz⟩
  let U := ball (0 : LoopPlane) r ∩ {z | 0 < z 1}
  have hUR : U ⊆ ball (0 : LoopPlane) R ∩ {z | 0 < z 1} :=
    inter_subset_inter_left _ (ball_subset_ball hrR)
  have hP : MapsTo (diskBoundaryCoordinate p) U (ball (0 : LoopPlane) 1) := by
    intro z hz
    rw [mem_ball_zero_iff, norm_diskBoundaryCoordinate hp, Real.exp_lt_one_iff]
    exact neg_neg_of_pos hz.2
  have hqs : ContMDiffOn (𝓡 2) (𝓡 3) ∞ q U :=
    (hf.comp (contDiff_diskBoundaryCoordinate p).contMDiff.contMDiffOn hP).congr
      (heq.mono hUR)
  have hHc : ContinuousOn H (closedBall 0 r) := c.continuousOn.comp
    (hq.mono (closedBall_subset_closedBall hrR)) (fun z hz => (hcap z hz).1)
  have hHs : ContDiffOn ℝ ∞ H U :=
    (contMDiffOn_chart.comp hqs (fun z hz => (hcap z (ball_subset_closedBall hz.1)).1)).contDiffOn
  have hmet (z : LoopPlane) (hz : z ∈ closedBall 0 r) :
      ∀ᶠ y in 𝓝 (H z), ∀ a b : LoopAmbient,
        gE.inner y a b = g.inner (c.symm y)
          (mfderiv (𝓡 3) (𝓡 3) c.symm y a)
          (mfderiv (𝓡 3) (𝓡 3) c.symm y b) :=
    mem_of_superset (hVopen.mem_nhds (hcap z hz).2) hVsub
  refine ⟨gE, DE, r, hr, hrR, (fun z hz => (hcap z hz).1), hHc, hHs, hmet, ?_⟩
  let G := c ∘ f
  let W0 := ball (0 : LoopPlane) 1 ∩ f ⁻¹' c.source
  have hW0 : IsOpen W0 := hf.continuousOn.isOpen_inter_preimage isOpen_ball c.open_source
  have hG0 : ContDiffOn ℝ ∞ G W0 :=
    (contMDiffOn_chart.comp (hf.mono inter_subset_left) (fun _ hz => hz.2)).contDiffOn
  let W := W0 ∩ G ⁻¹' V
  have hW : IsOpen W := hG0.continuousOn.isOpen_inter_preimage hW0 hVopen
  have hG : ContDiffOn ℝ ∞ G W := hG0.mono inter_subset_left
  have hGeq (z : LoopPlane) (hz : z ∈ W) :
      (∑ i : Fin 2, fderiv ℝ (fderiv ℝ G) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) +
        ∑ i : Fin 2, M65Gauss.connectionCoefficient DE (G z)
          (fderiv ℝ G z (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (fderiv ℝ G z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0 := by
    exact M65Gauss.harmonic_coordinate_equation D DE (q 0) isOpen_ball hf hz.1.1 hz.1.2
      (mem_of_superset (hVopen.mem_nhds hz.2) hVsub) (hharm z hz.1.1)
  let T := ball (0 : ℂ) r ∩ {z | 0 < z.im}
  have hT : IsOpen T := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have heU (z : ℂ) (hz : z ∈ T) : e z ∈ U := by
    constructor
    · simpa only [mem_ball_zero_iff, e, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        orthonormalBasisOneI.repr.norm_map] using hz.1
    · change 0 < (orthonormalBasisOneI.repr z) 1
      simpa only [orthonormalBasisOneI_repr_apply, Matrix.cons_val_one,
        Matrix.cons_val_zero, mem_ofPred_eq] using hz.2
  have hPe (z : ℂ) : diskBoundaryCoordinate p (e z) = e (boundaryCoordinate p z) := by
    simp only [diskBoundaryCoordinate, e, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.symm_apply_apply]
  have hmap : MapsTo (boundaryCoordinate p) T (e ⁻¹' W) := by
    intro z hz
    have hzU := heU z hz
    have hqeq : q (e z) = f (e (boundaryCoordinate p z)) := by
      simpa only [Function.comp_apply, hPe] using heq (hUR hzU)
    have hsmall := hcap (e z) (ball_subset_closedBall hzU.1)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hPe]
      exact hP hzU
    · change f (e (boundaryCoordinate p z)) ∈ c.source
      rw [← hqeq]
      exact hsmall.1
    · change c (f (e (boundaryCoordinate p z))) ∈ V
      simpa only [H, Function.comp_apply, hqeq] using hsmall.2
  have hWe : IsOpen (e ⁻¹' W) := hW.preimage e.continuous
  have hGes : ContDiffOn ℝ ∞ (G ∘ e) (e ⁻¹' W) :=
    hG.comp e.contDiff.contDiffOn (fun _ hz => hz)
  have hGeq' (z : ℂ) (hz : z ∈ e ⁻¹' W) :
      dbar (complexGradient (G ∘ e)) z =
        harmonicMatrix DE (G ∘ e) z (complexGradient (G ∘ e) z) :=
    plane_harmonic_to_complex DE (hG.contDiffAt (hW.mem_nhds hz)) (hGeq _ hz)
  let J := (G ∘ e) ∘ boundaryCoordinate p
  have hKJ : EqOn K J T := by
    intro z hz
    change c (q (e z)) = c (f (e (boundaryCoordinate p z)))
    congr 1
    simpa only [Function.comp_apply, hPe] using heq (hUR (heU z hz))
  intro z hz
  change dbar (complexGradient K) z = harmonicMatrix DE K z (complexGradient K z)
  have hj := harmonic_matrix_equation_comp_holomorphic DE hWe hT hGes
    (contDiff_boundaryCoordinate p).contDiffOn hmap hGeq' hz
  have hnear : K =ᶠ[𝓝 z] J := by
    filter_upwards [hT.mem_nhds hz] with w hw
    exact hKJ hw
  have hgrad : complexGradient K =ᶠ[𝓝 z] complexGradient J := by
    filter_upwards [hnear.fderiv (𝕜 := ℝ)] with w hw
    simp only [complexGradient, hw]
  have hbar : dbar (complexGradient K) z = dbar (complexGradient J) z :=
    congrArg dbarLinear hgrad.fderiv_eq
  have hmatrix : harmonicMatrix DE K z = harmonicMatrix DE J z := by
    simp only [harmonicMatrix, hnear.self_of_nhds, hnear.fderiv_eq]
  rw [hbar, hmatrix, hgrad.self_of_nhds]
  exact hj

end PoincareConjecture.M65Boundary
