import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetDensityTransport
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryLog
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetInteriorLog
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology ContDiff Manifold Laplacian

namespace PoincareConjecture.M65Gauss

open M65StrictTrace

def logarithmicGaussDensity (lambda : LoopPlane → ℝ) (z : LoopPlane) : ℝ :=
  -(∑ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ (fun w => Real.log (lambda w)) y
    (EuclideanSpace.basisFun (Fin 2) ℝ i)) z
      (EuclideanSpace.basisFun (Fin 2) ℝ i)) / 2

private theorem density_complex_parameter (lambda : LoopPlane → ℝ) {z : ℂ}
    (hs : ContDiffAt ℝ ∞ (lambda ∘ orthonormalBasisOneI.repr) z)
    (hp : 0 < lambda (orthonormalBasisOneI.repr z)) :
    logarithmicGaussDensity lambda (orthonormalBasisOneI.repr z) =
      -Δ (fun w => Real.log (lambda (orthonormalBasisOneI.repr w))) z / 2 := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let f := fun w : LoopPlane => Real.log (lambda w)
  have hc : ContDiffAt ℝ ∞ (f ∘ e) z := hs.log hp.ne'
  have hc' : ContDiffAt ℝ ∞ (f ∘ e) (e.symm (e z)) := by
    simpa only [e.symm_apply_apply] using hc
  have hreal : ContDiffAt ℝ ∞ f (e z) := by
    simpa only [Function.comp_def, e.apply_symm_apply] using
      hc'.comp (e z) e.symm.contDiff.contDiffAt
  have hh := laplacian_complex_parameter f z
  change Δ (f ∘ e) z = Δ f (e z) at hh
  rw [laplacian_eq_plane_trace (hreal.of_le (WithTop.coe_le_coe.mpr le_top))] at hh
  change -(∑ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ f y
      (EuclideanSpace.basisFun (Fin 2) ℝ i)) (e z)
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) / 2 = -Δ (f ∘ e) z / 2
  rw [hh]

theorem boundary_density_integrable_relative
    {lambda localFactor : LoopPlane → ℝ} {p : ℂ} (hp : ‖p‖ = 1)
    {r : ℝ} (hr : 0 < r)
    (hs : ContDiffOn ℝ ∞ (lambda ∘ orthonormalBasisOneI.repr) (ball (0 : ℂ) 1))
    (hnon : ∀ w ∈ loopDiskSet, 0 ≤ lambda w)
    (hfinite : {w : LoopPlane | w ∈ loopDiskSet ∧ lambda w = 0}.Finite)
    (heq : ∀ z ∈ closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im},
      localFactor (orthonormalBasisOneI.repr z) =
        lambda (orthonormalBasisOneI.repr (boundaryCoordinate p z)) *
          ‖deriv (boundaryCoordinate p) z‖ ^ 2)
    (hlocal : IntegrableOn (logarithmicGaussDensity localFactor)
      (orthonormalBasisOneI.repr.symm ⁻¹' (ball (0 : ℂ) r ∩ {z | 0 < z.im})) volume) :
    ∃ V : Set LoopPlane, V ∈ 𝓝[loopDiskSet] (orthonormalBasisOneI.repr p) ∧
      IntegrableOn (logarithmicGaussDensity lambda) V volume := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let P := boundaryCoordinate p
  let Q := boundaryInverse p
  let W0 := ball (0 : ℂ) r ∩ {z | 0 < z.im}
  have hp0 : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; norm_num)
  obtain ⟨s, hs0, hleft⟩ := Metric.mem_nhds_iff.mp (boundaryInverse_coordinate_eventually hp0)
  let d := min r s / 2
  have hd : 0 < d := half_pos (lt_min hr hs0)
  have hdr : d < r := (half_lt_self (lt_min hr hs0)).trans_le (min_le_left _ _)
  have hds : d < s := (half_lt_self (lt_min hr hs0)).trans_le (min_le_right _ _)
  let W := ball (0 : ℂ) d ∩ {z | 0 < z.im}
  have hW : IsOpen W := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hW0 : IsOpen W0 := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hWW0 : W ⊆ W0 := inter_subset_inter (ball_subset_ball hdr.le) Subset.rfl
  have hP : ContDiff ℂ ∞ P := contDiff_boundaryCoordinate p
  have hPA (z : ℂ) : AnalyticAt ℂ P z := (hP.differentiable (by simp)).analyticAt z
  have hPn (z : ℂ) : deriv P z ≠ 0 := deriv_boundaryCoordinate_ne_zero hp0 z
  have hPD (z : ℂ) : HasDerivAt P (deriv P z) z :=
    (hP.differentiable (by simp) z).hasDerivAt
  have hleftW (z : ℂ) (hz : z ∈ W) : Q (P z) = z :=
    hleft ((ball_subset_ball hds.le) hz.1)
  have hinj : InjOn P W := fun z hz w hw hzw => by
    have hh := congrArg Q hzw
    rwa [hleftW z hz, hleftW w hw] at hh
  have hPball (z : ℂ) (hz : z ∈ W0) : P z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    exact (boundaryCoordinate_interior_iff hp z).mpr hz.2
  have hPK (z : ℂ) (hz : z ∈ W0) : e (P z) ∈ loopDiskSet := by
    rw [loopDiskSet, mem_closedBall_zero_iff]
    change ‖orthonormalBasisOneI.repr (P z)‖ ≤ 1
    rw [orthonormalBasisOneI.repr.norm_map]
    exact (mem_ball_zero_iff.mp (hPball z hz)).le
  let T := {z : ℂ | z ∈ W ∧ lambda (e (P z)) = 0}
  have hT : T.Finite := by
    have himg : ((e ∘ P) '' T).Finite := hfinite.subset (by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨hPK z (hWW0 hz.1), hz.2⟩)
    exact himg.of_finite_image (fun z hz w hw hzw => hinj hz.1 hw.1 (e.injective hzw))
  have hpre : e ⁻¹' (e.symm ⁻¹' W) = W := by
    ext z
    simp only [mem_preimage, e.symm_apply_apply]
  have hL : IntegrableOn (fun z => logarithmicGaussDensity localFactor (e z)) W volume := by
    have hh := (orthonormalBasisOneI.measurePreserving_repr.integrableOn_comp_preimage
      e.toHomeomorph.measurableEmbedding).mpr (hlocal.mono_set (preimage_mono hWW0))
    change IntegrableOn (fun z => logarithmicGaussDensity localFactor (e z))
      (e ⁻¹' (e.symm ⁻¹' W)) volume at hh
    rwa [hpre] at hh
  let G := fun w : ℂ => logarithmicGaussDensity lambda (e w)
  have hweighted : IntegrableOn (fun z => |(fderiv ℝ P z).det| • G (P z)) W volume := by
    apply hL.congr
    filter_upwards [ae_restrict_mem hW.measurableSet,
      ae_restrict_of_ae (hT.countable.ae_notMem volume)] with z hz hn
    have hpos : 0 < lambda (e (P z)) :=
      lt_of_le_of_ne (hnon _ (hPK z (hWW0 hz)))
        (fun h => hn ⟨hz, h.symm⟩)
    have hlam := hs.contDiffAt (isOpen_ball.mem_nhds (hPball z (hWW0 hz)))
    have hlocEq : localFactor ∘ e =ᶠ[𝓝 z]
        fun w => (lambda ∘ e) (P w) * ‖deriv P w‖ ^ 2 := by
      filter_upwards [hW0.mem_nhds (hWW0 hz)] with w hw
      exact heq w ⟨ball_subset_closedBall hw.1, (show 0 < w.im from hw.2).le⟩
    have hnSmooth : ContDiffAt ℝ ∞ (fun w => ‖deriv P w‖ ^ 2) z :=
      (((hPA z).deriv.contDiffAt.restrict_scalars ℝ).norm ℝ (hPn z)).pow 2
    have hlocSmooth : ContDiffAt ℝ ∞ (localFactor ∘ e) z :=
      ((hlam.comp z (hP.contDiffAt.restrict_scalars ℝ)).mul hnSmooth)
        |>.congr_of_eventuallyEq hlocEq
    have hlocPos : 0 < localFactor (e z) := by
      change 0 < (localFactor ∘ e) z
      rw [hlocEq.self_of_nhds]
      exact mul_pos hpos (sq_pos_of_pos (norm_pos_iff.mpr (hPn z)))
    have hDelta := logarithmic_laplacian_comp_holomorphic hlam hpos (hPA z) (hPn z) hlocEq
    change Δ (fun w => Real.log (localFactor (orthonormalBasisOneI.repr w))) z =
      ‖deriv P z‖ ^ 2 * Δ (fun w => Real.log (lambda (orthonormalBasisOneI.repr w))) (P z)
      at hDelta
    change logarithmicGaussDensity localFactor (orthonormalBasisOneI.repr z) = _
    rw [density_complex_parameter localFactor hlocSmooth hlocPos,
      det_real_fderiv_holomorphic (hPD z), abs_of_nonneg (sq_nonneg _)]
    dsimp only [G]
    change _ = _ • logarithmicGaussDensity lambda (orthonormalBasisOneI.repr (P z))
    rw [density_complex_parameter lambda hlam hpos, hDelta]
    simp only [smul_eq_mul]
    ring
  have hPder (z : ℂ) : HasFDerivAt P (fderiv ℝ P z) z :=
    ((hP.restrict_scalars ℝ).differentiable (by simp) z).hasFDerivAt
  have hImage : IntegrableOn G (P '' W) volume :=
    (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hW.measurableSet
      (fun z _ => (hPder z).hasFDerivWithinAt) hinj G).mpr
        hweighted
  let N := {w : ℂ | w ≠ 0 ∧ ‖Q w‖ < d} ∩ closedBall (0 : ℂ) 1
  have hN : N ∈ 𝓝[closedBall (0 : ℂ) 1] p := by
    have hn : ∀ᶠ w in 𝓝[closedBall (0 : ℂ) 1] p, w ≠ 0 :=
      Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds hp0))
        (fun _ h => h)
    have hq : ∀ᶠ w in 𝓝[closedBall (0 : ℂ) 1] p, ‖Q w‖ < d := by
      have hh := (boundaryInverse_tendstoWithin hp).eventually
        (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) hd))
      simpa only [dist_zero_right, Q] using hh
    filter_upwards [hn, hq, self_mem_nhdsWithin] with w hw hq hwK
    exact ⟨⟨hw, hq⟩, hwK⟩
  have hNsub : N ⊆ P '' W ∪ sphere (0 : ℂ) 1 := by
    intro w hw
    have hwle : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw.2
    rcases lt_or_eq_of_le hwle with hlt | heqnorm
    · left
      have hright : P (Q w) = w := boundaryCoordinate_inverse hp0 hw.1.1
      refine ⟨Q w, ⟨mem_ball_zero_iff.mpr hw.1.2, ?_⟩, hright⟩
      apply (boundaryCoordinate_interior_iff hp (Q w)).mp
      change ‖P (Q w)‖ < 1
      rwa [hright]
    · exact Or.inr (by simpa only [mem_sphere, dist_zero_right] using heqnorm)
  have hNull : IntegrableOn G (sphere (0 : ℂ) 1) volume :=
    IntegrableOn.of_measure_zero (Measure.addHaar_sphere volume (0 : ℂ) 1)
  have hNI : IntegrableOn G N volume := (hImage.union hNull).mono_set hNsub
  have hE : Tendsto e.symm (𝓝[loopDiskSet] (e p)) (𝓝[closedBall (0 : ℂ) 1] p) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hh : Tendsto e.symm (𝓝[loopDiskSet] (e p)) (𝓝 (e.symm (e p))) :=
        (e.symm.continuous.tendsto (e p)).mono_left nhdsWithin_le_nhds
      simpa only [e.symm_apply_apply] using hh
    · filter_upwards [self_mem_nhdsWithin] with w hw
      rw [mem_closedBall_zero_iff]
      change ‖orthonormalBasisOneI.repr.symm w‖ ≤ 1
      rw [orthonormalBasisOneI.repr.symm.norm_map]
      exact mem_closedBall_zero_iff.mp hw
  refine ⟨e.symm ⁻¹' N, hE hN, ?_⟩
  have hh := (orthonormalBasisOneI.measurePreserving_repr_symm.integrableOn_comp_preimage
    e.symm.toHomeomorph.measurableEmbedding).mpr hNI
  change IntegrableOn (G ∘ e.symm) (e.symm ⁻¹' N) volume at hh
  simpa only [Function.comp_def, G, e.apply_symm_apply] using hh

end PoincareConjecture.M65Gauss

namespace PoincareConjecture.M65MinimalDisk

open M65StrictTrace M65Gauss

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}

theorem boundary_original_logarithmicDensity_integrable
    (S : M65MinimalDisk g connection gamma)
    (hinj : Function.Injective (gamma : LoopCircle → M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ s : ℝ, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) s ≠ 0)
    {x : LoopPlane} (hx : ‖x‖ = 1) :
    ∃ V : Set LoopPlane, V ∈ 𝓝[loopDiskSet] x ∧
      IntegrableOn (logarithmicGaussDensity S.conformalFactor) V volume := by
  obtain ⟨gE, DE, r, hr, _hmap, _hsource, _hH, _hHi, _hmetric, hnorm, _heq, hlocal⟩ :=
    S.boundary_logarithmicDensity_integrable hinj hsmooth hregular hx
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let p := e.symm x
  let P := boundaryCoordinate p
  let H := (chartAt LoopAmbient (S.disk.map x)) ∘ S.disk.map ∘ e ∘ P
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let lam := fun z : LoopPlane => gE.inner (H (e.symm z))
    (fderivWithin ℝ H K (e.symm z) 1) (fderivWithin ℝ H K (e.symm z) 1)
  have hp : ‖p‖ = 1 := (orthonormalBasisOneI.repr.symm.norm_map x).trans hx
  have hfactor (z : ℂ) (hz : z ∈ K) :
      lam (e z) = S.conformalFactor (e (P z)) * ‖deriv P z‖ ^ 2 := by
    have hh := hnorm z hz 1
    change gE.inner (H z) (fderivWithin ℝ H K z 1) (fderivWithin ℝ H K z 1) =
      diskConformalFactor g S.disk.map (e (P z)) * ‖I * P z‖ ^ 2 * ‖(1 : ℂ)‖ ^ 2 at hh
    dsimp only [lam]
    rw [e.symm_apply_apply]
    rw [(hasDerivAt_boundaryCoordinate p z).deriv]
    simpa +instances only [norm_one, one_pow, mul_one, conformalFactor, boundaryColumn,
      diskConformalFactor, diskColumn] using! hh
  have hh := boundary_density_integrable_relative hp hr S.conformalFactor_complex_contDiffOn
    (fun w _ => S.conformalFactor_nonneg w) S.conformalFactor_finite_zeros hfactor hlocal
  change ∃ V : Set LoopPlane, V ∈ 𝓝[loopDiskSet] (e p) ∧
    IntegrableOn (logarithmicGaussDensity S.conformalFactor) V volume at hh
  simpa only [p, e.apply_symm_apply] using hh

theorem logarithmicGaussDensity_integrable (S : M65MinimalDisk g connection gamma)
    (hinj : Function.Injective (gamma : LoopCircle → M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (gamma ∘ m65LoopAngular))
    (hregular : ∀ s : ℝ, curveVelocity (n := 3) (gamma ∘ m65LoopAngular) s ≠ 0) :
    IntegrableOn (logarithmicGaussDensity S.conformalFactor) loopDiskSet volume := by
  have hlocal : LocallyIntegrableOn (logarithmicGaussDensity S.conformalFactor)
      loopDiskSet volume := by
    intro x hx
    have hnorm : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    rcases lt_or_eq_of_le hnorm with hinside | hboundary
    · obtain ⟨r, hr, _hsub, hI⟩ :=
        S.interior_logarithmicDensity_integrable (mem_ball_zero_iff.mpr hinside)
      exact ⟨ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr), hI⟩
    · exact S.boundary_original_logarithmicDensity_integrable hinj hsmooth hregular hboundary
  exact hlocal.integrableOn_isCompact (isCompact_closedBall (0 : LoopPlane) 1)

end PoincareConjecture.M65MinimalDisk
