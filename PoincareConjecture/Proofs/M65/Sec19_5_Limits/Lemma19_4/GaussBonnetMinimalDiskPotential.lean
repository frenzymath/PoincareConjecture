import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetScalarExtension

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.M65MinimalDisk

open M65Branch M65StrictTrace M65Gauss

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}

theorem conformalFactor_complex_contDiffOn (S : M65MinimalDisk g connection gamma) :
    ContDiffOn ℝ ∞ (S.conformalFactor ∘ orthonormalBasisOneI.repr)
      (ball (0 : ℂ) 1) := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let K := ball (0 : ℂ) 1
  have hmap : MapsTo (orthonormalBasisOneI.repr ∘ (fun z : ℂ => z)) K loopDiskSet := by
    intro z hz
    rw [loopDiskSet, mem_closedBall_zero_iff]
    change ‖orthonormalBasisOneI.repr z‖ ≤ 1
    rw [orthonormalBasisOneI.repr.norm_map]
    exact (mem_ball_zero_iff.mp hz).le
  intro z0 hz0
  have hx : e z0 ∈ ball (0 : LoopPlane) 1 := by
    rw [mem_ball_zero_iff]
    change ‖orthonormalBasisOneI.repr z0‖ < 1
    rw [orthonormalBasisOneI.repr.norm_map]
    exact mem_ball_zero_iff.mp hz0
  let x := e z0
  let chart := chartAt LoopAmbient (S.disk.map x)
  let G := chart ∘ S.disk.map
  let H := G ∘ e
  obtain ⟨gE, DE, V, hV, hxV, hVdisk, hsource, hG, hmetric, _heq⟩ :=
    S.exists_harmonic_chart_neighborhood hx
  have hH : ContDiffAt ℝ ∞ H z0 :=
    (hG.contDiffAt (hV.mem_nhds hxV)).comp z0 e.contDiff.contDiffAt
  have hGc : ContDiffAt ℝ ∞ (fun z => gE.euclideanCoefficients (H z)) z0 :=
    (gE.contDiffAt_euclideanCoefficients (H z0)).comp z0 hH
  have hDc : ContDiffAt ℝ ∞ (fun z => fderiv ℝ H z 1) z0 :=
    (hH.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hp : ContDiffAt ℝ ∞ (fun z => gE.euclideanCoefficients (H z)
      (fderiv ℝ H z 1) (fderiv ℝ H z 1)) z0 := (hGc.clm_apply hDc).clm_apply hDc
  apply (hp.congr_of_eventuallyEq ?_).contDiffWithinAt
  have hpre : ∀ᶠ z in 𝓝 z0, e z ∈ V :=
    e.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hxV)
  filter_upwards [hpre] with z hzV
  have hzK : z ∈ K := by
    have hz := hVdisk hzV
    rw [mem_ball_zero_iff] at hz ⊢
    change ‖orthonormalBasisOneI.repr z‖ < 1 at hz
    rwa [orthonormalBasisOneI.repr.norm_map] at hz
  have hh := complex_parameter_within_conformal_norm g gE (S.disk.map x)
    S.boundary_regular S.weakly_conformal (isOpen_ball.uniqueDiffOn z hzK) hzK
    (hasDerivAt_id z) hmap (hsource hzV) (hmetric (e z) hzV) (1 : ℂ)
  dsimp only at hh
  rw [fderivWithin_of_mem_nhds (isOpen_ball.mem_nhds hzK)] at hh
  symm
  simpa +instances only [Function.comp_id, Function.comp_apply, id_eq, norm_one,
    one_pow, mul_one, H, G, chart, e, conformalFactor, boundaryColumn,
    diskConformalFactor, diskColumn] using! hh

theorem exists_interior_logarithmic_potential (S : M65MinimalDisk g connection gamma) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let U := ball (0 : ℂ) 1
    let lambda := S.conformalFactor ∘ e
    ∃ (B : Finset ℂ) (m : ℂ → ℕ) (u : ℂ → ℝ),
      (∀ z, z ∈ B ↔ z ∈ U ∧ lambda z = 0) ∧
      ContDiffOn ℝ 1 u U ∧ ContDiffOn ℝ ∞ u (U \ (B : Set ℂ)) ∧
      (∀ z ∈ U, z ∉ B →
        u z = Real.log (lambda z) / 2 - ∑ a ∈ B, (m a : ℝ) * Real.log ‖z - a‖) ∧
      ∀ a ∈ B, ∃ rho : ℂ → ℝ, ContDiffAt ℝ 1 rho a ∧ 0 < rho a ∧
        ∀ᶠ z in 𝓝 a, lambda z = ‖z - a‖ ^ (2 * m a) * rho z := by
  classical
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let U := ball (0 : ℂ) 1
  let lambda := S.conformalFactor ∘ e
  have hmap (z : ℂ) (hz : z ∈ U) : e z ∈ ball (0 : LoopPlane) 1 := by
    rw [mem_ball_zero_iff]
    change ‖orthonormalBasisOneI.repr z‖ < 1
    rw [orthonormalBasisOneI.repr.norm_map]
    exact mem_ball_zero_iff.mp hz
  let T := {z : ℂ | z ∈ U ∧ lambda z = 0}
  have hT : T.Finite :=
    (S.conformalFactor_finite_zeros.preimage e.injective.injOn).subset
      (fun z hz => ⟨ball_subset_closedBall (hmap z hz.1), hz.2⟩)
  let B := hT.toFinset
  have hB (z : ℂ) : z ∈ B ↔ z ∈ U ∧ lambda z = 0 := hT.mem_toFinset
  have hlocal (a : U) : ∃ (k : ℕ) (rho : ℂ → ℝ),
      ContDiffAt ℝ 1 rho a ∧ 0 < rho a ∧
        ∀ᶠ z in 𝓝 (a : ℂ), lambda z = ‖z - a‖ ^ (2 * k) * rho z := by
    have hh := S.interior_conformalFactor_power (hmap a a.property)
    change ∃ (k : ℕ) (rho : ℂ → ℝ),
      ContDiffAt ℝ 1 rho (e.symm (e a)) ∧ 0 < rho (e.symm (e a)) ∧
        ∀ᶠ z in 𝓝 (e.symm (e a)), lambda z = ‖z - e.symm (e a)‖ ^ (2 * k) * rho z at hh
    simpa only [e.symm_apply_apply] using hh
  choose k r hrc hrp hrf using hlocal
  let m : ℂ → ℕ := fun a => if ha : a ∈ U then k ⟨a, ha⟩ else 0
  let rho : ℂ → ℂ → ℝ := fun a => if ha : a ∈ U then r ⟨a, ha⟩ else fun _ => 1
  have hbranch (a : ℂ) (_haB : a ∈ B) (ha : a ∈ U) :
      ContDiffAt ℝ 1 (rho a) a ∧ 0 < rho a a ∧
        ∀ᶠ z in 𝓝 a, lambda z = ‖z - a‖ ^ (2 * m a) * rho a z := by
    simpa only [m, rho, dif_pos ha] using
      And.intro (hrc ⟨a, ha⟩) (And.intro (hrp ⟨a, ha⟩) (hrf ⟨a, ha⟩))
  have hlambda : ContDiffOn ℝ ∞ lambda U := S.conformalFactor_complex_contDiffOn
  have hpos (z : ℂ) (hz : z ∈ U) (hne : z ∉ B) : 0 < lambda z := by
    apply lt_of_le_of_ne (S.conformalFactor_nonneg (e z))
    intro heq
    exact hne ((hB z).mpr ⟨hz, heq.symm⟩)
  obtain ⟨u, hu, heq, _hvalues⟩ := exists_scalar_residual_extension B m lambda rho
    isOpen_ball (hlambda.of_le (by simp)) hpos hbranch
  refine ⟨B, m, u, hB, hu, ?_, heq, ?_⟩
  · intro z hz
    have hn (a : ℂ) (ha : a ∈ B) : z - a ≠ 0 :=
      sub_ne_zero.mpr (fun h => hz.2 (h.symm ▸ ha))
    have hsum : ContDiffAt ℝ ∞
        (fun w : ℂ => ∑ a ∈ B, (m a : ℝ) * Real.log ‖w - a‖) z := by
      apply ContDiffAt.sum
      intro a ha
      have hs : ContDiffAt ℝ ∞ (fun w : ℂ => w - a) z :=
        contDiffAt_id.sub contDiffAt_const
      exact contDiffAt_const.mul ((hs.norm ℝ (hn a ha)).log (norm_ne_zero_iff.mpr (hn a ha)))
    have hc := (((hlambda.contDiffAt (isOpen_ball.mem_nhds hz.1)).log
      (hpos z hz.1 hz.2).ne').div_const 2).sub hsum
    apply (hc.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [isOpen_ball.mem_nhds hz.1,
      B.finite_toSet.isClosed.compl_mem_nhds hz.2] with w hw hnB
    exact heq w hw hnB
  · intro a ha
    exact ⟨rho a, hbranch a ha ((hB a).mp ha).1⟩

end PoincareConjecture.M65MinimalDisk
