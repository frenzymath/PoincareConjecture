import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric.UniformHarmonicLift

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem exists_smooth_local_right_inverse {e : E → M} {x : E}
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e x)
    (hinv : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible) :
    ∃ j : M → E, ContMDiffAt (𝓡 n) (𝓡 n) ∞ j (e x) ∧
      j (e x) = x ∧ ∀ᶠ y in 𝓝 (e x), e (j y) = y := by
  let c := extChartAt (𝓡 n) x
  let d := extChartAt (𝓡 n) (e x)
  let q := writtenInExtChartAt (𝓡 n) (𝓡 n) x e
  have hq : ContDiffAt ℝ ∞ q (c x) := by
    simpa [q, c, writtenInExtChartAt, contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp he).2
  have hderiv : mfderiv (𝓡 n) (𝓡 n) e x = fderiv ℝ q (c x) := by
    rw [mfderiv, if_pos (he.mdifferentiableAt (by simp))]
    simp [q, c]
  have hbij : Function.Bijective (fderiv ℝ q (c x)) := by
    rw [← hderiv]
    exact hinv.bijective
  let L := ContinuousLinearEquiv.ofBijective (fderiv ℝ q (c x))
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hdq : HasFDerivAt q (L : E →L[ℝ] E) (c x) :=
    (hq.differentiableAt (by simp)).hasFDerivAt
  let i := hq.localInverse hdq (by simp)
  have hi : ContDiffAt ℝ ∞ i (q (c x)) := hq.to_localInverse hdq (by simp)
  have hix : i (q (c x)) = c x := hq.localInverse_apply_image hdq (by simp)
  have hqx : q (c x) = d (e x) := by simp [q, c, d, writtenInExtChartAt]
  have hil : ∀ᶠ z in 𝓝 (c x), i (q z) = z :=
    (hq.hasStrictFDerivAt' hdq (by simp)).eventually_left_inverse
  let j : M → E := fun y => c.symm (i (d y))
  have hjx : j (e x) = x := by
    simp only [j, ← hqx, hix]
    exact c.left_inv (mem_extChartAt_source x)
  have hj : ContMDiffAt (𝓡 n) (𝓡 n) ∞ j (e x) := by
    have hi' : ContMDiffAt (𝓡 n) (𝓡 n) ∞ i (d (e x)) := by
      rw [← hqx]
      exact hi.contMDiffAt
    have hcs : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm (i (d (e x))) := by
      rw [← hqx, hix]
      exact (contMDiffOn_extChartAt_symm x).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds (mem_extChartAt_target x))
    exact hcs.comp (e x) (hi'.comp (e x) contMDiffAt_extChartAt)
  refine ⟨j, hj, hjx, ?_⟩
  rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective he hinv.bijective]
  change ∀ᶠ z in 𝓝 x, e (j (e z)) = e z
  filter_upwards [(continuousAt_extChartAt (I := 𝓡 n) x).tendsto.eventually hil,
    (isOpen_extChartAt_source (I := 𝓡 n) x).mem_nhds (mem_extChartAt_source x)]
    with z hzi hzc
  have hqz : q (c z) = d (e z) := by
    simp only [q, writtenInExtChartAt, Function.comp_apply]
    rw [c.left_inv hzc]
  change e (c.symm (i (d (e z)))) = e z
  rw [← hqz, hzi, c.left_inv hzc]


theorem contMDiffAt_of_contDiffAt_pullback
    {g : RiemannianMetric n M} {O : M} {r C A : ℝ}
    (F : UniformHarmonicLift g O r C A) (hr : 0 < r)
    {u : ℝ × M → ℝ} {t : ℝ}
    (hu : ContDiffAt ℝ ∞ (fun p : E × ℝ => u (p.2, F.e p.1)) (0, t)) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (t, O) := by
  have hzero : (0 : E) ∈ Metric.ball 0 (2 * r) := by simpa using (by linarith : 0 < 2 * r)
  obtain ⟨j, hj, hj0, hright⟩ := exists_smooth_local_right_inverse
    (F.he.contMDiffAt (Metric.isOpen_ball.mem_nhds hzero)) (F.hlocal 0 hzero)
  rw [F.he0] at hj hj0 hright
  have hmap : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ (fun p : ℝ × M => (j p.2, p.1)) (t, O) :=
    (hj.comp (t, O) contMDiffAt_snd).prodMk contMDiffAt_fst
  have hu' : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : E × ℝ => u (p.2, F.e p.1)) (j O, t) := by
    rw [hj0]
    simp +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hu.contMDiffAt
  apply (hu'.comp (t, O) hmap).congr_of_eventuallyEq
  filter_upwards [continuousAt_snd.tendsto.eventually hright] with p hp
  simp only [Function.comp_apply, hp]

end PoincareConjecture.RiemannianMetric.UniformHarmonicLift
