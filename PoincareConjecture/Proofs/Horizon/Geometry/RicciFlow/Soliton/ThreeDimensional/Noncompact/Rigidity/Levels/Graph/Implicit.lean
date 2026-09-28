import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.HittingTime








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold



theorem contMDiffAt_of_unique_zero
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {F : ℝ × M → ℝ} {σ : M → ℝ} {I : Set ℝ} {V : Set M}
    (hI : IsOpen I) (hV : IsOpen V)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (I ×ˢ V))
    (hroot : ∀ y ∈ V, σ y ∈ I ∧ F (σ y, y) = 0)
    (hunique : ∀ y ∈ V, ∀ s ∈ I, F (s, y) = 0 → s = σ y)
    {y : M} (hy : y ∈ V) {v : ℝ} (hv : v ≠ 0)
    (hder : HasDerivAt (fun s ↦ F (s, y)) v (σ y)) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ y := by
  let e := extChartAt (𝓡 n) y
  have he := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) y
    (mem_extChartAt_target y)).contMDiffAt
      (extChartAt_target_mem_nhds' (I := 𝓡 n) (mem_extChartAt_target y))
  let G : EuclideanSpace ℝ (Fin n) × ℝ → ℝ := fun q ↦ F (q.2, e.symm q.1)
  let q₀ : EuclideanSpace ℝ (Fin n) × ℝ := (e y, σ y)
  have hG : ContDiffAt ℝ ∞ G q₀ := by
    have he' : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ) (𝓡 n) ∞
        (fun q ↦ e.symm q.1) q₀ := he.comp q₀ contDiffAt_fst.contMDiffAt
    have hpair : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × ℝ)
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ (fun q ↦ (q.2, e.symm q.1)) q₀ :=
      contDiffAt_snd.contMDiffAt.prodMk he'
    have hF' := hF.contMDiffAt ((hI.prod hV).mem_nhds
      (show (σ y, y) ∈ I ×ˢ V from ⟨(hroot y hy).1, hy⟩))
    have hsame : (q₀.2, e.symm q₀.1) = (σ y, y) := by
      simp only [q₀, e.left_inv (mem_extChartAt_source y)]
    rw [← hsame] at hF'
    exact (hF'.comp q₀ hpair).contDiffAt
  have hGder : HasDerivAt (fun s ↦ G (q₀.1, s)) v (σ y) := by
    simpa only [G, q₀, e.left_inv (mem_extChartAt_source y)] using hder
  have hpart : (fderiv ℝ G q₀).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ) =
      v • (ContinuousLinearMap.id ℝ ℝ) := by
    have hd := (hG.differentiableAt (by simp)).hasFDerivAt
    have hcomp := hd.comp (σ y)
      ((hasFDerivAt_const q₀.1 (σ y)).prodMk (hasFDerivAt_id (σ y)))
    have heq := hcomp.unique hGder.hasFDerivAt
    apply ContinuousLinearMap.ext
    intro z
    have hz := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L z) heq
    change fderiv ℝ G q₀ (0, z) = z * v at hz
    change fderiv ℝ G q₀ (0, z) = v * z
    simpa only [mul_comm] using hz
  have hinv : ((fderiv ℝ G q₀).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) ℝ)).IsInvertible := by
    rw [hpart]
    refine ⟨(LinearEquiv.smulOfNeZero ℝ ℝ v hv).toContinuousLinearEquiv, ?_⟩
    apply ContinuousLinearMap.ext
    intro z
    rfl
  let ψ := hG.implicitFunction (by simp) hinv
  have hψ : ContDiffAt ℝ ∞ ψ (e y) := hG.contDiffAt_implicitFunction (by simp) hinv
  have hψzero : ψ (e y) = σ y := hG.implicitFunction_apply_self (by simp) hinv
  have hψeq : ∀ᶠ z in 𝓝 (e y), G (z, ψ z) = G q₀ :=
    hG.eventually_apply_implicitFunction (by simp) hinv
  have hψI : ∀ᶠ z in 𝓝 (e y), ψ z ∈ I := by
    apply hψ.continuousAt.preimage_mem_nhds
    rw [hψzero]
    exact hI.mem_nhds (hroot y hy).1
  have hechart : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e y := contMDiffAt_extChartAt
  have hcomp : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun z ↦ ψ (e z)) y :=
    hψ.contMDiffAt.comp y hechart
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hechart.continuousAt hψeq, hechart.continuousAt hψI,
    hV.mem_nhds hy, extChartAt_source_mem_nhds' (I := 𝓡 n) (mem_extChartAt_source y)]
    with z heq hIz hz hchartz
  apply (hunique z hz (ψ (e z)) hIz ?_).symm
  have hback : e.symm (e z) = z := e.left_inv hchartz
  change F (ψ (e z), z) = 0
  conv_lhs => arg 1; arg 2; rw [← hback]
  change G (e z, ψ (e z)) = 0
  rw [heq]
  simpa only [G, q₀, e.left_inv (mem_extChartAt_source y)] using (hroot y hy).2



theorem contMDiffAt_of_unique_time_root
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {F : ℝ × M → ℝ} {σ : M → ℝ} {I : Set ℝ} {V : Set M}
    (hI : IsOpen I) (hV : IsOpen V)
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (I ×ˢ V))
    (hroot : ∀ y ∈ V, σ y ∈ I ∧ F (σ y, y) = 0)
    (hinj : ∀ y ∈ V, InjOn (fun s ↦ F (s, y)) I)
    {y : M} (hy : y ∈ V) {v : ℝ} (hv : v ≠ 0)
    (hder : HasDerivAt (fun s ↦ F (s, y)) v (σ y)) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ y := by
  apply contMDiffAt_of_unique_zero hI hV hF hroot ?_ hy hv hder
  intro z hz s hs hzero
  exact hinj z hz hs (hroot z hz).1 (hzero.trans (hroot z hz).2.symm)

end Poincare.Manifold
