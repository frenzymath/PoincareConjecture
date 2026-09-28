import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.ChartedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold.RegularFiber

variable {m k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = m + k)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → Fin k → ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) ∞ f) (c : Fin k → ℝ)
  (hreg : ∀ x : M, f x = c → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x))

theorem contMDiff_fiber_val :
    let := fiberChartedSpace (m := m) hf c hreg
    ContMDiff (𝓡 m) 𝓘(ℝ, E) ∞ ((↑) : (f ⁻¹' {c} : Set M) → M) := by
  let := fiberChartedSpace (m := m) hf c hreg
  change ContMDiff (𝓡 m) 𝓘(ℝ, E) ∞ ((↑) : (f ⁻¹' {c} : Set M) → M)
  intro z
  let e := adaptedChart (m := m) hf z (hreg z z.2)
  let y := extChartAt (𝓡 m) z z
  have hy : y ∈ (fiberChart (m := m) hf c hreg z).target :=
    (fiberChart (m := m) hf c hreg z).map_source (mem_fiberChart_source hf c hreg z)
  have hp : ContMDiffAt (𝓡 m)
      𝓘(ℝ, (Fin k → ℝ) × EuclideanSpace ℝ (Fin m)) ∞ (fun v => (c, v)) y :=
    (contDiff_const.prodMk contDiff_id).contDiffAt.contMDiffAt
  have hi := (contMDiffOn_adaptedChart_symm hf z (hreg z z.2)).contMDiffAt
    (e.open_target.mem_nhds hy)
  have hev : ((↑) : (f ⁻¹' {c} : Set M) → M) ∘ (extChartAt (𝓡 m) z).symm
      =ᶠ[𝓝 y] fun v => e.symm (c, v) := by
    filter_upwards [(fiberChart (m := m) hf c hreg z).open_target.mem_nhds hy] with v hv
    exact fiberChart_symm_val hf c hreg z hv
  rw [contMDiffAt_iff_source]
  exact ((hi.comp y hp).congr_of_eventuallyEq hev).contMDiffWithinAt

theorem injective_mfderiv_fiber_val (z : (f ⁻¹' {c} : Set M)) :
    let := fiberChartedSpace (m := m) hf c hreg
    Injective (mfderiv (𝓡 m) 𝓘(ℝ, E) ((↑) : (f ⁻¹' {c} : Set M) → M) z) := by
  let := fiberChartedSpace (m := m) hf c hreg
  let : IsManifold (𝓡 m) ∞ (f ⁻¹' {c} : Set M) := isManifold_fiber (m := m) hf c hreg
  change Injective (mfderiv (𝓡 m) 𝓘(ℝ, E) ((↑) : (f ⁻¹' {c} : Set M) → M) z)
  let e := adaptedChart (m := m) hf z (hreg z z.2)
  have he := (contMDiffOn_adaptedChart hf z (hreg z z.2)).contMDiffAt
    (e.open_source.mem_nhds (mem_adaptedChart_source hf z (hreg z z.2)))
  have hp : ContMDiffAt 𝓘(ℝ, E) (𝓡 m) ∞ (fun x => (e x).2) (z : M) :=
    contDiff_snd.contDiffAt.contMDiffAt.comp (z : M) he
  have hv := (contMDiff_fiber_val (m := m) hf c hreg z).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp z (hp.mdifferentiableAt (by simp)) hv
  have heq : (fun x => (e x).2) ∘ ((↑) : (f ⁻¹' {c} : Set M) → M) =
      extChartAt (𝓡 m) z := rfl
  rw [heq, mfderiv_extChartAt_self] at hcomp
  intro u v huv
  have h := congrArg (mfderiv 𝓘(ℝ, E) (𝓡 m) (fun x => (e x).2) (z : M)) huv
  change (mfderiv 𝓘(ℝ, E) (𝓡 m) (fun x => (e x).2) (z : M) ∘L
      mfderiv (𝓡 m) 𝓘(ℝ, E) ((↑) : (f ⁻¹' {c} : Set M) → M) z) u =
    (mfderiv 𝓘(ℝ, E) (𝓡 m) (fun x => (e x).2) (z : M) ∘L
      mfderiv (𝓡 m) 𝓘(ℝ, E) ((↑) : (f ⁻¹' {c} : Set M) → M) z) v at h
  rwa [← hcomp] at h

theorem range_mfderiv_fiber_val (z : (f ⁻¹' {c} : Set M)) :
    let := fiberChartedSpace (m := m) hf c hreg
    (mfderiv (𝓡 m) 𝓘(ℝ, E) ((↑) : (f ⁻¹' {c} : Set M) → M) z :
      EuclideanSpace ℝ (Fin m) →L[ℝ] E).range =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f (z : M) : E →L[ℝ] (Fin k → ℝ)).ker := by
  let := fiberChartedSpace (m := m) hf c hreg
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] E :=
    mfderiv (𝓡 m) 𝓘(ℝ, E) ((↑) : (f ⁻¹' {c} : Set M) → M) z
  let L : E →L[ℝ] (Fin k → ℝ) := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f (z : M)
  change A.range = L.ker
  have hA : Injective A := injective_mfderiv_fiber_val hf c hreg z
  have hchain := mfderiv_comp z ((hf (z : M)).mdifferentiableAt (by simp))
    ((contMDiff_fiber_val (m := m) hf c hreg z).mdifferentiableAt (by simp))
  have hc : f ∘ ((↑) : (f ⁻¹' {c} : Set M) → M) = fun _ => c := funext fun y => y.2
  rw [hc, mfderiv_const] at hchain
  have hLA : L.comp A = 0 := hchain.symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro v ⟨u, rfl⟩
    change L (A u) = 0
    exact DFunLike.congr_fun hLA u
  · have hdim := (L : E →ₗ[ℝ] (Fin k → ℝ)).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (hreg z z.2), finrank_top, Module.finrank_pi,
      Fintype.card_fin, Fact.out (p := Module.finrank ℝ E = m + k)] at hdim
    rw [LinearMap.finrank_range_of_inj hA, finrank_euclideanSpace_fin]
    omega

end Poincare.Geometry.Manifold.RegularFiber
