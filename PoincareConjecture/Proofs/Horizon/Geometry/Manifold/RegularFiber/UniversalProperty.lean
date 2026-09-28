import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.OpenSubset
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.UniversalProperty







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold.RegularFiber

variable {m k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = m + k)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → Fin k → ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) ∞ f) (c : Fin k → ℝ)
  (hreg : ∀ x : M, f x = c → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x))


theorem contMDiffAt_into_fiber_iff (F : N → (f ⁻¹' {c} : Set M)) (x : N) :
    let := fiberChartedSpace (m := m) hf c hreg
    ContMDiffAt J (𝓡 m) ∞ F x ↔
      ContMDiffAt J 𝓘(ℝ, E) ∞ (fun y => (F y : M)) x := by
  let := fiberChartedSpace (m := m) hf c hreg
  constructor
  · intro hF
    exact (contMDiff_fiber_val hf c hreg (F x)).comp x hF
  · intro hF
    rw [contMDiffAt_iff_target]
    refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hF.continuousAt, ?_⟩
    have hc := (contMDiffOn_adaptedChart (m := m) hf (F x) (hreg (F x) (F x).2)).contMDiffAt
      ((adaptedChart (m := m) hf (F x) (hreg (F x) (F x).2)).open_source.mem_nhds
        (mem_adaptedChart_source hf (F x) (hreg (F x) (F x).2)))
    have hproj := contDiff_snd.contDiffAt.contMDiffAt.comp x (hc.comp x hF)
    convert! hproj using 1


theorem contMDiffAt_into_openFiber_iff (U : Opens M)
    (hregU : ∀ x ∈ U, Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x))
    (F : N → openFiber f U c) (x : N) :
    let := openFiberChartedSpace (m := m) hf U hregU c
    ContMDiffAt J (𝓡 m) ∞ F x ↔
      ContMDiffAt J 𝓘(ℝ, E) ∞ (openFiberIncl f U c ∘ F) x := by
  let := openFiberChartedSpace (m := m) hf U hregU c
  have h := contMDiffAt_into_fiber_iff (m := m) (J := J)
    (hf.comp contMDiff_subtype_val) c
    (fun y _ => openFiberRestrict_regular hf U hregU y) F x
  exact h.trans (ContMDiffAt.subtypeVal_comp_iff U (fun y => (F y : U)) x).symm


theorem contMDiffOn_into_openFiber_iff (U : Opens M)
    (hregU : ∀ x ∈ U, Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x))
    (F : N → openFiber f U c) {V : Set N} (hV : IsOpen V) :
    let := openFiberChartedSpace (m := m) hf U hregU c
    ContMDiffOn J (𝓡 m) ∞ F V ↔
      ContMDiffOn J 𝓘(ℝ, E) ∞ (openFiberIncl f U c ∘ F) V := by
  let := openFiberChartedSpace (m := m) hf U hregU c
  constructor
  · intro hF x hx
    exact ((contMDiffAt_into_openFiber_iff hf c U hregU F x).mp
      ((hF x hx).contMDiffAt (hV.mem_nhds hx))).contMDiffWithinAt
  · intro hF x hx
    exact ((contMDiffAt_into_openFiber_iff hf c U hregU F x).mpr
      ((hF x hx).contMDiffAt (hV.mem_nhds hx))).contMDiffWithinAt

end Poincare.Geometry.Manifold.RegularFiber
