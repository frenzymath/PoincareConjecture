import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.Inclusion
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenInclusion








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold.RegularFiber


abbrev openFiber {M F : Type*} [TopologicalSpace M] (f : M → F) (U : Opens M) (c : F) :=
  ((fun x : U => f (x : M)) ⁻¹' {c} : Set U)


def openFiberIncl {M F : Type*} [TopologicalSpace M] (f : M → F) (U : Opens M) (c : F)
    (z : openFiber f U c) : M := ((z : U) : M)

theorem range_openFiberIncl {M F : Type*} [TopologicalSpace M]
    (f : M → F) (U : Opens M) (c : F) :
    range (openFiberIncl f U c) = (U : Set M) ∩ f ⁻¹' {c} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(z : U).2, z.2⟩
  · rintro ⟨hx, hf⟩
    exact ⟨⟨⟨x, hx⟩, hf⟩, rfl⟩

theorem isEmbedding_openFiberIncl {M F : Type*} [TopologicalSpace M]
    (f : M → F) (U : Opens M) (c : F) :
    Topology.IsEmbedding (openFiberIncl f U c) :=
  Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal

variable {m k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = m + k)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → Fin k → ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) ∞ f) (U : Opens M)
  (hreg : ∀ x ∈ U, Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x))
  (c : Fin k → ℝ)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
include hf hreg in
theorem openFiberRestrict_regular (x : U) :
    Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) (fun y : U => f (y : M)) x) := by
  rw [RegularLevel.mfderiv_opens_restrict U f ((hf (x : M)).mdifferentiableAt (by simp))]
  exact hreg x x.2


@[reducible] def openFiberChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin m)) (openFiber f U c) :=
  fiberChartedSpace (m := m) (hf.comp contMDiff_subtype_val) c
    (fun x _ => openFiberRestrict_regular hf U hreg x)

theorem isManifold_openFiber :
    let := openFiberChartedSpace (m := m) hf U hreg c
    IsManifold (𝓡 m) ∞ (openFiber f U c) :=
  isManifold_fiber (m := m) (hf.comp contMDiff_subtype_val) c
    (fun x _ => openFiberRestrict_regular hf U hreg x)

theorem contMDiff_openFiberIncl :
    let := openFiberChartedSpace (m := m) hf U hreg c
    ContMDiff (𝓡 m) 𝓘(ℝ, E) ∞ (openFiberIncl f U c) := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  exact contMDiff_subtype_val.comp
    (contMDiff_fiber_val (m := m) (hf.comp contMDiff_subtype_val) c
      (fun x _ => openFiberRestrict_regular hf U hreg x))

theorem mfderiv_openFiberIncl (z : openFiber f U c) :
    let := openFiberChartedSpace (m := m) hf U hreg c
    mfderiv (𝓡 m) 𝓘(ℝ, E) (openFiberIncl f U c) z =
      mfderiv (𝓡 m) 𝓘(ℝ, E) ((↑) : openFiber f U c → U) z := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  have hv0 : ContMDiff (𝓡 m) 𝓘(ℝ, E) ∞ ((↑) : openFiber f U c → U) :=
    contMDiff_fiber_val (m := m) (hf.comp contMDiff_subtype_val) c
      (fun x _ => openFiberRestrict_regular hf U hreg x)
  have hv := (hv0 z).mdifferentiableAt (by simp)
  have h := mfderiv_comp z
    (RegularLevel.hasMFDerivAt_opens_subtypeVal U (z : U)).mdifferentiableAt hv
  change mfderiv (𝓡 m) 𝓘(ℝ, E) ((fun y : U => (y : M)) ∘
    ((↑) : openFiber f U c → U)) z = _
  rw [h, RegularLevel.mfderiv_opens_subtypeVal]
  ext v
  rfl

theorem injective_mfderiv_openFiberIncl (z : openFiber f U c) :
    let := openFiberChartedSpace (m := m) hf U hreg c
    Injective (mfderiv (𝓡 m) 𝓘(ℝ, E) (openFiberIncl f U c) z) := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  change Injective (mfderiv (𝓡 m) 𝓘(ℝ, E) (openFiberIncl f U c) z)
  rw [mfderiv_openFiberIncl hf U hreg c z]
  exact injective_mfderiv_fiber_val (m := m) (hf.comp contMDiff_subtype_val) c
    (fun x _ => openFiberRestrict_regular hf U hreg x) z

theorem range_mfderiv_openFiberIncl (z : openFiber f U c) :
    let := openFiberChartedSpace (m := m) hf U hreg c
    (mfderiv (𝓡 m) 𝓘(ℝ, E) (openFiberIncl f U c) z :
      EuclideanSpace ℝ (Fin m) →L[ℝ] E).range =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f (openFiberIncl f U c z) :
        E →L[ℝ] (Fin k → ℝ)).ker := by
  let := openFiberChartedSpace (m := m) hf U hreg c
  have hr := range_mfderiv_fiber_val (m := m) (hf.comp contMDiff_subtype_val) c
    (fun x _ => openFiberRestrict_regular hf U hreg x) z
  have hk := congrArg (fun A : E →L[ℝ] (Fin k → ℝ) => A.ker)
    (RegularLevel.mfderiv_opens_restrict U f ((hf ((z : U) : M)).mdifferentiableAt (by simp)))
  exact (congrArg (fun A : EuclideanSpace ℝ (Fin m) →L[ℝ] E => A.range)
    (mfderiv_openFiberIncl hf U hreg c z)).trans (hr.trans hk)

end Poincare.Geometry.Manifold.RegularFiber
