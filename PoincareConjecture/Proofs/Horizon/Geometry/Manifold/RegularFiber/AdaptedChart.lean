import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Submersion.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Real

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

theorem exists_adaptedChart
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) ∞ f) (x : M)
    (hreg : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x)) :
    ∃ d : OpenPartialHomeomorph M ((Fin k → ℝ) × EuclideanSpace ℝ (Fin m)),
      x ∈ d.source ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, (Fin k → ℝ) × EuclideanSpace ℝ (Fin m)) ∞ d d.source ∧
      ContMDiffOn 𝓘(ℝ, (Fin k → ℝ) × EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, E) ∞
        d.symm d.target ∧
      ∀ y ∈ d.target, f (d.symm y) = y.1 := by
  let L : E →L[ℝ] (Fin k → ℝ) := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x
  have hdim : Module.finrank ℝ L.ker = m := by
    have h := (L : E →ₗ[ℝ] (Fin k → ℝ)).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hreg, finrank_top, Module.finrank_pi,
      Fact.out (p := Module.finrank ℝ E = m + k)] at h
    simp only [Fintype.card_fin] at h
    omega
  let b : L.ker ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [hdim, finrank_euclideanSpace_fin])
  obtain ⟨e, d, hx, hd, hdi, heq⟩ :=
    exists_projection_chart_of_surjective_mfderiv hf x hreg
  change E ≃L[ℝ] ((Fin k → ℝ) × L.ker) at e
  let a := e.trans ((ContinuousLinearEquiv.refl ℝ (Fin k → ℝ)).prodCongr b)
  let D := d.trans a.toHomeomorph.toOpenPartialHomeomorph
  refine ⟨D, ⟨hx, Set.mem_univ _⟩, ?_, ?_, ?_⟩
  · exact a.contDiff.contMDiff.comp_contMDiffOn (hd.mono inter_subset_left)
  · exact hdi.comp a.symm.contDiff.contMDiff.contMDiffOn (fun y hy => hy.2)
  · intro y hy
    have h := heq (a.symm y) hy.2
    change f (d.symm (a.symm y)) = y.1
    change f (d.symm (a.symm y)) = (e (a.symm y)).1 at h
    simpa [a] using h

def adaptedChart
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) ∞ f) (x : M)
    (hreg : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x)) :
    OpenPartialHomeomorph M ((Fin k → ℝ) × EuclideanSpace ℝ (Fin m)) :=
  (exists_adaptedChart (m := m) hf x hreg).choose

variable (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) ∞ f) (x : M)
  (hreg : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x))

theorem mem_adaptedChart_source : x ∈ (adaptedChart (m := m) hf x hreg).source :=
  (exists_adaptedChart hf x hreg).choose_spec.1

theorem contMDiffOn_adaptedChart :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, (Fin k → ℝ) × EuclideanSpace ℝ (Fin m)) ∞
      (adaptedChart (m := m) hf x hreg) (adaptedChart (m := m) hf x hreg).source :=
  (exists_adaptedChart hf x hreg).choose_spec.2.1

theorem contMDiffOn_adaptedChart_symm :
    ContMDiffOn 𝓘(ℝ, (Fin k → ℝ) × EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, E) ∞
      (adaptedChart (m := m) hf x hreg).symm (adaptedChart (m := m) hf x hreg).target :=
  (exists_adaptedChart hf x hreg).choose_spec.2.2.1

theorem comp_adaptedChart_symm {y : (Fin k → ℝ) × EuclideanSpace ℝ (Fin m)}
    (hy : y ∈ (adaptedChart (m := m) hf x hreg).target) :
    f ((adaptedChart (m := m) hf x hreg).symm y) = y.1 :=
  (exists_adaptedChart hf x hreg).choose_spec.2.2.2 y hy

theorem adaptedChart_fst {y : M} (hy : y ∈ (adaptedChart (m := m) hf x hreg).source) :
    ((adaptedChart (m := m) hf x hreg) y).1 = f y := by
  have h := comp_adaptedChart_symm hf x hreg
    ((adaptedChart (m := m) hf x hreg).map_source hy)
  rw [(adaptedChart (m := m) hf x hreg).left_inv hy] at h
  exact h.symm

end Poincare.Geometry.Manifold.RegularFiber
