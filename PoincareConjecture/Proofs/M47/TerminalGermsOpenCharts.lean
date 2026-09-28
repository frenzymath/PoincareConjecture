import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalDiffeomorph











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]



theorem terminalGerms_open_codomain_localDiffeomorph (V : Opens N) {f : M → V}
    (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (Subtype.val ∘ f)) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f := by
  intro x
  have hinc := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) V (f x)
  have hcomp := (hf x).comp (𝓡 n) V hinc.localInverse_isLocalDiffeomorphAt
  apply hcomp.congr_of_eventuallyEq
  have hfc : Continuous f := hf.contMDiff.continuous.subtype_mk (fun x => (f x).property)
  filter_upwards [hfc.continuousAt hinc.localInverse_eventuallyEq_left] with y hy
  exact hy.symm


def terminalGermsOpenChartSource (q : M → N)
    (hq : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ q) (V : Opens N) : Opens M :=
  ⟨q ⁻¹' (V : Set N), V.isOpen.preimage hq.contMDiff.continuous⟩


def terminalGermsOpenChartMap (q : M → N)
    (hq : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ q) (V : Opens N) :
    terminalGermsOpenChartSource q hq V → V :=
  fun x => ⟨q x.val, x.property⟩

theorem terminalGerms_openChartMap_localDiffeomorph (q : M → N)
    (hq : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ q) (V : Opens N) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (terminalGermsOpenChartMap q hq V) := by
  apply terminalGerms_open_codomain_localDiffeomorph
  intro x
  exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n)
    (terminalGermsOpenChartSource q hq V) x).comp (𝓡 n) N (hq x.val)



theorem terminalGerms_openChartMap_differential (q : M → N)
    (hq : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ q) (V : Opens N)
    (x : terminalGermsOpenChartSource q hq V) :
    (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : V → N)
        (terminalGermsOpenChartMap q hq V x)).comp
      (mfderiv (𝓡 n) (𝓡 n) (terminalGermsOpenChartMap q hq V) x) =
    (mfderiv (𝓡 n) (𝓡 n) q x.val).comp
      (mfderiv (𝓡 n) (𝓡 n)
        (Subtype.val : terminalGermsOpenChartSource q hq V → M) x) := by
  rw [← mfderiv_comp x ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) _)
    ((terminalGerms_openChartMap_localDiffeomorph q hq V).mdifferentiable (by simp) x)]
  rw [← mfderiv_comp x (hq.mdifferentiable (by simp) x.val)
    ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) x)]
  rfl

end PoincareConjecture.M47
