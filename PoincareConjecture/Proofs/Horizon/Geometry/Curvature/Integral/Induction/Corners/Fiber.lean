import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Submersion
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.OpenSubset

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle InnerProductSpace

namespace PoincareConjecture.RiemannianMetric

variable {m k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M] [IsManifold (𝓡 (m + k)) ∞ M]
  (g : RiemannianMetric (m + k) M) (f : Fin k → M → ℝ)
  (hf : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (f i)) (U : Opens M)
  (w : ∀ x : M, Fin k → TangentSpace (𝓡 (m + k)) x)
  {δ : ℝ} (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
  (hsmall : (k : ℝ) * δ < (1 - 2 * δ) ^ 2)
  (hh : ∀ x ∈ U, ∀ i, g.tangentNorm x (w x i) ≤ 1)
  (hopposite : ∀ x ∈ U, ∀ i,
    g.inner x (g.gradient (f i) x) (w x i) ≤ -1 + 2 * δ)
  (hcross : ∀ x ∈ U, ∀ i j, i ≠ j →
    |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ)

include g hf w hδ hδhalf hsmall hh hopposite hcross in

theorem strainer_openFiber_regular (x : M) (hx : x ∈ U) :
    Surjective (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) (fun y i => f i y) x) := by
  have hsurj := (g.strainer_gradients_regular f x (w x) hδ hδhalf
    (by simpa using hsmall) (hh x hx) (hopposite x hx) (hcross x hx)).2
  intro y
  obtain ⟨v, hv⟩ := hsurj y
  refine ⟨v, ?_⟩
  funext i
  rw [Poincare.Geometry.Manifold.mfderiv_pi_apply f hf x v i]
  exact congrFun hv i

@[reducible] def strainerOpenFiberChartedSpace (c : Fin k → ℝ) :
    ChartedSpace (EuclideanSpace ℝ (Fin m)) (openFiber (fun y i => f i y) U c) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact openFiberChartedSpace (m := m) (contMDiff_pi_space.mpr hf) U
    (g.strainer_openFiber_regular f hf U w hδ hδhalf hsmall hh hopposite hcross) c

theorem strainerOpenFiber_geometry (c : Fin k → ℝ) :
    let := g.strainerOpenFiberChartedSpace f hf U w hδ hδhalf hsmall hh hopposite hcross c
    IsManifold (𝓡 m) ∞ (openFiber (fun y i => f i y) U c) ∧
    ContMDiff (𝓡 m) (𝓡 (m + k)) ∞ (openFiberIncl (fun y i => f i y) U c) ∧
    ∀ z : openFiber (fun y i => f i y) U c,
      Injective (mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl (fun y i => f i y) U c) z) ∧
      (mfderiv (𝓡 m) (𝓡 (m + k)) (openFiberIncl (fun y i => f i y) U c) z :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (m + k))).range =
      (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) (fun y i => f i y)
        (openFiberIncl (fun y i => f i y) U c z) :
        EuclideanSpace ℝ (Fin (m + k)) →L[ℝ] (Fin k → ℝ)).ker := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := g.strainer_openFiber_regular f hf U w hδ hδhalf hsmall hh hopposite hcross
  refine ⟨isManifold_openFiber (m := m) (contMDiff_pi_space.mpr hf) U hreg c,
    contMDiff_openFiberIncl (m := m) (contMDiff_pi_space.mpr hf) U hreg c, ?_⟩
  exact fun z =>
    ⟨injective_mfderiv_openFiberIncl (m := m) (contMDiff_pi_space.mpr hf) U hreg c z,
      range_mfderiv_openFiberIncl (m := m) (contMDiff_pi_space.mpr hf) U hreg c z⟩

end PoincareConjecture.RiemannianMetric
