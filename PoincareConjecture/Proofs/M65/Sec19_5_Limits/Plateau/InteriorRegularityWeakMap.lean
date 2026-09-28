import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEnergy
import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

set_option autoImplicit false

open Set MeasureTheory Metric
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} {N : ℕ}

structure M65LocalWeakMap (e : M → EuclideanSpace ℝ (Fin N)) (U : Set LoopPlane) where
  value : LoopPlane → M
  derivative : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin N)
  value_memLp : ∀ K : Set LoopPlane, IsCompact K → K ⊆ U →
    MemLp (fun z => e (value z)) 2 (volume.restrict K)
  derivative_memLp : ∀ i (K : Set LoopPlane), IsCompact K → K ⊆ U →
    MemLp (derivative i) 2 (volume.restrict K)
  weak_derivative : ∀ (test : 𝓢(LoopPlane, ℝ)), HasCompactSupport test → tsupport test ⊆ U →
    ∀ (i : Fin 2) (j : Fin N),
      (∫ z in U, test z * derivative i z j) =
        -(∫ z in U,
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) * e (value z) j)

namespace M65LocalWeakMap

variable {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}

theorem test_derivative_integrable (F : M65LocalWeakMap e U) (test : 𝓢(LoopPlane, ℝ))
    (hc : HasCompactSupport test) (hs : tsupport test ⊆ U) (i : Fin 2) (j : Fin N) :
    IntegrableOn (fun z => test z * F.derivative i z j) U := by
  have hi := (F.derivative_memLp i (tsupport test) hc hs).eval_piLp j
  have ht := (test.memLp 2 volume).restrict (tsupport test)
  have hsupport : Function.support (fun z => test z * F.derivative i z j) ⊆
      tsupport test := by
    intro z hz
    apply subset_tsupport test
    exact (mul_ne_zero_iff.mp hz).1
  exact ((integrableOn_iff_integrable_of_support_subset hsupport).mp
    (ht.integrable_mul hi)).integrableOn

theorem test_value_integrable (F : M65LocalWeakMap e U) (test : 𝓢(LoopPlane, ℝ))
    (hc : HasCompactSupport test) (hs : tsupport test ⊆ U) (i : Fin 2) (j : Fin N) :
    IntegrableOn (fun z =>
      fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i) * e (F.value z) j) U := by
  let derivativeTest := ∂_{EuclideanSpace.basisFun (Fin 2) ℝ i} test
  have hi := (F.value_memLp (tsupport test) hc hs).eval_piLp j
  have ht := (derivativeTest.memLp 2 volume).restrict (tsupport test)
  have hsupport : Function.support (fun z => derivativeTest z * e (F.value z) j) ⊆
      tsupport test := by
    intro z hz
    exact (SchwartzMap.tsupport_lineDerivOp_subset _ test)
      (subset_tsupport derivativeTest ((mul_ne_zero_iff.mp hz).1))
  exact ((integrableOn_iff_integrable_of_support_subset hsupport).mp
    (ht.integrable_mul hi)).integrableOn

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem energy_integrable (F : M65LocalWeakMap e U) (g : RiemannianMetric 3 M)
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (K : Set LoopPlane) (hc : IsCompact K) (hs : K ⊆ U) :
    IntegrableOn (m65EmbeddedEnergyDensity g e F.value F.derivative) K :=
  m65EmbeddedEnergyDensity_integrable g e he hinj hemb compact
    (F.value_memLp K hc hs).1 (fun i => F.derivative_memLp i K hc hs)

end M65LocalWeakMap

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

def M65LocallyMinimizesEnergy {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}
    (g : RiemannianMetric 3 M) (F : M65LocalWeakMap e U) : Prop :=
  ∀ (x : LoopPlane) (r : ℝ), 0 < r → closedBall x r ⊆ U →
    ∀ G : M65LocalWeakMap e U,
      (G.value =ᵐ[volume.restrict (U \ closedBall x r)] F.value) →
        (∫ z in closedBall x r, m65EmbeddedEnergyDensity g e F.value F.derivative z) ≤
          ∫ z in closedBall x r, m65EmbeddedEnergyDensity g e G.value G.derivative z

end PoincareConjecture
