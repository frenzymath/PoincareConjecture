import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerTension
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerAlphaOneLocal
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerMinimumC1
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerDiskMinimum
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.Attainment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold

universe u

namespace PoincareConjecture.M65Euler

theorem exists_smooth_representative_of_alphaOne {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (hregularity : ∀ gE : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)),
      M65AlphaOneSmoothness gE)
    {U : Set LoopPlane} (hU : IsOpen U) (F : M65LocalWeakMap e U)
    (hmin : M65LocallyMinimizesEnergy g F) :
    ∃ q : LoopPlane → M, ContMDiffOn (𝓡 2) (𝓡 3) ∞ q U ∧
      q =ᵐ[volume.restrict U] F.value ∧
      (∀ i : Fin 2, (fun z => fderiv ℝ (e ∘ q) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        =ᵐ[volume.restrict U] F.derivative i) ∧
      ∀ z ∈ U, m65PlaneTension D q z = 0 := by
  obtain ⟨q, hq1, hq⟩ := exists_C1_representative g e he hinj hemb compact hU F hmin
  have hqs := minimum_representative_smooth_of_alphaOne g e he hemb.injective hinj
    hregularity hU F hmin q hq1.continuousOn hq
  refine ⟨q, hqs, hq, ?_, fun z hz =>
    minimum_representative_harmonic D e he hemb.injective hinj hU F hmin q hqs hq hz⟩
  intro i
  have hcomp : ContDiffOn ℝ 1 (e ∘ q) U :=
    (he.comp_contMDiffOn hqs).contDiffOn.of_le (by simp)
  apply classical_derivative_eq_weak hU F q hcomp _ i
  filter_upwards [hq] with z hz
  rw [hz]

theorem interiorRegularityInput_of_alphaOne {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (hregularity : ∀ gE : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)),
      M65AlphaOneSmoothness gE)
    (γ : C1FreeLoopSpace (M := M)) (a b c : LoopCircle) :
    M65PlateauInteriorRegularityInput g D e γ a b c := by
  intro F hmin
  have hlocal := F.localMap_minimizes g e he hinj hemb compact γ.continuous a b c hmin
  obtain ⟨q, hqs, hq, hD, hharm⟩ := exists_smooth_representative_of_alphaOne D e he hinj
    hemb compact hregularity isOpen_ball F.localMap hlocal
  exact ⟨q, ⟨hqs, hq, hD, hharm⟩⟩

end PoincareConjecture.M65Euler
