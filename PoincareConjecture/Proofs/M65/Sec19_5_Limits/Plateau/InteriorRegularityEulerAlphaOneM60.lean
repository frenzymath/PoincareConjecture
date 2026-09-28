import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerAlphaOne
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerInterior
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalSmooth










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture




theorem m65AlphaOneSmoothness {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) : M65AlphaOneSmoothness g := by
  intro b u V center radius hr hmap hc hu hV hw hvar
  apply M60.suWeakAlphaCoordinate_smooth_alpha_one g b u V center radius
  refine
    { radius_pos := hr
      coordinate_range := hmap
      coordinate_continuous := hc
      coordinate_memLp := by simpa using hu
      column_memLp := fun i => by simpa using hV i
      weak_derivative := ?_
      variation_integrable := ?_
      variation_zero := ?_ }
  · intro i a φ hφ hcomp hs
    exact (hw i a φ hφ hcomp hs).2.2
  · intro φ hφ hcomp hs
    change IntegrableOn (fun z => M60.suAlphaChartVariation g b 1 u V φ z)
      (Metric.ball center radius)
    simpa only [M60.suAlphaChartVariation, sub_self, Real.rpow_zero, mul_one, one_mul]
      using (hvar φ hφ hcomp hs).1
  · intro φ hφ hcomp hs
    simpa only [M60.suAlphaChartVariation, sub_self, Real.rpow_zero, mul_one, one_mul]
      using (hvar φ hφ hcomp hs).2







theorem m65PlateauInteriorRegularityInput_proved {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (γ : C1FreeLoopSpace (M := M)) (a b c : LoopCircle) :
    M65PlateauInteriorRegularityInput g D e γ a b c :=
  M65Euler.interiorRegularityInput_of_alphaOne D e he hinj hemb compact
    (fun gE => m65AlphaOneSmoothness gE) γ a b c

end PoincareConjecture
