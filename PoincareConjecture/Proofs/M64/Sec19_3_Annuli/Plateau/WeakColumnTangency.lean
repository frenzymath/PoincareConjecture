import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ObservedTangentProjection
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MovingKernelWeakClosure












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.WeakCompactness

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)



theorem m64Annulus_observed_weak_column_tangent
    {mu : Measure LoopPlane}
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e)
    (f : ℕ → LoopPlane → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j))
    (v : LoopPlane → M) (i : Fin 2)
    (hV : ∀ j, MemLp (fun p => fderiv ℝ (e ∘ f j) p
      (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2 mu)
    (V : Lp E 2 mu)
    (hweak : WeakConverges (fun j => (hV j).toLp
      (fun p => fderiv ℝ (e ∘ f j) p (EuclideanSpace.basisFun (Fin 2) ℝ i))) V)
    (hlim : ∀ᵐ p ∂mu, Tendsto (fun j => f j p) atTop (𝓝 (v p))) :
    ∀ᵐ p ∂mu, V p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (v p)) := by
  obtain ⟨P, K, hP, hK, hb, hfix, hrange⟩ := m64ChartReadable_tangent_projection e he hread
  let R := fun j p => ContinuousLinearMap.id ℝ E - P (f j p)
  let R0 := fun p => ContinuousLinearMap.id ℝ E - P (v p)
  have hR (j : ℕ) : AEStronglyMeasurable (R j) mu :=
    (continuous_const.sub (hP.comp (hf j).continuous)).aestronglyMeasurable
  have hbound (j : ℕ) : ∀ᵐ p ∂mu, ‖R j p‖ ≤ 1 + K := Eventually.of_forall fun p =>
    (norm_sub_le _ _).trans (add_le_add (ContinuousLinearMap.norm_id_le) (hb _))
  have hRlim : ∀ᵐ p ∂mu, Tendsto (fun j => R j p) atTop (𝓝 (R0 p)) := by
    filter_upwards [hlim] with p hp
    exact tendsto_const_nhds.sub ((hP.tendsto _).comp hp)
  have hzero (j : ℕ) : ∀ᵐ p ∂mu, R j p ((hV j).toLp
      (fun q => fderiv ℝ (e ∘ f j) q (EuclideanSpace.basisFun (Fin 2) ℝ i)) p) = 0 := by
    filter_upwards [(hV j).coeFn_toLp] with p hp
    let w := EuclideanSpace.basisFun (Fin 2) ℝ i
    have hd := mfderiv_comp p ((he _).mdifferentiableAt (by simp))
      ((hf j p).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hd
    have hcol : fderiv ℝ (e ∘ f j) p w = mfderiv (𝓡 n) (𝓡 m) e (f j p)
        (mfderiv (𝓡 2) (𝓡 n) (f j) p w) := congrArg (fun T => T w) hd
    have hpfix : P (f j p) (fderiv ℝ (e ∘ f j) p w) = fderiv ℝ (e ∘ f j) p w := by
      erw [hcol]
      exact hfix _ _
    change _ - P (f j p) _ = 0
    rw [hp]
    exact sub_eq_zero.mpr hpfix.symm
  have hz := m64MovingKernel_weak_closed R R0 hR (by positivity : 0 ≤ 1 + K)
    hbound hRlim hweak hzero
  filter_upwards [hz] with p hp
  change V p - P (v p) (V p) = 0 at hp
  have heq : P (v p) (V p) = V p := (sub_eq_zero.mp hp).symm
  simpa only [heq] using hrange (v p) (V p)

end PoincareConjecture
