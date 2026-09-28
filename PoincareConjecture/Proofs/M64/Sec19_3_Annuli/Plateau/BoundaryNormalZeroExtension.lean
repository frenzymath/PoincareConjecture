import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryZeroExtension











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.BoundaryTangential

namespace PoincareConjecture

private theorem swap_normal_preimage :
    m64BoundaryCoordinateSwap ⁻¹' {p : LoopPlane | 0 < p 1} = halfSpace 2 := by
  ext p
  simp [halfSpace, m64BoundaryCoordinateSwap_apply]

private theorem swap_indicator (u : LoopPlane → ℝ) :
    ((halfSpace 2).indicator (u ∘ m64BoundaryCoordinateSwap)) ∘
      m64BoundaryCoordinateSwap = {p : LoopPlane | 0 < p 1}.indicator u := by
  funext p
  have hh : m64BoundaryCoordinateSwap p ∈ halfSpace 2 ↔ 0 < p 1 := by
    simp [halfSpace, m64BoundaryCoordinateSwap_apply]
  by_cases hp : 0 < p 1
  · simp only [comp_apply, indicator_of_mem (hh.mpr hp), m64BoundaryCoordinateSwap_twice,
      indicator_of_mem (show p ∈ {p : LoopPlane | 0 < p 1} from hp)]
  · simp only [comp_apply, indicator_of_notMem (not_congr hh |>.mpr hp),
      indicator_of_notMem (show p ∉ {p : LoopPlane | 0 < p 1} from hp)]




theorem m64Continuous_normalZeroExtension_continuous {u : LoopPlane → ℝ}
    (hu : Continuous u) (hzero : ∀ p : LoopPlane, p 1 = 0 → u p = 0) :
    Continuous ({p : LoopPlane | 0 < p 1}.indicator u) := by
  have hz : ∀ p : LoopPlane, p 0 = 0 → (u ∘ m64BoundaryCoordinateSwap) p = 0 := by
    intro p hp
    exact hzero _ (by simpa [m64BoundaryCoordinateSwap_apply] using hp)
  have hh := (m64Continuous_zeroExtension_continuous
    (hu.comp m64BoundaryCoordinateSwap.continuous) hz).comp m64BoundaryCoordinateSwap.continuous
  rwa [swap_indicator] at hh





theorem m64Continuous_normalZeroExtension_weak {u v : LoopPlane → ℝ} (i : Fin 2)
    (hu : Continuous u) (hzero : ∀ p : LoopPlane, p 1 = 0 → u p = 0)
    (huLp : MemLp u 2 (volume.restrict {p : LoopPlane | 0 < p 1}))
    (hvLp : MemLp v 2 (volume.restrict {p : LoopPlane | 0 < p 1}))
    (hw : HasWeakPartialDeriv i v u {p : LoopPlane | 0 < p 1}) :
    HasWeakPartialDeriv i ({p : LoopPlane | 0 < p 1}.indicator v)
      ({p : LoopPlane | 0 < p 1}.indicator u) univ := by
  let j := Equiv.swap (0 : Fin 2) 1 i
  have hmp := m64BoundaryCoordinateSwap.measurePreserving.restrict_preimage_emb
    m64BoundaryCoordinateSwap.toHomeomorph.measurableEmbedding {p : LoopPlane | 0 < p 1}
  rw [swap_normal_preimage] at hmp
  have hwj : HasWeakPartialDeriv j (v ∘ m64BoundaryCoordinateSwap)
      (u ∘ m64BoundaryCoordinateSwap) (halfSpace 2) := by
    have hh := m64WeakPartialDeriv_coordinateSwap (i := j)
      (show HasWeakPartialDeriv (Equiv.swap (0 : Fin 2) 1 j) v u
        {p : LoopPlane | 0 < p 1} by simpa only [j, Equiv.swap_apply_self] using hw)
    rwa [swap_normal_preimage] at hh
  have hz : ∀ p : LoopPlane, p 0 = 0 → (u ∘ m64BoundaryCoordinateSwap) p = 0 := by
    intro p hp
    exact hzero _ (by simpa [m64BoundaryCoordinateSwap_apply] using hp)
  have hzeroWeak := m64Continuous_zeroExtension_weak j
    (hu.comp m64BoundaryCoordinateSwap.continuous) hz
    (huLp.comp_measurePreserving hmp) (hvLp.comp_measurePreserving hmp) hwj
  have hh := m64WeakPartialDeriv_coordinateSwap (i := i) hzeroWeak
  simpa only [swap_indicator, preimage_univ] using hh

end PoincareConjecture
