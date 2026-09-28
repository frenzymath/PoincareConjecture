import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCriticalEmbedding
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RadialFlipGeometry












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.BoundaryTangential

namespace PoincareConjecture





def m64BoundaryCoordinateSwap : LoopPlane ≃ₗᵢ[ℝ] LoopPlane :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)




theorem m64BoundaryCoordinateSwap_apply (p : LoopPlane) (i : Fin 2) :
    m64BoundaryCoordinateSwap p i = p (Equiv.swap (0 : Fin 2) 1 i) := rfl




theorem m64BoundaryCoordinateSwap_involutive :
    Function.Involutive m64BoundaryCoordinateSwap := by
  intro p
  ext i
  simp only [m64BoundaryCoordinateSwap_apply, Equiv.swap_apply_self]




theorem m64BoundaryCoordinateSwap_twice (p : LoopPlane) :
    m64BoundaryCoordinateSwap (m64BoundaryCoordinateSwap p) = p :=
  m64BoundaryCoordinateSwap_involutive p





theorem m64BoundaryCoordinateSwap_basis (i : Fin 2) :
    m64BoundaryCoordinateSwap (EuclideanSpace.single i 1) =
      EuclideanSpace.single (Equiv.swap (0 : Fin 2) 1 i) 1 :=
  LinearIsometryEquiv.piLpCongrLeft_single _ _ _




theorem m64BoundaryCoordinateSwap_fderiv {phi : LoopPlane → ℝ}
    (hp : Differentiable ℝ phi) (p : LoopPlane) (i : Fin 2) :
    fderiv ℝ (phi ∘ m64BoundaryCoordinateSwap) p (EuclideanSpace.single i 1) =
      fderiv ℝ phi (m64BoundaryCoordinateSwap p)
        (EuclideanSpace.single (Equiv.swap (0 : Fin 2) 1 i) 1) := by
  have hd : HasFDerivAt m64BoundaryCoordinateSwap
      m64BoundaryCoordinateSwap.toContinuousLinearEquiv.toContinuousLinearMap p :=
    m64BoundaryCoordinateSwap.toContinuousLinearEquiv.hasFDerivAt
  rw [fderiv_comp p (hp _) m64BoundaryCoordinateSwap.differentiableAt,
    ContinuousLinearMap.comp_apply, hd.fderiv]
  change fderiv ℝ phi (m64BoundaryCoordinateSwap p)
    (m64BoundaryCoordinateSwap (EuclideanSpace.single i 1)) = _
  rw [m64BoundaryCoordinateSwap_basis]





theorem m64WeakPartialDeriv_coordinateSwap
    {S : Set LoopPlane} {u v : LoopPlane → ℝ} {i : Fin 2}
    (hv : HasWeakPartialDeriv (Equiv.swap (0 : Fin 2) 1 i) v u S) :
    HasWeakPartialDeriv i (v ∘ m64BoundaryCoordinateSwap)
      (u ∘ m64BoundaryCoordinateSwap) (m64BoundaryCoordinateSwap ⁻¹' S) := by
  let T := m64BoundaryCoordinateSwap.toHomeomorph
  have hmp := m64BoundaryCoordinateSwap.measurePreserving.restrict_preimage_emb
    T.measurableEmbedding S
  intro phi hp hc hs
  have hpc : ContDiff ℝ ∞ (phi ∘ T) :=
    hp.comp m64BoundaryCoordinateSwap.toContinuousLinearEquiv.contDiff
  have hps : tsupport (phi ∘ T) ⊆ S := by
    rw [tsupport_comp_eq_preimage]
    intro p hpS
    have hh := hs hpS
    change T (T p) ∈ S at hh
    exact m64BoundaryCoordinateSwap_twice p ▸ hh
  have heq := hv (phi ∘ T) hpc (hc.comp_homeomorph T) hps
  have hleft := hmp.integral_comp T.measurableEmbedding
    (fun p => u p * fderiv ℝ (phi ∘ T) p
      (EuclideanSpace.single (Equiv.swap (0 : Fin 2) 1 i) 1))
  have hright := hmp.integral_comp T.measurableEmbedding
    (fun p => v p * (phi ∘ T) p)
  change (∫ p in T ⁻¹' S, u (T p) * fderiv ℝ (phi ∘ m64BoundaryCoordinateSwap)
      (m64BoundaryCoordinateSwap p) (EuclideanSpace.single (Equiv.swap (0 : Fin 2) 1 i) 1)) = _
    at hleft
  simp only [m64BoundaryCoordinateSwap_fderiv (hp.differentiable (by simp)),
    m64BoundaryCoordinateSwap_twice, Equiv.swap_apply_self] at hleft
  change (∫ p in T ⁻¹' S, v (T p) * phi (m64BoundaryCoordinateSwap
    (m64BoundaryCoordinateSwap p))) = _ at hright
  simp only [m64BoundaryCoordinateSwap_twice] at hright
  change (∫ p in T ⁻¹' S, u (T p) * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
    -(∫ p in T ⁻¹' S, v (T p) * phi p)
  rw [hleft, hright]
  simpa only [T, m64BoundaryCoordinateSwap_fderiv (hp.differentiable (by simp)),
    Equiv.swap_apply_self] using heq




theorem m64MemW1p_coordinateSwap
    {S : Set LoopPlane} {u : LoopPlane → ℝ} {p : ℝ≥0∞}
    (hu : MemW1p p u S) :
    MemW1p p (u ∘ m64BoundaryCoordinateSwap) (m64BoundaryCoordinateSwap ⁻¹' S) := by
  have hmp := m64BoundaryCoordinateSwap.measurePreserving.restrict_preimage_emb
    m64BoundaryCoordinateSwap.toHomeomorph.measurableEmbedding S
  refine ⟨hu.1.comp_measurePreserving hmp, ?_⟩
  intro i
  obtain ⟨v, hv, hw⟩ := hu.2 (Equiv.swap (0 : Fin 2) 1 i)
  exact ⟨v ∘ m64BoundaryCoordinateSwap, hv.comp_measurePreserving hmp,
    m64WeakPartialDeriv_coordinateSwap hw⟩





theorem m64NormalHalfPlane_H1_memLp {u : LoopPlane → ℝ}
    (hc : HasCompactSupport u) (hu : MemW1p 2 u {p : LoopPlane | 0 < p 1})
    {q : ℝ} (hq : 1 ≤ q) :
    MemLp u (ENNReal.ofReal q) (volume.restrict {p : LoopPlane | 0 < p 1}) := by
  have hpre : m64BoundaryCoordinateSwap ⁻¹' {p : LoopPlane | 0 < p 1} = halfSpace 2 := by
    ext p
    simp [halfSpace, m64BoundaryCoordinateSwap_apply]
  have hpre' : m64BoundaryCoordinateSwap ⁻¹' halfSpace 2 = {p : LoopPlane | 0 < p 1} := by
    ext p
    simp [halfSpace, m64BoundaryCoordinateSwap_apply]
  have hs := m64MemW1p_coordinateSwap hu
  rw [hpre] at hs
  have hlp := m64HalfSpace_H1_memLp (hc.comp_homeomorph
    m64BoundaryCoordinateSwap.toHomeomorph) hs hq
  have hmp := m64BoundaryCoordinateSwap.measurePreserving.restrict_preimage_emb
    m64BoundaryCoordinateSwap.toHomeomorph.measurableEmbedding (halfSpace 2)
  rw [hpre'] at hmp
  have hh := hlp.comp_measurePreserving hmp
  change MemLp (fun p => u (m64BoundaryCoordinateSwap (m64BoundaryCoordinateSwap p)))
    (ENNReal.ofReal q) (volume.restrict {p : LoopPlane | 0 < p 1}) at hh
  simpa only [m64BoundaryCoordinateSwap_twice] using hh

end PoincareConjecture
