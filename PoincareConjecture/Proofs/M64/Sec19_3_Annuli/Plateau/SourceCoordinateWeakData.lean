import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.SourceAffineGeometry
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundedCoordinateWeakChain









noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology ContDiff
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture




theorem m64SourceCoordinate_weak_data {m n : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)}
    (a : LoopPlane) (s : ℝ) (hs : s ≠ 0) {rho R kappa : ℝ}
    (hR : 0 < R) (hk : 0 ≤ kappa)
    (hD : ‖(m64SourceScale s hs).toContinuousLinearMap‖ ≤ kappa)
    (hsmall : kappa * (2 * R) < rho)
    (hu : ContinuousOn u (closedBall a rho))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball a rho)))
    (hweak : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) (ball a rho))
    {H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    (hH : ContDiff ℝ 1 H) {K : ℝ} (hK : 0 < K) (hDH : ∀ y, ‖fderiv ℝ H y‖ ≤ K) :
    let Phi := m64SourceAffine a s hs
    let v := H ∘ (u ∘ Phi)
    let W := fun i p => fderiv ℝ H (u (Phi p)) (m64SourceScaleFactor s i • V i (Phi p))
    MemLp v 2 (volume.restrict (ball (0 : LoopPlane) (2 * R))) ∧
      (∀ i, MemLp (W i) 2 (volume.restrict (ball (0 : LoopPlane) (2 * R)))) ∧
      (∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => v p j)
        (ball (0 : LoopPlane) R)) ∧
      ContinuousOn v (closedBall (0 : LoopPlane) (2 * R)) := by
  let Phi := m64SourceAffine a s hs
  let U := u ∘ Phi
  let V' := fun i p => m64SourceScaleFactor s i • V i (Phi p)
  have hmaps : MapsTo Phi (closedBall (0 : LoopPlane) (2 * R)) (ball a rho) :=
    m64SourceAffine_mapsTo_ball a s hs hk hD hsmall
  have hsub : ball (0 : LoopPlane) (2 * R) ⊆ Phi ⁻¹' ball a rho :=
    fun p hp => hmaps (ball_subset_closedBall hp)
  have hU : ContinuousOn U (closedBall (0 : LoopPlane) (2 * R)) :=
    hu.comp Phi.continuous.continuousOn (fun p hp => ball_subset_closedBall (hmaps hp))
  have hcols (i : Fin 2) : MemLp (V' i) 2 (volume.restrict (ball (0 : LoopPlane) (2 * R))) := by
    have h := (m64SourceAffine_memLp (hV i) a s hs).mono_measure
      (Measure.restrict_mono_set volume hsub)
    simpa +instances only [V', Pi.smul_apply, Function.comp_apply] using!
      h.const_smul (m64SourceScaleFactor s i)
  have hw (i : Fin 2) (j : Fin m) :
      HasWeakPartialDeriv i (fun p => V' i p j) (fun p => U p j)
        (ball (0 : LoopPlane) (2 * R)) := by
    have h := (m64SourceAffine_weakPartial (hweak i j) a s hs).restrict isOpen_ball hsub
    simpa only [U, V', Phi, Function.comp_def, PiLp.smul_apply, smul_eq_mul] using h
  obtain ⟨hv, hW, hchain⟩ := m64BoundedCoordinate_weak_chain hR
    (by linarith : R < 2 * R) hU hcols hw hH hK hDH
  exact ⟨hv, hW, hchain, hH.continuous.comp_continuousOn hU⟩

end PoincareConjecture
