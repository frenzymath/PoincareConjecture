import PoincareConjecture.Proofs.M65.Mathlib.Plateau.ThreePointNormalization
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.SpanningDiskReparameterization

set_option autoImplicit false

open Set Metric Complex
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m65SpanningDisk_threePointNormalization {g : RiemannianMetric 3 M}
    {γ : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g γ)
    (a b c : LoopCircle) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ D' : LipschitzSpanningDisk g γ, D'.area = D.area ∧
      (D'.reparameterization.inverse a).val = orthonormalBasisOneI.repr 1 ∧
      (D'.reparameterization.inverse b).val = orthonormalBasisOneI.repr (-1) ∧
      ((D'.reparameterization.inverse c).val = orthonormalBasisOneI.repr I ∨
        (D'.reparameterization.inverse c).val = orthonormalBasisOneI.repr (-I)) := by
  let e := orthonormalBasisOneI.repr
  let old := fun z : LoopCircle => e.symm (D.reparameterization.inverse z).val
  have hold : Function.Injective old := by
    intro x y hxy
    apply D.reparameterization.right_inverse.injective
    apply Subtype.ext
    exact e.symm.injective hxy
  have hnorm (z : LoopCircle) : ‖old z‖ = 1 := by
    dsimp only [old]
    rw [e.symm.norm_map, (D.reparameterization.inverse z).property]
  obtain ⟨φ, ψ, hφdisk, hψdisk, hφcircle, hψcircle, hleft, hright,
      hφsmooth, hψsmooth, ha, hb, hc⟩ :=
    exists_plateau_threePoint_normalization (hnorm a) (hnorm b) (hnorm c)
      (fun h => hab (hold h)) (fun h => hac (hold h)) (fun h => hbc (hold h))
  let φP := fun z : LoopPlane => e (φ (e.symm z))
  let ψP := fun z : LoopPlane => e (ψ (e.symm z))
  have hnormP (z : LoopPlane) : ‖e.symm z‖ = ‖z‖ := e.symm.norm_map z
  have hφPdisk : MapsTo φP loopDiskSet loopDiskSet := by
    intro z hz
    apply mem_closedBall_zero_iff.mpr
    dsimp only [φP]
    rw [e.norm_map]
    exact hφdisk _ ((hnormP z).trans_le (mem_closedBall_zero_iff.mp hz))
  have hψPdisk : MapsTo ψP loopDiskSet loopDiskSet := by
    intro z hz
    apply mem_closedBall_zero_iff.mpr
    dsimp only [ψP]
    rw [e.norm_map]
    exact hψdisk _ ((hnormP z).trans_le (mem_closedBall_zero_iff.mp hz))
  have hφPcircle (z : LoopPlane) (hz : ‖z‖ = 1) : ‖φP z‖ = 1 := by
    dsimp only [φP]
    rw [e.norm_map]
    exact hφcircle _ ((hnormP z).trans hz)
  have hψPcircle (z : LoopPlane) (hz : ‖z‖ = 1) : ‖ψP z‖ = 1 := by
    dsimp only [ψP]
    rw [e.norm_map]
    exact hψcircle _ ((hnormP z).trans hz)
  have hleftP (z : LoopPlane) (hz : z ∈ loopDiskSet) : ψP (φP z) = z := by
    dsimp only [φP, ψP]
    rw [e.symm_apply_apply, hleft _ ((hnormP z).trans_le (mem_closedBall_zero_iff.mp hz)),
      e.apply_symm_apply]
  have hrightP (z : LoopPlane) (hz : z ∈ loopDiskSet) : φP (ψP z) = z := by
    dsimp only [φP, ψP]
    rw [e.symm_apply_apply, hright _ ((hnormP z).trans_le (mem_closedBall_zero_iff.mp hz)),
      e.apply_symm_apply]
  have hφP (z : LoopPlane) (hz : z ∈ loopDiskSet) : ContDiffAt ℝ 1 φP z := by
    have h : ContDiffAt ℝ 1 φ (e.symm z) :=
      ((hφsmooth _ ((hnormP z).trans_le (mem_closedBall_zero_iff.mp hz))).restrict_scalars ℝ).of_le
        (by simp)
    exact e.toContinuousLinearEquiv.contDiff.contDiffAt.comp z
      (h.comp z e.symm.toContinuousLinearEquiv.contDiff.contDiffAt)
  have hψP (z : LoopPlane) (hz : z ∈ loopDiskSet) : ContDiffAt ℝ 1 ψP z := by
    have h : ContDiffAt ℝ 1 ψ (e.symm z) :=
      ((hψsmooth _ ((hnormP z).trans_le (mem_closedBall_zero_iff.mp hz))).restrict_scalars ℝ).of_le
        (by simp)
    exact e.toContinuousLinearEquiv.contDiff.contDiffAt.comp z
      (h.comp z e.symm.toContinuousLinearEquiv.contDiff.contDiffAt)
  obtain ⟨D', _, harea, hboundary⟩ := m65SpanningDisk_reparameterize D ψP φP
    hψP hφP hψPdisk hφPdisk hψPcircle hφPcircle hrightP hleftP
  have hinverse (z : LoopCircle) : (D'.reparameterization.inverse z).val =
      φP (D.reparameterization.inverse z).val := by
    let w := D'.reparameterization.inverse z
    have hpre : (⟨ψP w, hψPcircle w w.property⟩ : LoopCircle) =
        D.reparameterization.inverse z := by
      apply D.reparameterization.left_inverse.injective
      rw [← hboundary w, D.reparameterization.right_inverse]
      exact D'.reparameterization.right_inverse z
    calc
      _ = φP (ψP w) := (hrightP w (mem_closedBall_zero_iff.mpr w.property.le)).symm
      _ = _ := congrArg φP (congrArg Subtype.val hpre)
  refine ⟨D', harea, ?_, ?_, ?_⟩
  · rw [hinverse]
    exact congrArg e ha
  · rw [hinverse]
    exact congrArg e hb
  · rw [hinverse]
    exact hc.imp (congrArg e) (congrArg e)

end PoincareConjecture
