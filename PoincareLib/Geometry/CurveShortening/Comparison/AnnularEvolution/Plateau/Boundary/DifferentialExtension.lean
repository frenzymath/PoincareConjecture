import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.GradientRecovery
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Actual C1 extension from the continuous full differential

The genuine derivative limit on the convex upper half-disk produces
the within derivative at its diameter. The original map and the
recovered field are retained throughout.
Source: Heinz 1970, pp. 100--101; M64 transverse-conformality derivation;
generalized from the M65 extension proof.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace PoincareMT.M64Boundary

variable {N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin N)

/-- A continuous extension of the actual interior differential makes the same map C1 within
a smaller closed upper half-disk. Source: Heinz 1970, pp. 100--101; the M64
transverse-conformality derivation. Exact proof derivation:
`2026-09-26-transverse-conformality.md`. -/
theorem contDiffOn_halfDisk_of_continuous_differential {R : ℝ} (hR : 0 < R)
    (X : LoopPlane → E)
    (hXc : ContinuousOn X (closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}))
    (hX : ContDiffOn ℝ 1 X (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (D : LoopPlane → LoopPlane →L[ℝ] E)
    (hD : ContinuousOn D (closedBall 0 (R / 2) ∩ {z | 0 ≤ z 1}))
    (hDeq : EqOn D (fderiv ℝ X) (ball 0 (R / 2) ∩ {z | 0 < z 1})) :
    ContDiffOn ℝ 1 X (closedBall 0 (R / 4) ∩ {z | 0 ≤ z 1}) := by
  let U := ball (0 : LoopPlane) (R / 2) ∩ {z | 0 < z 1}
  let S := closedBall (0 : LoopPlane) (R / 2) ∩ {z | 0 ≤ z 1}
  let K := closedBall (0 : LoopPlane) (R / 4) ∩ {z | 0 ≤ z 1}
  have hUS : U ⊆ S := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z 1 from hz.2).le⟩
  have hKS : K ⊆ S := fun z hz =>
    ⟨closedBall_subset_closedBall (by linarith) hz.1, hz.2⟩
  have hSbig : S ⊆ closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1} :=
    fun z hz => ⟨closedBall_subset_closedBall (by linarith) hz.1, hz.2⟩
  have hUbig : U ⊆ ball (0 : LoopPlane) R ∩ {z | 0 < z 1} :=
    fun z hz => ⟨ball_subset_ball (by linarith) hz.1, hz.2⟩
  have hUopen : IsOpen U := isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous)
  have hUconv : Convex ℝ U := (convex_ball _ _).inter
    (convex_halfSpace_gt (show IsLinearMap ℝ (fun z : LoopPlane => z 1) from
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩) 0)
  have hclosure : closure U ⊆ S := closure_minimal hUS
    (isClosed_closedBall.inter (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous))
  have hKclosure : K ⊆ closure U := by
    let pr : LoopPlane →L[ℝ] ℝ := EuclideanSpace.proj 1
    have hsurj : Function.Surjective pr := by
      intro t
      refine ⟨t • EuclideanSpace.basisFun (Fin 2) ℝ 1, ?_⟩
      change (t • EuclideanSpace.basisFun (Fin 2) ℝ 1) 1 = t
      simp [EuclideanSpace.single]
    have hhalf : closure {z : LoopPlane | 0 < z 1} = {z | 0 ≤ z 1} := by
      change closure (pr ⁻¹' Ioi 0) = pr ⁻¹' Ici 0
      rw [pr.closure_preimage hsurj, closure_Ioi]
    intro z hz
    apply isOpen_ball.inter_closure
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff]
      have hh := mem_closedBall_zero_iff.mp hz.1
      linarith
    · rw [hhalf]
      exact hz.2
  have hder (x : LoopPlane) (hx : x ∈ K) : HasFDerivWithinAt X (D x) K x := by
    have hlimit : Tendsto (fderiv ℝ X) (𝓝[U] x) (𝓝 (D x)) := by
      apply ((hD x (hKS hx)).mono_left (nhdsWithin_mono _ hUS)).congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hDeq hz
    have hh := hasFDerivWithinAt_closure_of_tendsto_fderiv
      (hX.differentiableOn_one.mono hUbig) hUconv hUopen
      (fun y hy => (hXc y (hSbig (hclosure hy))).mono (hUS.trans hSbig)) hlimit
    exact hh.mono hKclosure
  change ContDiffOn ℝ ((0 : ℕ∞ω) + 1) X K
  rw [contDiffOn_succ_iff_hasFDerivWithinAt (by norm_num : (0 : ℕ∞ω) ≠ ∞)]
  intro x hx
  refine ⟨K, ?_, ?_, D, hder, contDiffOn_zero.mpr (hD.mono hKS)⟩
  · rw [insert_eq_of_mem hx]
    exact self_mem_nhdsWithin
  · intro h
    norm_num at h

end PoincareMT.M64Boundary
