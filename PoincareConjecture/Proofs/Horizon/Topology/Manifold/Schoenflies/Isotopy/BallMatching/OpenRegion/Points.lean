import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.PointAdjustment
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Connected.Clopen

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

def ballAffineDiffeomorph {n : Nat} (x : EuclideanSpace Real (Fin n))
    {r : Real} (hr : 0 < r) :
    Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞ :=
  let L := (LinearEquiv.smulOfNeZero Real (EuclideanSpace Real (Fin n)) r
    hr.ne').toContinuousLinearEquiv
  let T : Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞ := {
    toEquiv := Equiv.addRight x
    contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
    contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff }
  L.toDiffeomorph.trans T

@[simp] theorem ballAffineDiffeomorph_apply {n : Nat}
    (x z : EuclideanSpace Real (Fin n)) {r : Real} (hr : 0 < r) :
    ballAffineDiffeomorph x hr z = r • z + x := rfl

theorem ballAffineDiffeomorph_image_ball {n : Nat}
    (x : EuclideanSpace Real (Fin n)) {r : Real} (hr : 0 < r) :
    ballAffineDiffeomorph x hr '' ball 0 1 = ball x r := by
  let C := ballAffineDiffeomorph x hr
  have hmem (z : EuclideanSpace Real (Fin n)) : C z ∈ ball x r ↔ z ∈ ball 0 1 := by
    simp only [C, mem_ball, ballAffineDiffeomorph_apply, dist_eq_norm,
      add_sub_cancel_right, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    constructor <;> intro h <;> nlinarith
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hmem z).mpr hz
  · intro hy
    refine ⟨C.symm y, ?_, C.apply_symm_apply y⟩
    exact (hmem _).mp (by simpa only [C.apply_symm_apply] using hy)

theorem exists_supported_point_motion_in_open_region {n : Nat}
    (O : Set (EuclideanSpace Real (Fin n))) (hO : IsOpen O) (hc : IsPreconnected O)
    {x y : EuclideanSpace Real (Fin n)} (hx : x ∈ O) (hy : y ∈ O) :
    ∃ K : Set (EuclideanSpace Real (Fin n)), IsCompact K ∧ K ⊆ O ∧
      ∃ D : Diffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞,
        (∀ z ∉ K, D z = z) ∧ D x = y := by
  let E := EuclideanSpace Real (Fin n)
  let P : E → E → Prop := fun x y =>
    ∃ K : Set E, IsCompact K ∧ K ⊆ O ∧
      ∃ D : Diffeomorph (𝓡 n) (𝓡 n) E E ∞,
        (∀ z ∉ K, D z = z) ∧ D x = y
  apply hc.induction₂ P ?_ ?_ ?_ hx hy
  · intro a ha
    obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO a ha
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a hr)] with b hb
    let C := ballAffineDiffeomorph a hr
    have hCb : ‖C.symm b‖ < 1 := by
      have hmem : C.symm b ∈ ball (0 : E) 1 := by
        have : b ∈ C '' ball 0 1 := by
          rw [show C '' ball 0 1 = ball a r from ballAffineDiffeomorph_image_ball a hr]
          exact hb
        obtain ⟨z, hz, rfl⟩ := this
        simpa only [C.symm_apply_apply] using hz
      simpa only [mem_ball_zero_iff] using hmem
    obtain ⟨s, F, hs, hs1, hF0, hFfix⟩ :=
      Poincare.exists_diffeomorph_move_zero_in_unitBall hCb
    let D := (C.symm.trans F).trans C
    refine ⟨C '' closedBall 0 s, (isCompact_closedBall _ _).image C.continuous,
      ?_, D, ?_, ?_⟩
    · apply (image_mono (closedBall_subset_ball hs1)).trans
      exact (ballAffineDiffeomorph_image_ball a hr).symm ▸ hrO
    · intro z hz
      change C (F (C.symm z)) = z
      have hn : s ≤ ‖C.symm z‖ := by
        by_contra h
        exact hz ⟨C.symm z, mem_closedBall_zero_iff.mpr (le_of_lt (lt_of_not_ge h)),
          C.apply_symm_apply z⟩
      rw [hFfix _ hn, C.apply_symm_apply]
    · change C (F (C.symm a)) = b
      have hC0 : C 0 = a := by simp [C]
      rw [← hC0, C.symm_apply_apply, hF0, C.apply_symm_apply]
  · intro a b c _ _ _ hab hbc
    obtain ⟨K, hK, hKO, F, hF, hFab⟩ := hab
    obtain ⟨L, hL, hLO, G, hG, hGbc⟩ := hbc
    refine ⟨K ∪ L, hK.union hL, union_subset hKO hLO, F.trans G, ?_, ?_⟩
    · intro z hz
      change G (F z) = z
      rw [hF z (fun h => hz (Or.inl h)), hG z (fun h => hz (Or.inr h))]
    · change G (F a) = c
      rw [hFab, hGbc]
  · intro a b _ _ hab
    obtain ⟨K, hK, hKO, F, hF, hFab⟩ := hab
    refine ⟨K, hK, hKO, F.symm, ?_, ?_⟩
    · intro z hz
      apply F.injective
      change F (F.symm z) = F z
      rw [F.apply_symm_apply, hF z hz]
    · rw [← hFab, F.symm_apply_apply]

end Poincare.Manifold.Schoenflies
