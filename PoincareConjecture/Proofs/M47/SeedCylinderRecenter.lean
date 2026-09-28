import PoincareConjecture.Proofs.M47.SeedCylinderSource
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart









set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}




theorem exists_seedCylinder_recenter
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (a : ℝ) (ha : a ∈ I) {r K : ℝ}
    (hrange : ∀ s ∈ Icc (-r ^ 2) 0, a + scale * s ∈ I)
    (V : Set (F.slice (origin + a / scale)).carrier)
    (hV : V ⊆ e.forward a ha '' U)
    (hK : ∀ s (hs : s ∈ I), ∀ x ∈ U,
      (F.connection (origin + s / scale)).curvatureTensorNorm (e.forward s hs x) ≤ K) :
    ∃ d : SurgeryFlowCylinder F (F.slice (origin + a / scale))
        (origin + a / scale) 1 (Icc (-r ^ 2) 0) V,
      (∀ h x, x ∈ V → HEq (d.forward 0 h x) x) ∧
      (∀ s hs x, x ∈ V →
        (F.connection ((origin + a / scale) + s / 1)).curvatureTensorNorm
          (d.forward s hs x) ≤ K) := by
  let chart := M44.cylinderSliceChart e hU a ha
  let phi : ℝ → ℝ := fun s => a + scale * s
  have hmono : StrictMonoOn phi (Icc (-r ^ 2) 0) := by
    intro s _ t _ hst
    simpa only [phi, add_comm] using
      add_lt_add_left (mul_lt_mul_of_pos_left hst e.scale_pos) a
  have hclock (s : ℝ) (_hs : s ∈ Icc (-r ^ 2) 0) :
      (origin + a / scale) + s / 1 = origin + phi s / scale := by
    dsimp only [phi]
    rw [div_one, add_div, mul_div_cancel_left₀ _ e.scale_pos.ne']
    ring
  let shifted := seedCylinderReclock e (by norm_num : (0 : ℝ) < 1)
    ordConnected_Icc phi hrange hmono hclock
  have hsource : V ⊆ chart.symm.source := hV
  have hmaps : MapsTo chart.symm V U := fun _ hx => chart.symm.map_source (hsource hx)
  let d := seedCylinderSource shifted chart.symm V hsource hmaps
  refine ⟨d, ?_, ?_⟩
  · intro h x hx
    have he := seedCylinderReclock_forward_heq e (by norm_num : (0 : ℝ) < 1)
      ordConnected_Icc phi hrange hmono hclock 0 h (chart.symm x)
    change HEq (d.forward 0 h x) (e.forward (phi 0) (hrange 0 h) (chart.symm x)) at he
    have hphi : phi 0 = a := by simp only [phi, mul_zero, add_zero]
    have hterminal : HEq (e.forward (phi 0) (hrange 0 h) (chart.symm x)) x := by
      have hpoint (s : ℝ) (hs : s ∈ I) (hsa : s = a) :
          HEq (e.forward s hs (chart.symm x)) x := by
        subst s
        exact heq_of_eq (chart.right_inv (hV hx))
      exact hpoint _ _ hphi
    exact he.trans hterminal
  · intro s hs x hx
    exact seedCylinderReclock_curvature e (by norm_num : (0 : ℝ) < 1)
      ordConnected_Icc phi hrange hmono hclock hK s hs (chart.symm x) (hmaps hx)

end PoincareConjecture.Proofs.M47
