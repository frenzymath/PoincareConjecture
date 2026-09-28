import PoincareConjecture.Proofs.M25.Topology3D.Space3.CirclePeriodCoordinates
import PoincareConjecture.Proofs.M25.Mathlib.CircleArcs
import Mathlib.Topology.OpenPartialHomeomorph.Composition











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M25.Topology3D



theorem exists_smooth_period_circle_arc (T : ℝ) (hT : 0 < T)
    (a b : ℝ) (_hab : a < b) (hlen : b < a + T) :
    ∃ e : OpenPartialHomeomorph ℝ UnitCircle,
      e.source = Ioo a b ∧
      e.target = periodCircleParam T '' Ioo a b ∧
      (∀ s : ℝ, e s = periodCircleParam T s) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ e e.source ∧
      ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ e.symm e.target := by
  let : Fact (0 < T) := ⟨hT⟩
  obtain ⟨e0, he0source, _, he0⟩ :=
    AddCircle.exists_openPartialHomeomorph_Ioo T a b hlen.le
  let J : AddCircle T ≃ₜ UnitCircle := periodUnitCircleHomeomorph T hT.ne'
  let e := e0.trans J.toOpenPartialHomeomorph
  have hsource : e.source = Ioo a b := by
    simp only [e, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ, he0source]
  have hforward (s : ℝ) : e s = periodCircleParam T s := by
    change J (e0 s) = periodCircleParam T s
    rw [he0]
    exact periodUnitCircleHomeomorph_coe T hT.ne' s
  have htarget : e.target = periodCircleParam T '' Ioo a b := by
    rw [← e.image_source_eq_target, hsource]
    exact congrArg (fun f : ℝ → UnitCircle => f '' Ioo a b) (funext hforward)
  refine ⟨e, hsource, htarget, hforward, ?_, ?_⟩
  · exact (periodCircleParam_contMDiff T).contMDiffOn.congr (fun s _ => hforward s)
  · intro z hz
    let t0 : ℝ := e.symm z
    have ht0 : t0 ∈ Ioo a b := hsource ▸ e.map_target hz
    obtain ⟨s, hs, hright⟩ := exists_periodCircle_local_time T hT.ne' z
    have hsright (y : UnitCircle) : periodCircleParam T (s y) = y := by
      simpa only [Function.comp_apply, id_eq] using congrFun hright y
    have ht0right : periodCircleParam T t0 = z :=
      (hforward t0).symm.trans (e.right_inv hz)
    have hclass : (t0 : AddCircle T) = (s z : AddCircle T) := by
      apply J.injective
      change periodUnitCircleHomeomorph T hT.ne' (t0 : AddCircle T) =
        periodUnitCircleHomeomorph T hT.ne' (s z : AddCircle T)
      rw [periodUnitCircleHomeomorph_coe, periodUnitCircleHomeomorph_coe]
      exact ht0right.trans (hsright z).symm
    have hshiftClass : ((t0 - s z : ℝ) : AddCircle T) = 0 := by
      rw [AddCircle.coe_sub, hclass, sub_self]
    let shifted : UnitCircle → ℝ := fun y => s y + (t0 - s z)
    have hshifted : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ shifted z :=
      hs.add contMDiffAt_const
    have hshiftedRight (y : UnitCircle) : periodCircleParam T (shifted y) = y := by
      change periodCircleParam T (s y + (t0 - s z)) = y
      rw [← periodUnitCircleHomeomorph_coe T hT.ne', AddCircle.coe_add,
        hshiftClass, add_zero, periodUnitCircleHomeomorph_coe]
      exact hsright y
    have hshiftedAt : shifted z = t0 := by
      dsimp only [shifted]
      ring
    have hnear : ∀ᶠ y in 𝓝 z, shifted y ∈ Ioo a b := by
      apply hshifted.continuousAt.preimage_mem_nhds
      rw [hshiftedAt]
      exact isOpen_Ioo.mem_nhds ht0
    have htargetNear : ∀ᶠ y in 𝓝 z, y ∈ e.target := e.open_target.mem_nhds hz
    have hagree : e.symm =ᶠ[𝓝 z] shifted := by
      filter_upwards [hnear, htargetNear] with y hy hytarget
      apply e.injOn (e.map_target hytarget) (hsource.symm ▸ hy)
      rw [e.right_inv hytarget, hforward, hshiftedRight]
    exact (hshifted.congr_of_eventuallyEq hagree).contMDiffWithinAt

end PoincareConjecture.M25.Topology3D
