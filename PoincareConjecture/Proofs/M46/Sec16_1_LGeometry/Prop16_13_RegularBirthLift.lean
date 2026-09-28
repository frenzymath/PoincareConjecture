import PoincareConjecture.Proofs.M33.GuardedCylinders
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalRestriction










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46




theorem exists_capCylinder_regular_birth_lift
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {origin scale : ℝ} {I : Set ℝ}
    {U : Set (F.slice origin).carrier} (hU : IsOpen U)
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale I U)
    (hzero : (0 : ℝ) ∈ I) (hnonneg : ∀ s ∈ I, 0 ≤ s)
    (hbase : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (htime : ∀ s ∈ I, origin + s / scale ∈ H.generalized.interval) :
    ∃ d : GeneralizedFlowCylinder H.generalized (F.slice origin) origin scale I
        (U ∩ m33RegularRegion F origin),
      (∀ s hs x, x ∈ U ∩ m33RegularRegion F origin →
        H.history.forward (origin + s / scale) (htime s hs)
          (d.forward s hs x) = e.forward s hs x) ∧
      (∀ s hs x, x ∈ U ∩ m33RegularRegion F origin →
        ∀ v w : TangentSpace (𝓡 3) x,
          d.pullbackInner s hs x v w = e.pullbackInner s hs x v w) := by
  have horigin : origin ∈ H.generalized.interval := by simpa using htime 0 hzero
  have hopen : IsOpen (m33RegularRegion F origin) := by
    rw [← H.regular_range origin horigin]
    exact (H.history.forward_openEmbedding origin horigin).isOpen_range
  let small := M44.restrictCylinderSource e
    (inter_subset_left : U ∩ m33RegularRegion F origin ⊆ U)
  have hregular : ∀ s hs,
      small.forward s hs '' (U ∩ m33RegularRegion F origin) ⊆
        m33RegularRegion F (origin + s / scale) := by
    intro s hs
    by_cases hz : s = 0
    · subst s
      rintro y ⟨x, ⟨hxU, hxreg⟩, rfl⟩
      have heq : (⟨origin + 0 / scale, small.forward 0 hs x⟩ : Σ t, (F.slice t).carrier) =
          ⟨origin, x⟩ := Sigma.ext (by simp) (hbase hs x hxU)
      exact (congrArg (fun p : Σ t, (F.slice t).carrier =>
        p.2 ∈ m33RegularRegion F p.1) heq).mpr hxreg
    · apply small.regular_image_of_earlier hs
      exact ⟨0, hzero, lt_of_le_of_ne (hnonneg s hs) (Ne.symm hz)⟩
  exact H.cylinders_from_surgery (F.slice origin) origin scale I
    (U ∩ m33RegularRegion F origin) (hU.inter hopen) htime small hregular

end PoincareConjecture.Proofs.M46
