import PoincareConjecture.Proofs.M38.ProjectiveTopology

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

theorem projective_quotient_localHomeomorph :
    IsLocalHomeomorph (Quotient.mk' : UnitThreeSphere → RealProjectiveThree) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro a
  let V : Set UnitThreeSphere := {x | 0 < inner ℝ a.val x.val}
  have hopen : IsOpen V :=
    isOpen_lt continuous_const (continuous_const.inner continuous_subtype_val)
  have ha : a ∈ V := by
    change 0 < inner ℝ a.val a.val
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere a]
    norm_num
  refine ⟨V, hopen.mem_nhds ha, ?_⟩
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_quotient_mk'.comp continuous_subtype_val) ?_
    (projective_open_quotient.isOpenMap.domRestrict hopen)
  intro x y hxy
  have hfiber : x.1 = y.1 ∨ x.1 = -y.1 := Quotient.exact hxy
  rcases hfiber with h | h
  · exact Subtype.ext h
  · have hx : 0 < inner ℝ a.val x.1.val := x.2
    have hy : 0 < inner ℝ a.val y.1.val := y.2
    rw [h] at hx
    change 0 < inner ℝ a.val (-y.1.val) at hx
    rw [inner_neg_right] at hx
    linarith

theorem projectiveLift_eventually_id_or_neg {g : UnitThreeSphere → UnitThreeSphere}
    {W : Set UnitThreeSphere} (hW : IsOpen W) (hg : ContinuousOn g W)
    (hfiber : ∀ x ∈ W, (Quotient.mk' (g x) : RealProjectiveThree) = Quotient.mk' x)
    {x : UnitThreeSphere} (hx : x ∈ W) :
    g =ᶠ[𝓝 x] id ∨ g =ᶠ[𝓝 x] Neg.neg := by
  have hcont : ContinuousAt g x := (hg x hx).continuousAt (hW.mem_nhds hx)
  rcases (Quotient.exact (hfiber x hx) : g x = x ∨ g x = -x) with h | h
  · left
    have hn : g x ≠ -x := by
      rw [h]
      exact (three_sphere_neg_ne x).symm
    filter_upwards [hW.mem_nhds hx,
      (hcont.ne_iff_eventually_ne continuous_neg.continuousAt).mp hn] with y hy hne
    exact (Quotient.exact (hfiber y hy) : g y = y ∨ g y = -y).resolve_right hne
  · right
    have hn : g x ≠ x := by
      rw [h]
      exact three_sphere_neg_ne x
    filter_upwards [hW.mem_nhds hx,
      (hcont.ne_iff_eventually_ne continuous_id.continuousAt).mp hn] with y hy hne
    exact (Quotient.exact (hfiber y hy) : g y = y ∨ g y = -y).resolve_left hne

theorem projectiveLift_contMDiffOn {g : UnitThreeSphere → UnitThreeSphere}
    {W : Set UnitThreeSphere} (hW : IsOpen W) (hg : ContinuousOn g W)
    (hfiber : ∀ x ∈ W, (Quotient.mk' (g x) : RealProjectiveThree) = Quotient.mk' x) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ g W := by
  intro x hx
  rcases projectiveLift_eventually_id_or_neg hW hg hfiber hx with h | h
  · exact (contMDiffAt_id.congr_of_eventuallyEq h).contMDiffWithinAt
  · exact ((contMDiff_neg_sphere (n := 3) (m := ∞) x).congr_of_eventuallyEq h).contMDiffWithinAt

theorem projective_sheet_transition_smooth (a : UnitThreeSphere) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (projective_quotient_localHomeomorph.localInverseAt a ∘
        (Quotient.mk' : UnitThreeSphere → RealProjectiveThree))
      ((Quotient.mk' : UnitThreeSphere → RealProjectiveThree) ⁻¹'
        (projective_quotient_localHomeomorph.localInverseAt a).source) := by
  let e := projective_quotient_localHomeomorph.localInverseAt a
  apply projectiveLift_contMDiffOn
    (e.open_source.preimage continuous_quotient_mk')
    (e.continuousOn.comp continuous_quotient_mk'.continuousOn (fun _ hx => hx))
  intro x hx
  exact projective_quotient_localHomeomorph.apply_localInverseAt_of_mem hx

end PoincareConjecture.M38
