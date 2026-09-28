import PoincareConjecture.Proofs.M47.CanonicalNeckCylinderForward









set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M47



theorem neck_buffer_regularSlab_forward
    {F : SurgeryFlowData.{u}} {T c : ℝ} {I : Set ℝ} {U : Set (F.slice T).carrier}
    (E : SurgeryFlowCylinder F (F.slice T) T 1 I U) (hzero : (0 : ℝ) ∈ I)
    (hbased : ∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x)
    (hTc : T < c) (hJ : Icc T c ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc T c))
    (s : ℝ) (hs : s ∈ I) (hphysical : T + s / 1 ∈ Icc T c)
    (x : (F.slice T).carrier) (hx : x ∈ U) :
    E.forward s hs x =
      (F.regular_slabs T c hTc hJ hfree).identify ⟨T + s / 1, hphysical⟩ x := by
  let S := F.regular_slabs T c hTc hJ hfree
  have hzeroSlab : T + 0 / 1 ∈ Icc T c := by
    simpa only [zero_div, add_zero] using (show T ∈ Icc T c from ⟨le_rfl, hTc.le⟩)
  have hidentify (t : ℝ) (ht : t = T) (htS : t ∈ Icc T c) :
      HEq (S.identify ⟨t, htS⟩ x) x := by
    subst t
    exact heq_of_eq (S.initial_identify x)
  have hzeroPoint : E.forward 0 hzero x = S.identify ⟨T + 0 / 1, hzeroSlab⟩ x :=
    eq_of_heq ((hbased hzero x hx).trans
      (hidentify _ (by simp only [zero_div, add_zero]) hzeroSlab).symm)
  have htransport := E.slab_compatibility T c hTc hJ hfree
    0 hzero s hs hzeroSlab hphysical x hx
  change S.identify ⟨T + s / 1, hphysical⟩
    ((S.identify ⟨T + 0 / 1, hzeroSlab⟩).symm (E.forward 0 hzero x)) =
      E.forward s hs x at htransport
  rw [hzeroPoint, Diffeomorph.symm_apply_apply] at htransport
  exact htransport.symm

end PoincareConjecture.Proofs.M47
