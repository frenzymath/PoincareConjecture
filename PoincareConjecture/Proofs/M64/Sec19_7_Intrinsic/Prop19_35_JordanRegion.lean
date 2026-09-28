import PoincareConjecture.Definitions.M64Annulus
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Jordan.Domains













noncomputable section
set_option autoImplicit false

open Set Function Metric
open scoped Topology

namespace PoincareConjecture





theorem m64Intrinsic_exists_jordan_region
    {γ : ℝ → AnnulusCoordinates} {T : ℝ} (hT : 0 < T)
    (hc : ContinuousOn γ (Icc 0 T)) (hend : γ 0 = γ T)
    (hinj : InjOn γ (Ico 0 T)) :
    ∃ U V : Set AnnulusCoordinates,
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ Disjoint U V ∧
      U ∪ V = (γ '' Icc 0 T)ᶜ ∧
      frontier U = γ '' Icc 0 T ∧ frontier V = γ '' Icc 0 T ∧
      IsCompact (closure U) := by
  let : Fact (0 < T) := ⟨hT⟩
  let f : AddCircle T → AnnulusCoordinates := AddCircle.liftIco T 0 γ
  have hfc : Continuous f := AddCircle.liftIco_zero_continuous hend hc
  have hfi : Injective f := by
    intro x y hxy
    apply (AddCircle.equivIco T 0).injective
    apply Subtype.ext
    apply hinj
    · simpa only [zero_add] using (AddCircle.equivIco T 0 x).property
    · simpa only [zero_add] using (AddCircle.equivIco T 0 y).property
    · exact hxy
  have hfrange : range f = γ '' Ico 0 T := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(AddCircle.equivIco T 0 x).val, ?_, rfl⟩
      simpa only [zero_add] using (AddCircle.equivIco T 0 x).property
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(t : AddCircle T), AddCircle.liftIco_zero_coe_apply ht⟩
  have himage : γ '' Ico 0 T = γ '' Icc 0 T := by
    apply Subset.antisymm (image_mono Ico_subset_Icc_self)
    rintro p ⟨t, ht, rfl⟩
    rcases ht.2.eq_or_lt with rfl | htT
    · exact ⟨0, ⟨le_rfl, hT⟩, hend⟩
    · exact ⟨t, ⟨ht.1, htT⟩, rfl⟩
  let e : sphere (0 : AnnulusCoordinates) 1 ≃ₜ AddCircle T :=
    Poincare.Topology.Plane.Jordan.Arcs.spherePlaneHomeoCircle.trans
      (AddCircle.homeomorphCircle hT.ne').symm
  have hrange : range (f ∘ e) = γ '' Icc 0 T := by
    rw [e.surjective.range_comp, hfrange, himage]
  obtain ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hdisj, hunion, hfU, hfV, hcompact⟩ :=
    Poincare.Topology.Plane.Jordan.exists_complementary_domains
      (hfc.comp e.continuous) (hfi.comp e.injective)
  rw [hrange] at hunion hfU hfV
  exact ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hdisj, hunion, hfU, hfV, hcompact⟩

end PoincareConjecture
