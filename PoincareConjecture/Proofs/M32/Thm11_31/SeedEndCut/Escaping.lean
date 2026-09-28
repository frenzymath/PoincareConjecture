import PoincareConjecture.Proofs.M32.Thm11_31.Levels
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32

theorem horn_exists_unique_escaping_component
    {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
    {E : GeneralizedFlowExtension F T} (horn : StrongHorn E epsilon)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K) :
    ∃ x ∈ horn.carrier \ K, ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧
      horn.parameterization '' (univ ×ˢ Ioo b 1) ⊆
        connectedComponentIn (horn.carrier \ K) x ∧
      (∀ L : Set (E.extended.slice T).carrier, IsCompact L →
        ¬ connectedComponentIn (horn.carrier \ K) x ⊆ L) ∧
      (∀ y : (E.extended.slice T).carrier,
        (∀ L : Set (E.extended.slice T).carrier, IsCompact L →
          ¬ connectedComponentIn (horn.carrier \ K) y ⊆ L) →
        connectedComponentIn (horn.carrier \ K) y =
          connectedComponentIn (horn.carrier \ K) x) := by
  classical
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  obtain ⟨b, hb0, hb1, havoid⟩ := horn_exists_tail_avoiding_compact horn K hK
  let V := horn.parameterization '' (univ ×ˢ Ioo b 1)
  let P := horn.parameterization '' (univ ×ˢ Icc 0 b)
  have hsub : V ⊆ horn.carrier \ K := by
    rintro _ ⟨⟨s, t⟩, ⟨_, hbt, ht1⟩, rfl⟩
    have hx := (horn.coordinate (s, ⟨t, hb0.trans hbt.le, ht1⟩)).property
    rw [horn.coordinate_eq] at hx
    exact ⟨hx, havoid s t hbt ht1⟩
  have hV : IsPreconnected V := by
    apply (isPreconnected_univ.prod isPreconnected_Ioo).image
    apply horn.parameterization_smooth.continuousOn.mono
    intro z hz
    exact ⟨hz.1, (neg_lt_zero.mpr horn.collar_pos).trans_le
      (hb0.trans hz.2.1.le), hz.2.2⟩
  have hP : IsCompact P := by
    apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    apply horn.parameterization_smooth.continuousOn.mono
    intro z hz
    exact ⟨hz.1, (neg_lt_zero.mpr horn.collar_pos).trans_le hz.2.1,
      hz.2.2.trans_lt hb1⟩
  have hcover : horn.carrier ⊆ P ∪ V := by
    intro x hx
    let z := horn.coordinate.symm ⟨x, hx⟩
    have hz : horn.parameterization (z.1, (z.2 : ℝ)) = x := by
      rw [← horn.coordinate_eq]
      exact congrArg Subtype.val (horn.coordinate.apply_symm_apply ⟨x, hx⟩)
    rcases le_or_gt (z.2 : ℝ) b with hle | hgt
    · exact Or.inl ⟨(z.1, z.2), ⟨mem_univ _, z.2.property.1, hle⟩, hz⟩
    · exact Or.inr ⟨(z.1, z.2), ⟨mem_univ _, hgt, z.2.property.2⟩, hz⟩
  let s : UnitTwoSphere := Classical.choice (inferInstance : Nonempty UnitTwoSphere)
  let x := horn.parameterization (s, (b + 1) / 2)
  have hx : x ∈ V := by
    refine ⟨(s, (b + 1) / 2), ⟨mem_univ _, ?_, ?_⟩, rfl⟩ <;> linarith
  have htail := hV.subset_connectedComponentIn hx hsub
  refine ⟨x, hsub hx, b, hb0, hb1, htail, ?_, ?_⟩
  · intro L hL hcontain
    exact horn_tail_not_subset_compact horn b hb1 L hL (htail.trans hcontain)
  · intro y hescape
    by_contra hne
    apply hescape P hP
    intro z hz
    rcases hcover (connectedComponentIn_subset (horn.carrier \ K) y hz).1 with hp | ht
    · exact hp
    · exact False.elim (hne ((connectedComponentIn_eq hz).trans
        (connectedComponentIn_eq (htail ht)).symm))

end PoincareConjecture.M32
