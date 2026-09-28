import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Tails
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.RadialCylinder










set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareConjecture.OpenCylinderModel

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]



theorem compact_cut_sides_escape (U V : Opens M) (T : OpenCylinderModel (V : Set M))
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U)
    (F : RoundCylinderSpace ≃ₜ (U ⊓ V : Opens M))
    (hclosed : ∀ p : RoundCylinderSpace, (F p : M) ∈ K ↔ p.2 ≤ 0)
    (hinterior : ∀ p : RoundCylinderSpace, (F p : M) ∈ interior K ↔ p.2 < 0) :
    ∀ L : Set M, IsCompact L → L ⊆ V →
      ¬ (V : Set M) ∩ interior K ⊆ L ∧ ¬ (V : Set M) \ K ⊆ L := by
  classical
  let j : RoundCylinderSpace → M := fun p => F p
  have hj : Continuous j := continuous_subtype_val.comp F.continuous
  have hbound (Q : Set M) (hQ : IsCompact Q) (hQW : Q ⊆ (U ⊓ V : Opens M)) :
      ∃ r : ℝ, r < 0 ∧ ∀ p : RoundCylinderSpace, j p ∈ Q → r < p.2 := by
    have hsub : IsCompact ((Subtype.val : (U ⊓ V : Opens M) → M) ⁻¹' Q) :=
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hQ
        (fun x hx => ⟨⟨x, hQW hx⟩, rfl⟩)
    have hh := ((hsub.image F.symm.continuous).image continuous_snd).bddBelow
    obtain ⟨l, hl⟩ := hh
    refine ⟨min l 0 - 1, by linarith [min_le_right l 0], ?_⟩
    intro p hp
    have hpl : l ≤ p.2 := hl ⟨p, ⟨F p, hp, F.symm_apply_apply p⟩, rfl⟩
    linarith [min_le_left l 0]
  let q : UnitTwoSphere := Classical.choice
    ((NormedSpace.sphere_nonempty.mpr (zero_le_one : (0 : ℝ) ≤ 1)).to_subtype)
  let S := T.coordinate '' (univ ×ˢ Icc (1 / 2 : ℝ) (1 / 2))
  have hS : IsCompact S := T.isCompact_coordinate_slab (by norm_num) (by norm_num)
  have hSV : S ⊆ V := T.coordinate_slab_subset (by norm_num) (by norm_num)
  obtain ⟨r, hr, hdeep⟩ := hbound (K ∩ S) (hK.inter_right hS.isClosed)
    (fun _ hx => ⟨hKU hx.1, hSV hx.2⟩)
  let P := j '' (univ ×ˢ Iio r)
  have hPV : P ⊆ V := by
    rintro _ ⟨p, _, rfl⟩
    exact (F p).property.2
  have hPS : Disjoint P S := by
    apply disjoint_left.mpr
    intro x hx hxS
    obtain ⟨p, hp, rfl⟩ := hx
    have hpK := (hclosed p).mpr (hp.2.trans hr).le
    exact lt_asymm (hdeep p ⟨hpK, hxS⟩) hp.2
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  have hPc : IsConnected P :=
    (isConnected_univ.prod isConnected_Iio).image j hj.continuousOn
  have hhalf : (∀ x ∈ P, (T.inverse x).2 < 1 / 2) ∨
      (∀ x ∈ P, 1 / 2 < (T.inverse x).2) := by
    have hh : IsPreconnected ((fun x => (T.inverse x).2) '' P) :=
      hPc.isPreconnected.image _ (T.inverse_smooth.continuousOn.snd.mono hPV)
    have hsub : (fun x => (T.inverse x).2) '' P ⊆ Iio (1 / 2) ∪ Ioi (1 / 2) := by
      rintro t ⟨x, hx, rfl⟩
      have hne : (T.inverse x).2 ≠ 1 / 2 := by
        intro heq
        exact disjoint_left.mp hPS hx
          ⟨T.inverse x, ⟨mem_univ _, heq.ge, heq.le⟩, T.right_inverse (hPV hx)⟩
      exact lt_or_gt_of_ne hne
    rcases hh.subset_or_subset isOpen_Iio isOpen_Ioi
        (disjoint_left.mpr fun _ hl hu => lt_asymm hl hu) hsub with hh | hh
    · exact Or.inl fun x hx => hh (mem_image_of_mem _ hx)
    · exact Or.inr fun x hx => hh (mem_image_of_mem _ hx)
  intro L hL hLV
  constructor
  · intro hAL
    obtain ⟨a, ha, havoid⟩ := hbound (K ∩ L) (hK.inter_right hL.isClosed)
      (fun _ hx => ⟨hKU hx.1, hLV hx.2⟩)
    let p : RoundCylinderSpace := (q, a - 1)
    have hp : p.2 < 0 := by dsimp [p]; linarith
    have hpK := (hinterior p).mpr hp
    have h := havoid p ⟨interior_subset hpK, hAL ⟨(F p).property.2, hpK⟩⟩
    dsimp [p] at h
    linarith
  · intro hBL
    let Z := j '' (univ ×ˢ Icc r 0)
    have hZ : IsCompact Z := (isCompact_univ.prod isCompact_Icc).image hj
    have hZV : Z ⊆ V := by
      rintro _ ⟨p, _, rfl⟩
      exact (F p).property.2
    obtain ⟨a, ha, hn, hp, _, _⟩ := T.exists_tails_disjoint_of_isCompact
      (hL.union hZ) (union_subset hLV hZV)
    have ha1 : a ∈ Ioo (0 : ℝ) 1 := ⟨ha.1, by linarith [ha.2]⟩
    have hca : 1 - a ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [ha.1, ha.2]
    have htailP (side : Bool) {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
        (hdis : Disjoint (T.tail side b) (L ∪ Z)) : T.tail side b ⊆ P := by
      intro x hx
      have hxV := T.tail_subset side hb hx
      have hxL : x ∉ L := fun h => disjoint_left.mp hdis hx (Or.inl h)
      have hxZ : x ∉ Z := fun h => disjoint_left.mp hdis hx (Or.inr h)
      have hxK : x ∈ K := by
        by_contra hh
        exact hxL (hBL ⟨hxV, hh⟩)
      let y : (U ⊓ V : Opens M) := ⟨x, hKU hxK, hxV⟩
      let p := F.symm y
      have heq : j p = x := congrArg Subtype.val (F.apply_symm_apply y)
      have hle : p.2 ≤ 0 := (hclosed p).mp (show j p ∈ K from heq.symm ▸ hxK)
      have hlt : p.2 < r := by
        by_contra hh
        exact hxZ ⟨p, ⟨mem_univ _, le_of_not_gt hh, hle⟩, heq⟩
      exact ⟨p, ⟨mem_univ _, hlt⟩, heq⟩
    rcases hhalf with hh | hh
    · let z : RoundCylinderSpace := (q, 1 - a / 2)
      have hz : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 := by
        refine ⟨mem_univ _, ?_, ?_⟩ <;> dsimp [z] <;> linarith [ha.1, ha.2]
      have hzt : T.coordinate z ∈ T.tail true (1 - a) :=
        ⟨z, ⟨mem_univ _, by dsimp [z]; linarith [ha.1], hz.2.2⟩, rfl⟩
      have h := hh _ (htailP true hca hp hzt)
      rw [T.left_inverse hz] at h
      dsimp [z] at h
      linarith [ha.2]
    · let z : RoundCylinderSpace := (q, a / 2)
      have hz : z ∈ univ ×ˢ Ioo (0 : ℝ) 1 := by
        refine ⟨mem_univ _, ?_, ?_⟩ <;> dsimp [z] <;> linarith [ha.1, ha.2]
      have hzt : T.coordinate z ∈ T.tail false a :=
        ⟨z, ⟨mem_univ _, hz.2.1, by dsimp [z]; linarith [ha.1]⟩, rfl⟩
      have h := hh _ (htailP false ha1 hn hzt)
      rw [T.left_inverse hz] at h
      dsimp [z] at h
      linarith [ha.2]

end PoincareConjecture.OpenCylinderModel
