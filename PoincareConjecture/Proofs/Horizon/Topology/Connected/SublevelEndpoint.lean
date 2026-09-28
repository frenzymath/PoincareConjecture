import PoincareConjecture.Proofs.Horizon.Topology.Connected.Sublevel
import Mathlib.Topology.Connected.Clopen

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X]

def HasConnectedLowerSide (f : X → ℝ) (O : Set X) (a : ℝ) (x : X) : Prop :=
  ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
    IsPreconnected (V ∩ f ⁻¹' Iio a) ∧
    V ∩ f ⁻¹' Iic a ⊆ closure (V ∩ f ⁻¹' Iio a)

variable [LocallyConnectedSpace X]

theorem connectedComponentIn_strict_sublevel_eq_iUnion
    {f : X → ℝ} {O : Set X} (hO : IsOpen O) (hf : ContinuousOn f O)
    {p : X} {a : ℝ} (hp : p ∈ O) (hpa : f p < a) :
    connectedComponentIn (O ∩ f ⁻¹' Iio a) p =
      ⋃ b < a, connectedComponentIn (O ∩ f ⁻¹' Iic b) p := by
  let U := ⋃ b < a, connectedComponentIn (O ∩ f ⁻¹' Iic b) p
  have hUsub : U ⊆ O ∩ f ⁻¹' Iio a := by
    rintro x hx
    rcases mem_iUnion₂.mp hx with ⟨b, hb, hxb⟩
    have hxbase := connectedComponentIn_subset _ _ hxb
    exact ⟨hxbase.1, hxbase.2.trans_lt hb⟩
  have hUopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rcases mem_iUnion₂.mp hx with ⟨b, hb, hxb⟩
    obtain ⟨d, hbd, hda⟩ := exists_between hb
    have hxbase := connectedComponentIn_subset _ _ hxb
    have hxd : x ∈ connectedComponentIn (O ∩ f ⁻¹' Iic d) p :=
      connectedComponentIn_mono p (inter_subset_inter_right O (preimage_mono (Iic_subset_Iic.mpr hbd.le))) hxb
    have hnbhd : O ∩ f ⁻¹' Iic d ∈ 𝓝 x := mem_of_superset
      ((hf.isOpen_inter_preimage hO isOpen_Iio).mem_nhds
        ⟨hxbase.1, hxbase.2.trans_lt hbd⟩) (inter_subset_inter_right O (preimage_mono Iio_subset_Iic_self))
    have hcomponent := connectedComponentIn_mem_nhds hnbhd
    rw [← connectedComponentIn_eq hxd] at hcomponent
    exact mem_of_superset hcomponent (fun y hy => mem_iUnion₂.mpr ⟨d, hda, hy⟩)
  have hclosure : closure U ∩ (O ∩ f ⁻¹' Iio a) ⊆ U := by
    intro x hx
    obtain ⟨d, hxd, hda⟩ := exists_between (show f x < a from hx.2.2)
    let V := connectedComponentIn (O ∩ f ⁻¹' Iio d) x
    have hV : IsOpen V := (hf.isOpen_inter_preimage hO isOpen_Iio).connectedComponentIn
    have hxV : x ∈ V := mem_connectedComponentIn ⟨hx.2.1, hxd⟩
    obtain ⟨z, hzV, hzU⟩ := mem_closure_iff.mp hx.1 V hV hxV
    rcases mem_iUnion₂.mp hzU with ⟨b, hb, hzb⟩
    let c := max b d
    have hca : c < a := max_lt hb hda
    have hzc : z ∈ connectedComponentIn (O ∩ f ⁻¹' Iic c) p :=
      connectedComponentIn_mono p
        (inter_subset_inter_right O (preimage_mono (Iic_subset_Iic.mpr (le_max_left b d)))) hzb
    have hVc : V ⊆ connectedComponentIn (O ∩ f ⁻¹' Iic c) z :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn hzV (fun y hy =>
        ⟨(connectedComponentIn_subset _ _ hy).1,
          (connectedComponentIn_subset _ _ hy).2.le.trans (le_max_right b d)⟩)
    have hxc := hVc hxV
    rw [← connectedComponentIn_eq hzc] at hxc
    exact mem_iUnion₂.mpr ⟨c, hca, hxc⟩
  apply subset_antisymm
  · apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hUopen
    · exact ⟨p, mem_connectedComponentIn ⟨hp, hpa⟩,
        mem_iUnion₂.mpr ⟨f p, hpa, mem_connectedComponentIn ⟨hp, le_refl (f p)⟩⟩⟩
    · exact fun x hx => hclosure ⟨hx.1, connectedComponentIn_subset _ _ hx.2⟩
  · rintro x hx
    rcases mem_iUnion₂.mp hx with ⟨b, hb, hxb⟩
    exact connectedComponentIn_mono p
      (show O ∩ f ⁻¹' Iic b ⊆ O ∩ f ⁻¹' Iio a from
        fun y hy => ⟨hy.1, hy.2.trans_lt hb⟩) hxb

theorem connectedComponentIn_sublevel_eq_closure_strict_sublevel
    {f : X → ℝ} {O : Set X} (hO : IsOpen O) (hf : ContinuousOn f O)
    {p : X} {a : ℝ} (hp : p ∈ O) (hpa : f p < a)
    (hclosure : closure (connectedComponentIn (O ∩ f ⁻¹' Iio a) p) ⊆ O)
    (hlocal : ∀ x ∈ O, f x = a →
      (∀ᶠ y in 𝓝 x, y ≠ x → f x < f y) ∨ HasConnectedLowerSide f O a x) :
    connectedComponentIn (O ∩ f ⁻¹' Iic a) p =
      closure (connectedComponentIn (O ∩ f ⁻¹' Iio a) p) := by
  let C := connectedComponentIn (O ∩ f ⁻¹' Iio a) p
  let S := O ∩ f ⁻¹' Iic a
  have hpC : p ∈ C := mem_connectedComponentIn ⟨hp, hpa⟩
  have hCS : closure C ⊆ S := by
    intro x hx
    refine ⟨hclosure hx, ?_⟩
    by_contra hxa
    have hax : a < f x := lt_of_not_ge hxa
    obtain ⟨y, hy, hyC⟩ := mem_closure_iff.mp hx (O ∩ f ⁻¹' Ioi a)
      (hf.isOpen_inter_preimage hO isOpen_Ioi) ⟨hclosure hx, hax⟩
    have hya : f y < a := (connectedComponentIn_subset _ _ hyC).2
    exact (not_lt_of_ge hya.le) (show a < f y from hy.2)
  have hside (x : X) (hx : x ∈ closure C) (V : Set X) (hV : IsOpen V)
      (hxV : x ∈ V) (hVO : V ⊆ O) (hconn : IsPreconnected (V ∩ f ⁻¹' Iio a)) :
      V ∩ f ⁻¹' Iio a ⊆ C := by
    obtain ⟨z, hzV, hzC⟩ := mem_closure_iff.mp hx V hV hxV
    have hzlower : z ∈ V ∩ f ⁻¹' Iio a :=
      ⟨hzV, (connectedComponentIn_subset _ _ hzC).2⟩
    have hsub := hconn.subset_connectedComponentIn hzlower
      (show V ∩ f ⁻¹' Iio a ⊆ O ∩ f ⁻¹' Iio a from fun y hy => ⟨hVO hy.1, hy.2⟩)
    rwa [← connectedComponentIn_eq hzC] at hsub
  have hrelative : IsOpen ((Subtype.val : S → X) ⁻¹' closure C) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hxC : (x : X) ∈ closure C := hx
    suffices ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧ V ∩ S ⊆ closure C by
      obtain ⟨V, hV, hxV, hVK⟩ := this
      exact mem_of_superset ((hV.preimage continuous_subtype_val).mem_nhds hxV)
        (fun y hy => hVK ⟨hy, y.2⟩)
    by_cases hxa : f x < a
    · let V := connectedComponentIn (O ∩ f ⁻¹' Iio a) x
      have hV : IsOpen V := (hf.isOpen_inter_preimage hO isOpen_Iio).connectedComponentIn
      have hxV : (x : X) ∈ V := mem_connectedComponentIn ⟨x.2.1, hxa⟩
      have hVO : V ⊆ O := fun y hy => (connectedComponentIn_subset _ _ hy).1
      have hVlower : V ∩ f ⁻¹' Iio a = V := inter_eq_left.mpr
        (fun y hy => (connectedComponentIn_subset _ _ hy).2)
      have hVC := hside x hxC V hV hxV hVO
        (by rw [hVlower]; exact isPreconnected_connectedComponentIn)
      refine ⟨V, hV, hxV, fun y hy => subset_closure ?_⟩
      exact hVC ⟨hy.1, (connectedComponentIn_subset _ _ hy.1).2⟩
    · have hxa : f x = a := le_antisymm x.2.2 (le_of_not_gt hxa)
      rcases hlocal x x.2.1 hxa with hmin | ⟨V, hV, hxV, hVO, hconn, hdense⟩
      · obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hmin
        obtain ⟨y, hyV, hyC⟩ := mem_closure_iff.mp hxC V hV hxV
        have hya : f y < a := (connectedComponentIn_subset _ _ hyC).2
        have hyx : y ≠ (x : X) := by intro heq; simp [heq, hxa] at hya
        have hxy := hVsub hyV hyx
        exact (not_lt_of_ge (hxa ▸ hxy.le)) hya |>.elim
      · exact ⟨V, hV, hxV, fun y hy =>
          closure_mono (hside x hxC V hV hxV hVO hconn) (hdense ⟨hy.1, hy.2.2⟩)⟩
  have hclopen : IsClopen ((Subtype.val : S → X) ⁻¹' closure C) :=
    ⟨isClosed_closure.preimage continuous_subtype_val, hrelative⟩
  apply subset_antisymm
  · intro x hx
    rw [connectedComponentIn_eq_image (show p ∈ S from ⟨hp, hpa.le⟩)] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hclopen.connectedComponent_subset (subset_closure hpC) hy
  · exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure hpC) hCS

theorem connectedComponentIn_sublevel_eq_closure_iUnion
    {f : X → ℝ} {O : Set X} (hO : IsOpen O) (hf : ContinuousOn f O)
    {p : X} {a : ℝ} (hp : p ∈ O) (hpa : f p < a)
    (hclosure : closure (⋃ b < a, connectedComponentIn (O ∩ f ⁻¹' Iic b) p) ⊆ O)
    (hlocal : ∀ x ∈ O, f x = a →
      (∀ᶠ y in 𝓝 x, y ≠ x → f x < f y) ∨ HasConnectedLowerSide f O a x) :
    connectedComponentIn (O ∩ f ⁻¹' Iic a) p =
      closure (⋃ b < a, connectedComponentIn (O ∩ f ⁻¹' Iic b) p) := by
  rw [← connectedComponentIn_strict_sublevel_eq_iUnion hO hf hp hpa] at hclosure ⊢
  exact connectedComponentIn_sublevel_eq_closure_strict_sublevel hO hf hp hpa hclosure hlocal

theorem isCompact_connectedComponentIn_sublevel_of_relativelyCompact_lower_components
    {f : X → ℝ} {O : Set X} (hO : IsOpen O) (hf : ContinuousOn f O)
    {p : X} {a : ℝ} (hp : p ∈ O) (hpa : f p < a)
    {V : Set X} (hV : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (hprior : ∀ b < a, connectedComponentIn (O ∩ f ⁻¹' Iic b) p ⊆ V)
    (hlocal : ∀ x ∈ O, f x = a →
      (∀ᶠ y in 𝓝 x, y ≠ x → f x < f y) ∨ HasConnectedLowerSide f O a x) :
    IsCompact (connectedComponentIn (O ∩ f ⁻¹' Iic a) p) := by
  have hsub : (⋃ b < a, connectedComponentIn (O ∩ f ⁻¹' Iic b) p) ⊆ V :=
    iUnion₂_subset hprior
  rw [connectedComponentIn_sublevel_eq_closure_iUnion hO hf hp hpa
    ((closure_mono hsub).trans hVO) hlocal]
  exact hV.of_isClosed_subset isClosed_closure (closure_mono hsub)

end Poincare.Topology
