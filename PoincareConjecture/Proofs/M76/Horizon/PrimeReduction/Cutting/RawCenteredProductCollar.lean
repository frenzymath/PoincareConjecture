import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CenteredCollarRawMarks

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem exists_signed_collar_of_centered_product
    {X : Type*} [TopologicalSpace X] [T2Space X] {S O : Set X}
    (hS : IsCompact S) (W : (S × unitInterval) ≃ₜ closure O)
    (hO : IsOpen O) (hSC : S ⊆ closure O)
    (hopen : ∀ z, (W z : X) ∈ O ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hcenter : ∀ z, (W z : X) ∈ S ↔ (z.2 : ℝ) = 1/2) :
    ∃ (HB : S ≃ₜ S) (c : X × ℝ → X),
      ContinuousOn c (S ×ˢ Icc (-1 : ℝ) 1) ∧
      Topology.IsEmbedding (fun z : (S ×ˢ Icc (-1 : ℝ) 1 : Set (X × ℝ)) => c z) ∧
      (∀ z : S, c ((z : X),0) = (HB z : X)) ∧
      c '' (S ×ˢ Ioo (-1 : ℝ) 1) = O ∧
      c '' (S ×ˢ Icc (-1 : ℝ) 1) = closure O ∧
      (∀ b : Bool, c '' (S ×ˢ ({if b then (1 : ℝ) else -1} : Set ℝ)) ⊆ frontier O) ∧
      S ⊆ O := by
  classical
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let mid : unitInterval := ⟨1/2,by norm_num,by norm_num⟩
  let m : S → S := fun x => ⟨W (x,mid),(hcenter (x,mid)).mpr rfl⟩
  have hm : Function.Bijective m := by
    constructor
    · intro x y hxy
      have hh := congrArg (fun z : S => (z : X)) hxy
      have hW : W (x,mid) = W (y,mid) := Subtype.ext hh
      exact congrArg Prod.fst (W.injective hW)
    · intro x
      let z := W.symm ⟨x,hSC x.property⟩
      have hzx : (W z : X) = x := congrArg Subtype.val (W.apply_symm_apply _)
      have hzt : z.2 = mid := Subtype.ext ((hcenter z).mp (hzx.symm ▸ x.property))
      refine ⟨z.1,Subtype.ext ?_⟩
      change (W (z.1,mid) : X) = x
      rw [←hzt]
      exact hzx
  have hmc : Continuous m :=
    ((continuous_subtype_val.comp W.continuous).comp
      (continuous_id.prodMk continuous_const)).subtype_mk _
  let HB : S ≃ₜ S := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective m hm) hmc
  let D := S ×ˢ Icc (-1 : ℝ) 1
  have ht (z : D) : ((z : X × ℝ).2+1)/2 ∈ unitInterval := by
    constructor <;> linarith [z.property.2.1,z.property.2.2]
  let p : D → S × unitInterval := fun z => ⟨⟨z.1.1,z.property.1⟩,⟨(z.1.2+1)/2,ht z⟩⟩
  have hp : Continuous p := by
    exact ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      ((((continuous_snd.comp continuous_subtype_val).add continuous_const).div_const 2).subtype_mk _)
  let c : X × ℝ → X := fun z => if hz : z ∈ D then W (p ⟨z,hz⟩) else z.1
  have hcval (z : D) : c z = (W (p z) : X) := by simp only [c,dif_pos z.property]
  have hc : ContinuousOn c D := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert (continuous_subtype_val.comp W.continuous).comp hp using 1
    exact funext hcval
  have hi : Function.Injective (fun z : D => c z) := by
    intro z w hzw
    have hpzw : p z = p w := W.injective (Subtype.ext
      ((hcval z).symm.trans (hzw.trans (hcval w))))
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun u : S × unitInterval => (u.1 : X)) hpzw
    · have hh := congrArg (fun u : S × unitInterval => (u.2 : ℝ)) hpzw
      dsimp [p] at hh
      linarith
  have hemb : Topology.IsEmbedding (fun z : D => c z) := by
    let : CompactSpace D := isCompact_iff_compactSpace.mp (hS.prod isCompact_Icc)
    exact hc.domRestrict.isClosedEmbedding hi |>.isEmbedding
  have hback (z : S × unitInterval) :
      c ((z.1 : X),2*(z.2 : ℝ)-1) = (W z : X) := by
    have hzD : ((z.1 : X),2*(z.2 : ℝ)-1) ∈ D :=
      ⟨z.1.property,by linarith [z.2.property.1],by linarith [z.2.property.2]⟩
    rw [hcval ⟨_,hzD⟩]
    congr 2
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp [p]
      ring
  have hSO : S ⊆ O := by
    intro x hx
    let z := W.symm ⟨x,hSC hx⟩
    have hzx : (W z : X) = x := congrArg Subtype.val (W.apply_symm_apply _)
    have hzmid := (hcenter z).mp (hzx.symm ▸ hx)
    exact hzx ▸ (hopen z).mpr (by rw [hzmid]; constructor <;> norm_num)
  refine ⟨HB,c,hc,hemb,?_,?_,?_,?_,hSO⟩
  · intro z
    rw [hcval ⟨((z : X),0),z.property,by norm_num,by norm_num⟩]
    change (W (p ⟨((z : X),0),_⟩) : X) = (W (z,mid) : X)
    congr 2
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      norm_num [p,mid]
  · apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      have hzD : z ∈ D := ⟨hz.1,hz.2.1.le,hz.2.2.le⟩
      rw [hcval ⟨z,hzD⟩]
      apply (hopen _).mpr
      dsimp [p]
      constructor <;> linarith [hz.2.1,hz.2.2]
    · intro x hx
      let z := W.symm ⟨x,subset_closure hx⟩
      have hzx : (W z : X) = x := congrArg Subtype.val (W.apply_symm_apply _)
      have hz := (hopen z).mp (hzx.symm ▸ hx)
      exact ⟨((z.1 : X),2*(z.2 : ℝ)-1),⟨z.1.property,by linarith [hz.1],by linarith [hz.2]⟩,
        (hback z).trans hzx⟩
  · apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact (hcval ⟨z,hz⟩).symm ▸ (W (p ⟨z,hz⟩)).property
    · intro x hx
      let z := W.symm ⟨x,hx⟩
      exact ⟨((z.1 : X),2*(z.2 : ℝ)-1),⟨z.1.property,
        by linarith [z.2.property.1],by linarith [z.2.property.2]⟩,
        (hback z).trans (congrArg Subtype.val (W.apply_symm_apply _))⟩
  · intro b
    rintro _ ⟨z,hz,rfl⟩
    have hzt : z.2 = if b then (1 : ℝ) else -1 := hz.2
    have hzD : z ∈ D := ⟨hz.1,by rw [hzt]; cases b <;> norm_num⟩
    rw [hcval ⟨z,hzD⟩,frontier,hO.interior_eq]
    refine ⟨(W (p ⟨z,hzD⟩)).property,?_⟩
    intro hx
    have hh := (hopen _).mp hx
    dsimp [p] at hh
    rw [hzt] at hh
    cases b <;> norm_num at hh

end PoincareConjecture.M76
