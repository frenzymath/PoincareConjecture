import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.ProperDiskCollarSide

set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76

local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1

theorem exists_attached_annulus_opposite_collar_half
    {X A B : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace B] [CompactSpace B] [PreconnectedSpace B]
    {K S O : Set X} (C : (A × I) ≃ₜ K)
    (hO : IsOpen O) (hOK : O ⊆ K)
    (hzero : ∀ z, (C z : X) ∈ S ↔ (z.2 : ℝ) = 0)
    (p : B × J → X) (hp : Continuous p)
    (hpO : ∀ b, p (b,⟨0,by norm_num⟩) ∈ O)
    (hproper : ∀ z, p z ∈ S ↔ (z.2 : ℝ) = 0) :
    ∃ (a δ : ℝ) (positive : Bool),
      0 < a ∧ a < 1 ∧ 0 < δ ∧ δ ≤ 1 / 2 ∧
      (∀ z : B × J, (z.2 : ℝ) ≤ a → p z ∈ O) ∧
      (∀ z : B × J, (z.2 : ℝ) ∈ Ioc 0 a → ∀ w : A × I,
        (C w : X) = p z →
        if positive then 0 < (w.2 : ℝ) else (w.2 : ℝ) < 0) ∧
      ∀ w : A × I,
        (if positive then (w.2 : ℝ) ∈ Ico (-δ) 0 else (w.2 : ℝ) ∈ Ioc 0 δ) →
        (C w : X) ∉ range p := by
  classical
  let j0 : J := ⟨0, by norm_num⟩
  have hbase : (univ : Set B) ×ˢ {j0} ⊆ p ⁻¹' O := by
    rintro ⟨b,t⟩ ⟨_,ht⟩
    have ht' : t = j0 := ht
    subst t
    exact hpO b
  obtain ⟨u,v,_,hv,hu,h0v,huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton (hO.preimage hp) hbase
  obtain ⟨r,hr,hrv⟩ := Metric.isOpen_iff.mp hv j0 (h0v (mem_singleton j0))
  let a := min (r / 2) (1 / 2 : ℝ)
  have ha : 0 < a := lt_min (half_pos hr) (by norm_num)
  have ha1 : a < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have har : a < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hmaps (z : B × J) (hz : (z.2 : ℝ) ≤ a) : p z ∈ O := by
    apply huv ⟨hu (mem_univ z.1),hrv ?_⟩
    change dist (z.2 : ℝ) (0 : ℝ) < r
    rw [Real.dist_eq,sub_zero,abs_of_nonneg z.2.property.1]
    exact hz.trans_lt har
  let T := Ioc (0 : ℝ) a
  let : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioc
  let inc : B × T → B × J := fun z => (z.1,⟨z.2, z.2.property.1.le,
    z.2.property.2.trans ha1.le⟩)
  have hinc : Continuous inc := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  let lift : B × T → K := fun z => ⟨p (inc z),hOK (hmaps _ z.2.property.2)⟩
  have hlift : Continuous lift := (hp.comp hinc).subtype_mk _
  let height : B × T → ℝ := fun z => (C.symm (lift z)).2
  have hheight : Continuous height := continuous_subtype_val.comp
    (continuous_snd.comp (C.symm.continuous.comp hlift))
  have hnonzero (z : B × T) : height z ≠ 0 := by
    intro hz
    have hm := (hzero (C.symm (lift z))).mpr hz
    rw [C.apply_symm_apply] at hm
    exact (ne_of_gt z.2.property.1) ((hproper (inc z)).mp hm)
  obtain ⟨positive,hsign⟩ : ∃ positive : Bool, ∀ z : B × T,
      if positive then 0 < height z else height z < 0 := by
    rcases isPreconnected_univ.mapsTo_Ioi_or_Iio hheight.continuousOn
      (fun z _ => hnonzero z) with hpos | hneg
    · exact ⟨true,fun z => hpos (mem_univ z)⟩
    · exact ⟨false,fun z => hneg (mem_univ z)⟩
  have hwhole (z : B × J) (hz : (z.2 : ℝ) ∈ Ioc 0 a) (w : A × I)
      (hw : (C w : X) = p z) :
      if positive then 0 < (w.2 : ℝ) else (w.2 : ℝ) < 0 := by
    let z' : B × T := (z.1,⟨z.2,hz⟩)
    have hi : inc z' = z := Prod.ext rfl (Subtype.ext rfl)
    have heq : C w = lift z' := Subtype.ext (by simpa only [lift,hi] using hw)
    have hh : C.symm (lift z') = w := by rw [←heq,C.symm_apply_apply]
    simpa only [height,hh] using hsign z'
  let core := p '' {z : B × J | a ≤ (z.2 : ℝ)}
  have hcore : IsCompact core := ((isClosed_le continuous_const
    (continuous_subtype_val.comp continuous_snd)).isCompact).image hp
  have hzeroCore (x : A) : (C (x,⟨0,by norm_num⟩) : X) ∈ coreᶜ := by
    rintro ⟨z,hz,heq⟩
    have hzS : p z ∈ S := heq ▸ (hzero (x,⟨0,by norm_num⟩)).mpr rfl
    have ht := (hproper z).mp hzS
    change a ≤ (z.2 : ℝ) at hz
    rw [ht] at hz
    exact (not_le_of_gt ha) hz
  obtain ⟨δ,hδ,hδhalf,hthin⟩ :=
    (continuous_subtype_val.comp C.continuous).exists_closed_strip_subset
      hcore.isClosed.isOpen_compl hzeroCore
  refine ⟨a,δ,positive,ha,ha1,hδ,hδhalf,hmaps,hwhole,?_⟩
  intro w hw hpw
  obtain ⟨z,heq⟩ := hpw
  have htime : |(w.2 : ℝ)| ≤ δ := by
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hw ⊢ <;>
      exact abs_le.mpr ⟨by linarith [hw.1],by linarith [hw.2]⟩
  have hnotcore := hthin w.1 w.2 htime
  have hta : (z.2 : ℝ) < a := by
    by_contra hn
    exact hnotcore ⟨z,le_of_not_gt hn,heq⟩
  have ht0 : (w.2 : ℝ) ≠ 0 := by
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hw ⊢ <;>
      linarith [hw.1,hw.2]
  have htz : 0 < (z.2 : ℝ) := by
    apply lt_of_le_of_ne z.2.property.1
    intro hz
    exact ht0 ((hzero w).mp (heq ▸ (hproper z).mpr hz.symm))
  have hs := hwhole z ⟨htz,hta.le⟩ w heq.symm
  cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hw hs <;>
    linarith [hw.1,hw.2]

end PoincareConjecture.M76
