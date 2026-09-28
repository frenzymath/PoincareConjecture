import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneRetraction
import Mathlib.Analysis.Normed.Module.Connected










set_option autoImplicit false
open Set Metric unitInterval
namespace PoincareConjecture.M76

theorem exists_annulus_complement_deformation
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A B F : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (H : (Y × Icc (-1 : ℝ) 1) ≃ₜ B)
    (hcover : A ∪ B = F)
    (hrim : ∀ z, (H z : X) ∈ A ↔ (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1) :
    let C := (fun z => (H z : X)) '' {z | (z.2 : ℝ) = 0}
    ∃ K : C(I × ↥(F \ C),F),
      (∀ x : ↥(F \ C), (K (0,x) : X) = x) ∧
      (∀ x : ↥(F \ C), (K (1,x) : X) ∈ A) ∧
      ∀ t (x : ↥(F \ C)), (x : X) ∈ A → (K (t,x) : X) = x := by
  classical
  let C := (fun z => (H z : X)) '' {z | (z.2 : ℝ) = 0}
  let Z := F \ C
  let s : Set (I × Z) := {z | z.2.val ∈ A}
  let t : Set (I × Z) := {z | z.2.val ∈ B}
  have hs : IsClosed s := hA.preimage (continuous_subtype_val.comp continuous_snd)
  have ht : IsClosed t := hB.preimage (continuous_subtype_val.comp continuous_snd)
  have hst : s ∪ t = univ := by
    apply eq_univ_of_forall
    intro z
    exact hcover.symm.subset z.2.property.1
  let v : t → Y × Icc (-1 : ℝ) 1 := fun z => H.symm ⟨z.val.2,z.property⟩
  have hv : Continuous v := H.symm.continuous.comp
    ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
  have hvval (z : t) : (H (v z) : X) = z.val.2 :=
    congrArg Subtype.val (H.apply_symm_apply _)
  let u : t → ℝ := fun z => (v z).2
  have hu : Continuous u := continuous_subtype_val.comp hv.snd
  have hune (z : t) : u z ≠ 0 := by
    intro hz
    exact z.val.2.property.2 ⟨v z,hz,hvval z⟩
  let signHeight : t → ℝ := fun z => u z / |u z|
  have hσ : Continuous signHeight := hu.div hu.abs (fun z => abs_ne_zero.mpr (hune z))
  have hσabs (z : t) : |signHeight z| = 1 := by
    simp only [signHeight,abs_div,abs_abs]
    exact div_self (abs_ne_zero.mpr (hune z))
  have hσbounds (z : t) : signHeight z ∈ Icc (-1 : ℝ) 1 :=
    abs_le.mp (hσabs z).le
  let w : t → ℝ := fun z => (1 - (z.val.1 : ℝ)) * u z + (z.val.1 : ℝ) * signHeight z
  have hw : Continuous w := by
    dsimp only [w]
    exact (continuous_const.sub (continuous_subtype_val.comp
      (continuous_fst.comp continuous_subtype_val))).mul hu |>.add
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).mul hσ)
  have hwbounds (z : t) : w z ∈ Icc (-1 : ℝ) 1 := by
    have hz0 := z.val.1.property.1
    have hz1 := z.val.1.property.2
    have hu0 := (v z).2.property.1
    have hu1 := (v z).2.property.2
    have hs0 := (hσbounds z).1
    have hs1 := (hσbounds z).2
    change -1 ≤ (1 - (z.val.1 : ℝ)) * u z + (z.val.1 : ℝ) * signHeight z ∧
      (1 - (z.val.1 : ℝ)) * u z + (z.val.1 : ℝ) * signHeight z ≤ 1
    change -1 ≤ u z at hu0
    change u z ≤ 1 at hu1
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hz1) (sub_nonneg.mpr hu0),
      mul_nonneg hz0 (sub_nonneg.mpr hs0),
      mul_nonneg (sub_nonneg.mpr hz1) (sub_nonneg.mpr hu1),
      mul_nonneg hz0 (sub_nonneg.mpr hs1)]
  let moved : t → Y × Icc (-1 : ℝ) 1 := fun z => ((v z).1,⟨w z,hwbounds z⟩)
  have hm : Continuous moved := hv.fst.prodMk (hw.subtype_mk _)
  let f : C(s,F) := ⟨fun z => ⟨z.val.2,z.val.2.property.1⟩,by fun_prop⟩
  let g : C(t,F) := ⟨fun z => ⟨H (moved z),hcover.subset (Or.inr (H (moved z)).property)⟩,
    (continuous_subtype_val.comp (H.continuous.comp hm)).subtype_mk _⟩
  have hfixed (z : t) (hz : z.val.2.val ∈ A) : moved z = v z := by
    have h := (hrim (v z)).mp ((hvval z).symm ▸ hz)
    have hsign : signHeight z = u z := by
      rcases h with h | h
      · change u z = -1 at h
        simp [signHeight,h]
      · change u z = 1 at h
        simp [signHeight,h]
    apply Prod.ext
    · rfl
    apply Subtype.ext
    change w z = u z
    dsimp only [w]
    rw [hsign]
    ring
  have hagree (z : I × Z) (hzs : z ∈ s) (hzt : z ∈ t) :
      f ⟨z,hzs⟩ = g ⟨z,hzt⟩ := by
    apply Subtype.ext
    change z.2.val = (H (moved ⟨z,hzt⟩) : X)
    rw [hfixed ⟨z,hzt⟩ hzs]
    exact (hvval ⟨z,hzt⟩).symm
  obtain ⟨K,hKs,hKt⟩ := HamiltonIndexOne.glue_closed_cover s t hs ht hst f g hagree
  refine ⟨K,?_,?_,?_⟩
  · intro x
    by_cases hx : x.val ∈ A
    · exact congrArg Subtype.val (hKs ⟨(0,x),hx⟩)
    · have hxB : x.val ∈ B := (hcover.symm.subset x.property.1).resolve_left hx
      rw [hKt ⟨(0,x),hxB⟩]
      change (H (moved ⟨(0,x),hxB⟩) : X) = x.val
      have hh : moved ⟨(0,x),hxB⟩ = v ⟨(0,x),hxB⟩ := by
        apply Prod.ext
        · rfl
        apply Subtype.ext
        simp [moved,w,u]
      rw [hh]
      exact hvval _
  · intro x
    by_cases hx : x.val ∈ A
    · rw [hKs ⟨(1,x),hx⟩]
      exact hx
    · have hxB : x.val ∈ B := (hcover.symm.subset x.property.1).resolve_left hx
      rw [hKt ⟨(1,x),hxB⟩]
      apply (hrim (moved ⟨(1,x),hxB⟩)).mpr
      have habs := hσabs ⟨(1,x),hxB⟩
      have hh : (moved ⟨(1,x),hxB⟩).2.val = signHeight ⟨(1,x),hxB⟩ := by simp [moved,w]
      rw [hh]
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
      · exact Or.inr h
      · exact Or.inl h
  · intro t' x hx
    exact congrArg Subtype.val (hKs ⟨(t',x),hx⟩)

theorem exists_disk_extension_of_fixed_projection_homotopy
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (inc : C(Y,X)) (r : C(X,Y))
    (disk : C(closedBall (0 : Fin 2 → ℝ) 1,X))
    (f g : C(sphere (0 : Fin 2 → ℝ) 1,Y)) (h : f.Homotopic g)
    (hrim : ∀ z : sphere (0 : Fin 2 → ℝ) 1,
      disk ⟨z,sphere_subset_closedBall z.property⟩ = inc (f z))
    (hfix : ∀ z, r (inc (g z)) = g z) :
    ∃ F : C(closedBall (0 : Fin 2 → ℝ) 1,Y),
      ∀ z : sphere (0 : Fin 2 → ℝ) 1,
        F ⟨z,sphere_subset_closedBall z.property⟩ = f z := by
  let rim : C(sphere (0 : Fin 2 → ℝ) 1,closedBall (0 : Fin 2 → ℝ) 1) :=
    ⟨fun z => ⟨z,sphere_subset_closedBall z.property⟩,by fun_prop⟩
  let G := r.comp disk
  have heq : (r.comp inc).comp g = g := ContinuousMap.ext hfix
  have hh : f.Homotopic ((r.comp inc).comp f) := by
    have hp := (ContinuousMap.Homotopic.refl (r.comp inc)).comp h
    rw [heq] at hp
    exact h.trans hp.symm
  have heq' : G.comp rim = (r.comp inc).comp f := by
    ext z
    exact congrArg r (hrim z)
  have hG : G.Nullhomotopic := by
    let : ContractibleSpace (closedBall (0 : Fin 2 → ℝ) 1) :=
      (convex_closedBall (0 : Fin 2 → ℝ) 1).contractibleSpace
        ⟨0,mem_closedBall_self (by norm_num)⟩
    simpa only [ContinuousMap.comp_id] using (id_nullhomotopic _).comp_right G
  obtain ⟨y,hy⟩ := hG.comp_left rim
  rw [heq'] at hy
  exact (show f.Nullhomotopic from ⟨y,hh.trans hy⟩).exists_closedBall_extension f

end PoincareConjecture.M76
