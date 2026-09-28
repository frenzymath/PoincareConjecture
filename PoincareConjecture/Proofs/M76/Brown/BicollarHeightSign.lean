import PoincareConjecture.Proofs.M76.Brown.TwoOpenSignCover
import PoincareConjecture.Proofs.M76.Brown.SignedCylinderCoordinates









set_option autoImplicit false

open Set SignType

namespace BrownCollar

variable {X : Type*} [TopologicalSpace X] {S C : Set X}

def bicollarHeight (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C) (y : C) : ℝ :=
  (H.symm y).2

theorem continuous_bicollarHeight (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C) :
    Continuous (bicollarHeight H) :=
  continuous_subtype_val.comp (continuous_snd.comp H.symm.continuous)



theorem bicollarHeight_eq_zero_iff (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X)) (y : C) :
    bicollarHeight H y = 0 ↔ (y : X) ∈ S := by
  constructor
  · intro hy
    have hz : H.symm y = bicollarBase (H.symm y).1 :=
      Prod.ext rfl (Subtype.ext hy)
    have heq : (y : X) = ((H.symm y).1 : X) := by
      calc
        (y : X) = (H (H.symm y) : X) := congrArg Subtype.val (H.apply_symm_apply y).symm
        _ = (H (bicollarBase (H.symm y).1) : X) := congrArg (fun z => (H z : X)) hz
        _ = ((H.symm y).1 : X) := hbase _
    rw [heq]
    exact (H.symm y).1.property
  · intro hy
    let s : S := ⟨y.val, hy⟩
    have heq : H (bicollarBase s) = y := Subtype.ext (hbase s)
    rw [← heq, bicollarHeight, H.symm_apply_apply]
    rfl

theorem bicollar_point_mem_overlap (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X))
    (z : S × Ioo (-1 : ℝ) 1) (hz : (z.2 : ℝ) ≠ 0) : (H z : X) ∈ Sᶜ ∩ C := by
  refine ⟨?_, (H z).property⟩
  intro hS
  have hzero := (bicollarHeight_eq_zero_iff H hbase (H z)).mpr hS
  rw [bicollarHeight, H.symm_apply_apply] at hzero
  exact hz hzero



noncomputable def bicollarOverlapUnit (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X)) (x : X) : SignTypeˣ := by
  classical
  exact if hx : x ∈ Sᶜ ∩ C then
    Units.mk0 (sign (bicollarHeight H ⟨x, hx.2⟩)) (by
      intro h
      exact hx.1 ((bicollarHeight_eq_zero_iff H hbase ⟨x, hx.2⟩).mp
        (sign_eq_zero_iff.mp h)))
  else 1

theorem bicollarOverlapUnit_spec (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X))
    (x : X) (hx : x ∈ Sᶜ ∩ C) :
    (bicollarOverlapUnit H hbase x : SignType) = sign (bicollarHeight H ⟨x, hx.2⟩) := by
  rw [bicollarOverlapUnit, dif_pos hx]
  rfl

theorem bicollarOverlapUnit_apply (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X))
    (z : S × Ioo (-1 : ℝ) 1) (hz : (z.2 : ℝ) ≠ 0) :
    (bicollarOverlapUnit H hbase (H z) : SignType) = sign (z.2 : ℝ) := by
  rw [bicollarOverlapUnit_spec H hbase (H z) (bicollar_point_mem_overlap H hbase z hz)]
  change sign (bicollarHeight H (H z)) = sign (z.2 : ℝ)
  rw [bicollarHeight, H.symm_apply_apply]

theorem continuousOn_bicollarOverlapUnit (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X)) :
    ContinuousOn (bicollarOverlapUnit H hbase) (Sᶜ ∩ C) := by
  let f : ↥(Sᶜ ∩ C) → C := fun x => ⟨x.val, x.property.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hheight : Continuous (fun x : ↥(Sᶜ ∩ C) => bicollarHeight H (f x)) :=
    (continuous_bicollarHeight H).comp hf
  have hne (x : ↥(Sᶜ ∩ C)) : bicollarHeight H (f x) ≠ 0 := by
    intro h
    exact x.property.1 ((bicollarHeight_eq_zero_iff H hbase (f x)).mp h)
  have hsign : Continuous (fun x : ↥(Sᶜ ∩ C) => sign (bicollarHeight H (f x))) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (continuousAt_sign_of_ne_zero (hne x)).comp
        (f := fun y : ↥(Sᶜ ∩ C) => bicollarHeight H (f y)) hheight.continuousAt)
  have hv : Continuous (fun x : ↥(Sᶜ ∩ C) =>
      (bicollarOverlapUnit H hbase x.val : SignType)) := by
    convert hsign using 1
    funext x
    exact bicollarOverlapUnit_spec H hbase x.val x.property
  rw [continuousOn_iff_continuous_domRestrict]
  refine Units.continuous_iff.mpr ⟨hv, ?_⟩
  have hinv (s : SignType) : s⁻¹ = s := rfl
  simpa only [Units.val_inv_eq_inv_val, hinv, Set.domRestrict_apply] using hv




theorem exists_bicollar_sign_section [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    [Nonempty X] (hS : IsClosed S) (hC : IsOpen C)
    (H : (S × Ioo (-1 : ℝ) 1) ≃ₜ C)
    (hbase : ∀ s, (H (bicollarBase s) : X) = (s : X)) :
    ∃ a0 a1 : X → SignTypeˣ, ContinuousOn a0 Sᶜ ∧ ContinuousOn a1 C ∧
      ∀ z : S × Ioo (-1 : ℝ) 1, (z.2 : ℝ) ≠ 0 →
        (a1 (H z) : SignType) = sign (z.2 : ℝ) * (a0 (H z) : SignType) := by
  have hSC : S ⊆ C := by
    intro x hx
    have hmem := (H (bicollarBase ⟨x, hx⟩)).property
    simpa only [hbase] using hmem
  have hcover : Sᶜ ∪ C = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ S
    · exact Or.inr (hSC hx)
    · exact Or.inl hx
  obtain ⟨a0, a1, ha0, ha1, hcompat⟩ := exists_two_open_sign_section
    Sᶜ C hS.isOpen_compl hC hcover (bicollarOverlapUnit H hbase)
      (continuousOn_bicollarOverlapUnit H hbase)
  refine ⟨a0, a1, ha0, ha1, ?_⟩
  intro z hz
  have heq := congrArg Units.val (hcompat (H z) (bicollar_point_mem_overlap H hbase z hz))
  change (a1 (H z) : SignType) =
    (bicollarOverlapUnit H hbase (H z) : SignType) * (a0 (H z) : SignType) at heq
  rwa [bicollarOverlapUnit_apply H hbase z hz] at heq

end BrownCollar
