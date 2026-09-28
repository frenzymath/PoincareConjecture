import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedProductCylinder

noncomputable section
open Set Metric BrownCollar

namespace PoincareConjecture.M76

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def cylinderInitialRimCoordinates (H : (X × Icc (0 : ℝ) 1) ≃ₜ Y) :
    X ≃ₜ range (fun x => H (x, ⟨0, by norm_num⟩)) where
  toFun x := ⟨H (x, ⟨0, by norm_num⟩), ⟨x, rfl⟩⟩
  invFun y := (H.symm y).1
  left_inv x := by simp
  right_inv y := by
    obtain ⟨x, hx⟩ := y.property
    apply Subtype.ext
    change H ((H.symm y).1, ⟨0, _⟩) = y
    rw [← hx, H.symm_apply_apply]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact H.continuous.comp (continuous_id.prodMk
      (continuous_const : Continuous (fun _ : X => (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1))))
  continuous_invFun := continuous_fst.comp (H.symm.continuous.comp continuous_subtype_val)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Unique κ]

def markedLowerRimMap
    (P : (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ≃ₜ Y)
    (x : sphere (0 : ι → ℝ) 1) : Y :=
  P ⟨((x : ι → ℝ), fun _ => -(3 / 2 : ℝ)), x.property, by
    rw [mem_closedBall_zero_iff, pi_norm_const, Real.norm_eq_abs]
    norm_num⟩

theorem markedLowerRimMap_eq
    (P : (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ≃ₜ Y)
    (x : sphere (0 : ι → ℝ) 1) :
    markedLowerRimMap P x = markedProductCylinder P (x, ⟨0, by norm_num⟩) := by
  rw [markedProductCylinder_apply]
  simp [markedLowerRimMap]

theorem exists_marked_lower_rim_image_data
    (P : (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ≃ₜ Y) :
    ∃ e : sphere (0 : ι → ℝ) 1 ≃ₜ range (markedLowerRimMap P),
      (∀ x, (e x : Y) = markedLowerRimMap P x) ∧
      ∀ b : range (markedLowerRimMap P),
        Function.Surjective (FundamentalGroup.map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(range (markedLowerRimMap P), Y)) b) ∧
        ∃ c : OpenPartialHomeomorph
            (range (markedLowerRimMap P) × Ico (0 : ℝ) 1) Y,
          c.source = univ ∧ ∀ a, c (collarBase a) = (a : Y) := by
  let H := markedProductCylinder P
  have heq : range (fun x => H (x, ⟨0, by norm_num⟩)) =
      range (markedLowerRimMap P) := by
    congr 1
    funext x
    exact (markedLowerRimMap_eq P x).symm
  let e := (cylinderInitialRimCoordinates H).trans (Homeomorph.setCongr heq)
  have he (x) : (e x : Y) = markedLowerRimMap P x :=
    (markedLowerRimMap_eq P x).symm
  refine ⟨e, he, ?_⟩
  intro b
  apply marked_product_lower_rim_data P e ⟨Subtype.val, continuous_subtype_val⟩ _ b
  intro x
  exact (he x).symm

end PoincareConjecture.M76
