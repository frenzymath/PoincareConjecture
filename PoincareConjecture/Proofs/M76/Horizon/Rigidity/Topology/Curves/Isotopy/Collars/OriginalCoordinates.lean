import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Collars.FinitePL

set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace PoincareConjecture.M76.CollarIsotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def normalizedCollarCoordinates (A : Set E) {eps : ℝ} (heps : 0 < eps) :
    (A ×ˢ Icc (0 : ℝ) eps) ≃ₜ (Icc (0 : ℝ) 1 ×ˢ A) where
  toFun z := ⟨((z : E × ℝ).2 / eps, (z : E × ℝ).1),
    ⟨⟨div_nonneg z.property.2.1 heps.le, (div_le_one heps).mpr z.property.2.2⟩,
      z.property.1⟩⟩
  invFun z := ⟨((z : ℝ × E).2, eps * (z : ℝ × E).1),
    ⟨z.property.2, ⟨mul_nonneg heps.le z.property.1.1,
      (mul_le_mul_of_nonneg_left z.property.1.2 heps.le).trans_eq (mul_one eps)⟩⟩⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change eps * ((z : E × ℝ).2 / eps) = (z : E × ℝ).2
      field_simp
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · change eps * (z : ℝ × E).1 / eps = (z : ℝ × E).1
      field_simp
    · rfl
  continuous_toFun := (((continuous_snd.comp continuous_subtype_val).div_const eps).prodMk
    (continuous_fst.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := ((continuous_snd.comp continuous_subtype_val).prodMk
    (continuous_const.mul (continuous_fst.comp continuous_subtype_val))).subtype_mk _

theorem isFinitePL_normalizedCollarCoordinates
    {A : Set E} {eps : ℝ} (heps : 0 < eps)
    {track : (ℝ × E) → E}
    (htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ A)) :
    (normalizedCollarCoordinates A heps).IsFinitePL := by
  obtain ⟨J, hJ, hJs, _⟩ := htrack
  let L : (ℝ × E) →L[ℝ] (E × ℝ) :=
    (ContinuousLinearMap.snd ℝ ℝ E).prod
      (eps • ContinuousLinearMap.fst ℝ ℝ E)
  have hInv : (normalizedCollarCoordinates A heps).symm.IsFinitePL :=
    ⟨L, ⟨J, hJ, hJs, J.affineOnFaces_affine L.toContinuousAffineMap⟩,
      fun _ => rfl⟩
  exact hInv.symm

noncomputable def scaledCollarExtension {A : Set E} {eps : ℝ} (heps : 0 < eps)
    (H : I → A ≃ₜ A)
    (hc : Continuous (fun z : I × A => H z.1 z.2))
    (hci : Continuous (fun z : I × A => (H z.1).symm z.2)) (t : I) :
    (A ×ˢ Icc (0 : ℝ) eps) ≃ₜ (A ×ˢ Icc (0 : ℝ) eps) :=
  (normalizedCollarCoordinates A heps).trans
    ((collarExtensionOnCarrier H hc hci t).trans
      (normalizedCollarCoordinates A heps).symm)

theorem isFinitePL_scaledCollarExtension
    {A : Set E} {eps : ℝ} (heps : 0 < eps)
    (H : I → A ≃ₜ A)
    (hc : Continuous (fun z : I × A => H z.1 z.2))
    (hci : Continuous (fun z : I × A => (H z.1).symm z.2))
    (track : (ℝ × E) → E)
    (htrack : FinitePiecewiseAffineOn track (Icc (0 : ℝ) 1 ×ˢ A))
    (hvalue : ∀ t : I, ∀ x : A, track ((t : ℝ), x) = (H t x : E)) (t : I) :
    (scaledCollarExtension heps H hc hci t).IsFinitePL := by
  have hN := isFinitePL_normalizedCollarCoordinates heps htrack
  exact hN.trans ((isFinitePL_collarExtensionOnCarrier H hc hci track htrack hvalue t).trans
    hN.symm)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem scaledCollarExtension_apply
    {A : Set E} {eps : ℝ} (heps : 0 < eps)
    (H : I → A ≃ₜ A)
    (hc : Continuous (fun z : I × A => H z.1 z.2))
    (hci : Continuous (fun z : I × A => (H z.1).symm z.2))
    (t : I) (x : A) (r : ℝ) (hr : r ∈ Icc 0 eps) :
    (scaledCollarExtension heps H hc hci t ⟨(x, r), x.property, hr⟩ : E × ℝ) =
      ((H (cutoff t ⟨r / eps, div_nonneg hr.1 heps.le,
        (div_le_one heps).mpr hr.2⟩) x : E), r) := by
  apply Prod.ext
  · rfl
  · change eps * (r / eps) = r
    field_simp

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem scaledCollarExtension_outer
    {A : Set E} {eps : ℝ} (heps : 0 < eps)
    (H : I → A ≃ₜ A)
    (hc : Continuous (fun z : I × A => H z.1 z.2))
    (hci : Continuous (fun z : I × A => (H z.1).symm z.2)) (t : I) (x : A) :
    scaledCollarExtension heps H hc hci t ⟨(x, 0), x.property, le_rfl, heps.le⟩ =
      ⟨(H t x, 0), (H t x).property, le_rfl, heps.le⟩ := by
  apply Subtype.ext
  rw [scaledCollarExtension_apply heps H hc hci t x 0 ⟨le_rfl, heps.le⟩]
  have hz : (⟨0 / eps, div_nonneg le_rfl heps.le,
      (div_le_one heps).mpr heps.le⟩ : I) = 0 := Subtype.ext (zero_div eps)
  rw [hz, cutoff_outer]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem scaledCollarExtension_inner
    {A : Set E} {eps : ℝ} (heps : 0 < eps)
    (H : I → A ≃ₜ A)
    (hc : Continuous (fun z : I × A => H z.1 z.2))
    (hci : Continuous (fun z : I × A => (H z.1).symm z.2))
    (hzero : ∀ x, H 0 x = x) (t : I) (x : A) :
    scaledCollarExtension heps H hc hci t ⟨(x, eps), x.property, heps.le, le_rfl⟩ =
      ⟨(x, eps), x.property, heps.le, le_rfl⟩ := by
  apply Subtype.ext
  rw [scaledCollarExtension_apply heps H hc hci t x eps ⟨heps.le, le_rfl⟩]
  have hz : (⟨eps / eps, div_nonneg heps.le heps.le,
      (div_le_one heps).mpr le_rfl⟩ : I) = 1 := Subtype.ext (div_self heps.ne')
  rw [hz, cutoff_inner, hzero]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem scaledCollarExtension_zero
    {A : Set E} {eps : ℝ} (heps : 0 < eps)
    (H : I → A ≃ₜ A)
    (hc : Continuous (fun z : I × A => H z.1 z.2))
    (hci : Continuous (fun z : I × A => (H z.1).symm z.2))
    (hzero : ∀ x, H 0 x = x) :
    scaledCollarExtension heps H hc hci 0 = Homeomorph.refl _ := by
  apply Homeomorph.ext
  intro z
  apply Subtype.ext
  rw [scaledCollarExtension_apply heps H hc hci 0
    ⟨(z : E × ℝ).1, z.property.1⟩ (z : E × ℝ).2 z.property.2,
    cutoff_zero, hzero]
  rfl

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem continuous_scaledCollarExtension
    {A : Set E} {eps : ℝ} (heps : 0 < eps)
    (H : I → A ≃ₜ A)
    (hc : Continuous (fun z : I × A => H z.1 z.2))
    (hci : Continuous (fun z : I × A => (H z.1).symm z.2)) :
    Continuous (fun z : I × (A ×ˢ Icc (0 : ℝ) eps) =>
      scaledCollarExtension heps H hc hci z.1 z.2) := by
  let N := normalizedCollarCoordinates A heps
  let P := Homeomorph.Set.prod (Icc (0 : ℝ) 1) A
  exact N.symm.continuous.comp (P.symm.continuous.comp
    ((continuous_collarExtension H hc hci).comp
      (continuous_fst.prodMk (P.continuous.comp (N.continuous.comp continuous_snd)))))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem continuous_scaledCollarExtension_symm
    {A : Set E} {eps : ℝ} (heps : 0 < eps)
    (H : I → A ≃ₜ A)
    (hc : Continuous (fun z : I × A => H z.1 z.2))
    (hci : Continuous (fun z : I × A => (H z.1).symm z.2)) :
    Continuous (fun z : I × (A ×ˢ Icc (0 : ℝ) eps) =>
      (scaledCollarExtension heps H hc hci z.1).symm z.2) := by
  let N := normalizedCollarCoordinates A heps
  let P := Homeomorph.Set.prod (Icc (0 : ℝ) 1) A
  exact N.symm.continuous.comp (P.symm.continuous.comp
    ((continuous_collarExtension_symm H hc hci).comp
      (continuous_fst.prodMk (P.continuous.comp (N.continuous.comp continuous_snd)))))

end PoincareConjecture.M76.CollarIsotopy
