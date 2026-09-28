import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.ProtectedBallAnnulusProduct



set_option autoImplicit false
noncomputable section
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)
local notation "J" => Icc (-1 : ℝ) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (J ×ˢ J : Set P2)
local notation "Cube" => (Square ×ˢ J : Set P3)

private def centeredIntervalCoordinates : J ≃ₜ I where
  toFun t := ⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
  invFun t := ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.property.1, t.property.2]⟩
  left_inv t := by apply Subtype.ext; dsimp; ring
  right_inv t := by apply Subtype.ext; dsimp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem centeredIntervalCoordinates_finitePL : centeredIntervalCoordinates.IsFinitePL := by
  obtain ⟨K, _, hK, hKs, _, _⟩ :=
    (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).exists_finite_carrier_and_rim_complexes
  let a : ℝ →ᴬ[ℝ] ℝ := (1 / 2 : ℝ) •
    (ContinuousAffineMap.id ℝ ℝ + ContinuousAffineMap.const ℝ ℝ 1)
  refine ⟨a, ?_, ?_⟩
  · rw [← hKs]
    exact (K.affineOnFaces_affine a).finitePiecewiseAffineOn hK
  · intro x
    change ((x : ℝ) + 1) / 2 = (1 / 2 : ℝ) * ((x : ℝ) + 1)
    ring

theorem exists_cube_coordinates_of_marked_ball_product_with_height
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {B S A : Set E} (d r : Bool → Set E)
    (P : B ≃ₜ (d false ×ˢ I : Set (E × ℝ))) (hP : P.IsFinitePL)
    (hd : IsFinitePLBallPair P2 (d false) (r false))
    (hcover : (d true ∪ d false) ∪ A = S)
    (hPc : ∀ i (x : B), (x : E) ∈ d i ↔
      (P x : E × ℝ) ∈ d false ×ˢ {if i then (1 : ℝ) else 0})
    (hPa : ∀ x : B, (x : E) ∈ A ↔ (P x : E × ℝ) ∈ r false ×ˢ I) :
    ∃ Q : Cube ≃ₜ B, Q.IsFinitePL ∧
      (∀ z : Cube, (Q z : E) ∈ A ↔ |z.val.1.1| = 1 ∨ |z.val.1.2| = 1) ∧
      (∀ i (z : Cube), (Q z : E) ∈ d i ↔ z.val.2 = if i then 1 else -1) ∧
      (∀ z : Cube, (Q z : E) ∈ S ↔
        (|z.val.1.1| = 1 ∨ |z.val.1.2| = 1) ∨ |z.val.2| = 1) ∧
      ∀ z : Cube, (P (Q z) : E × ℝ).2 = (z.val.2 + 1) / 2 := by
  classical
  have hI := isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  obtain ⟨w, hw, hwmark⟩ := (hI.prod hI).exists_homeomorph hd
  let T : Cube ≃ₜ (d false ×ˢ I : Set (E × ℝ)) :=
    (Homeomorph.Set.prod Square J).trans
      ((w.prodCongr centeredIntervalCoordinates).trans (Homeomorph.Set.prod (d false) I).symm)
  let Q := T.trans P.symm
  have hQ : Q.IsFinitePL := (hw.prod centeredIntervalCoordinates_finitePL).trans hP.symm
  have hsquare (z : Square) :
      (z : P2) ∈ (({(-1 : ℝ), 1} ×ˢ J) ∪ (J ×ˢ {(-1 : ℝ), 1})) ↔
        |z.val.1| = 1 ∨ |z.val.2| = 1 := by
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff,
      z.property.1, z.property.2, and_true, true_and]
    rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1), abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
    tauto
  have hlat (z : Cube) : (Q z : E) ∈ A ↔ |z.val.1.1| = 1 ∨ |z.val.1.2| = 1 := by
    rw [hPa]
    change (P (P.symm (T z)) : E × ℝ) ∈ r false ×ˢ I ↔ _
    rw [P.apply_symm_apply]
    change (w ⟨z.val.1, z.property.1⟩ : E) ∈ r false ∧
      (centeredIntervalCoordinates ⟨z.val.2, z.property.2⟩ : ℝ) ∈ I ↔ _
    rw [and_iff_left (centeredIntervalCoordinates ⟨z.val.2, z.property.2⟩).property,
      ← hwmark, hsquare]
  have hends (i : Bool) (z : Cube) : (Q z : E) ∈ d i ↔
      z.val.2 = if i then 1 else -1 := by
    rw [hPc]
    change (P (P.symm (T z)) : E × ℝ) ∈ d false ×ˢ {if i then (1 : ℝ) else 0} ↔ _
    rw [P.apply_symm_apply]
    change (w ⟨z.val.1, z.property.1⟩ : E) ∈ d false ∧
      ((z.val.2 + 1) / 2) = (if i then (1 : ℝ) else 0) ↔ _
    rw [and_iff_right (w ⟨z.val.1, z.property.1⟩).property]
    cases i <;> simp only [Bool.false_eq_true, if_false, if_true] <;> constructor <;> intro h <;> linarith
  refine ⟨Q, hQ, hlat, hends, ?_, ?_⟩
  · intro z
    rw [← hcover, mem_union, mem_union, hends, hends, hlat]
    simp only [Bool.false_eq_true, if_false, if_true, abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
    tauto
  · intro z
    change (P (P.symm (T z)) : E × ℝ).2 = _
    rw [P.apply_symm_apply]
    rfl

theorem exists_cube_coordinates_of_marked_ball_product
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {B S A : Set E} (d r : Bool → Set E)
    (P : B ≃ₜ (d false ×ˢ I : Set (E × ℝ))) (hP : P.IsFinitePL)
    (hd : IsFinitePLBallPair P2 (d false) (r false))
    (hcover : (d true ∪ d false) ∪ A = S)
    (hPc : ∀ i (x : B), (x : E) ∈ d i ↔
      (P x : E × ℝ) ∈ d false ×ˢ {if i then (1 : ℝ) else 0})
    (hPa : ∀ x : B, (x : E) ∈ A ↔ (P x : E × ℝ) ∈ r false ×ˢ I) :
    ∃ Q : Cube ≃ₜ B, Q.IsFinitePL ∧
      (∀ z : Cube, (Q z : E) ∈ A ↔ |z.val.1.1| = 1 ∨ |z.val.1.2| = 1) ∧
      (∀ i (z : Cube), (Q z : E) ∈ d i ↔ z.val.2 = if i then 1 else -1) ∧
      (∀ z : Cube, (Q z : E) ∈ S ↔
        (|z.val.1.1| = 1 ∨ |z.val.1.2| = 1) ∨ |z.val.2| = 1) := by
  obtain ⟨Q, hQ, hlat, hends, hboundary, _⟩ :=
    exists_cube_coordinates_of_marked_ball_product_with_height d r P hP hd hcover hPc hPa
  exact ⟨Q, hQ, hlat, hends, hboundary⟩

theorem exists_protected_ball_cube_product
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {B S A : Set E} (hB : IsFinitePLBallPair V3 B S)
    (H : squareAnnulus 8 1 ≃ₜ A) (hH : H.IsFinitePL) (hAS : A ⊆ S) :
    ∃ (d r : Bool → Set E) (Q : Cube ≃ₜ B), Q.IsFinitePL ∧
      (∀ i, IsFinitePLBallPair P2 (d i) (r i) ∧ d i ⊆ S ∧
        d i ∩ A = r i) ∧
      Disjoint (d true) (d false) ∧ (d true ∪ d false) ∪ A = S ∧
      (∀ z : Cube, (Q z : E) ∈ A ↔ |z.val.1.1| = 1 ∨ |z.val.1.2| = 1) ∧
      (∀ i (z : Cube), (Q z : E) ∈ d i ↔ z.val.2 = if i then 1 else -1) ∧
      (∀ z : Cube, (Q z : E) ∈ S ↔
        (|z.val.1.1| = 1 ∨ |z.val.1.2| = 1) ∨ |z.val.2| = 1) := by
  obtain ⟨d, r, P, hd, hdis, hcover, hP, hPc, hPa⟩ :=
    exists_protected_ball_product_of_annulus hB H hH hAS
  obtain ⟨Q, hQ, hlat, hends, hboundary⟩ := exists_cube_coordinates_of_marked_ball_product
    d r P hP (hd false).1 hcover hPc hPa
  exact ⟨d, r, Q, hQ, fun i => ⟨(hd i).1, (hd i).2.1, (hd i).2.2.1⟩,
    hdis, hcover, hlat, hends, hboundary⟩

end PoincareConjecture.M76
