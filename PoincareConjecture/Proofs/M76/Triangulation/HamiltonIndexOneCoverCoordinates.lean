import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneMiddleBall
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSubcomplex

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V" => ((Fin 1 ⊕ Fin 2) → ℝ)
local notation "W" => (ℝ × (ℝ × ℝ))

private noncomputable def productLinear : (V1 × V2) ≃L[ℝ] W :=
  (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).prodCongr
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

noncomputable def productCoordinates : (V1 × V2) ≃ᴬ[ℝ] W :=
  productLinear.toContinuousAffineEquiv

noncomputable def coverCoordinates : V ≃ᴬ[ℝ] W :=
  ((ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 1) (Fin 2)
    (fun _ => ℝ)).trans productLinear).toContinuousAffineEquiv

theorem coverCoordinates_apply (x : V) :
    coverCoordinates x = (x (Sum.inl 0), (x (Sum.inr 0), x (Sum.inr 1))) := rfl

theorem boundedCoordinate_norm (x : V1) : ‖x 0‖ = ‖x‖ := by
  apply le_antisymm (norm_le_pi_norm x 0)
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x 0))).mpr
  intro i
  fin_cases i
  exact le_rfl

theorem freeCoordinates_norm (x : V2) : ‖(x 0, x 1)‖ = ‖x‖ := by
  apply le_antisymm
  · exact max_le (norm_le_pi_norm x 0) (norm_le_pi_norm x 1)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x 0, x 1))).mpr
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _

theorem coverCoordinates_norm (x : V) : ‖coverCoordinates x‖ = ‖x‖ := by
  apply le_antisymm
  · exact max_le (norm_le_pi_norm x (Sum.inl 0))
      (max_le (norm_le_pi_norm x (Sum.inr 0)) (norm_le_pi_norm x (Sum.inr 1)))
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (coverCoordinates x))).mpr
    intro i
    rcases i with i | i
    · fin_cases i
      exact le_max_left _ _
    · fin_cases i
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)

def annulusParameterSpace : Set (V1 × V2) :=
  closedBall (0 : V1) 1 ×ˢ sphere (0 : V2) 1

theorem exists_annulus_parameter_complex :
    ∃ K : SimplicialComplex ℝ (V1 × V2),
      K.faces.Finite ∧ K.space = annulusParameterSpace := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨I, hI, hIs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V1
      (closedBall (0 : V1) 1) (sphere (0 : V1) 1))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨B, hB, hBs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube : IsFinitePLBallPair V2
      (closedBall (0 : V2) 1) (sphere (0 : V2) 1))
  let S := B.frontierSubcomplex (closedBall (0 : V2) 1)
  have hS : S.faces.Finite := B.frontierSubcomplex_finite _ hB
  have hSs : S.space = sphere (0 : V2) 1 := by
    rw [B.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hBs,
      frontier_closedBall _ one_ne_zero]
  obtain ⟨K, hK, hKs, _⟩ := I.exists_finite_triangulation_prod S hI hS
  exact ⟨K, hK, by rw [hKs, hIs, hSs]; rfl⟩

private noncomputable def annulusLinear : (V1 × V2) ≃L[ℝ] W :=
  productLinear.trans ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    (LinearEquiv.smulOfNeZero ℝ (ℝ × ℝ) (3 / 2 : ℝ)
      (by norm_num)).toContinuousLinearEquiv)

noncomputable def annulusCoordinates : (V1 × V2) ≃ᴬ[ℝ] W :=
  annulusLinear.toContinuousAffineEquiv

theorem annulusCoordinates_apply (x : V1 × V2) :
    annulusCoordinates x = (x.1 0, (3 / 2 : ℝ) • (x.2 0, x.2 1)) := rfl

noncomputable def unitAnnulusCoordinates : (ℝ × V2) ≃ᴬ[ℝ] W :=
  (((ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).symm.prodCongr
    (ContinuousLinearEquiv.refl ℝ V2)).toContinuousAffineEquiv).trans annulusCoordinates

theorem unitAnnulusCoordinates_apply (x : ℝ × V2) :
    unitAnnulusCoordinates x = (x.1, (3 / 2 : ℝ) • (x.2 0, x.2 1)) := rfl

theorem annulusCoordinates_mem_rims (x : annulusParameterSpace) :
    annulusCoordinates x ∈ squareRims ↔
      (x : V1 × V2).1 ∈ sphere (0 : V1) 1 := by
  have hn : ‖(x.val.2 0, x.val.2 1)‖ = 1 :=
    (freeCoordinates_norm x.val.2).trans (mem_sphere_zero_iff_norm.mp x.property.2)
  have hf : (3 / 2 : ℝ) • (x.val.2 0, x.val.2 1) ∈
      sphere (0 : ℝ × ℝ) (3 / 2) := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), hn, mul_one]
  change (x.val.1 0 ∈ ({-1, 1} : Set ℝ) ∧
    (3 / 2 : ℝ) • (x.val.2 0, x.val.2 1) ∈ sphere (0 : ℝ × ℝ) (3 / 2)) ↔ _
  rw [and_iff_left hf, mem_sphere_zero_iff_norm, ← boundedCoordinate_norm,
    Real.norm_eq_abs]
  simp only [mem_insert_iff, mem_singleton_iff, abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
  exact or_comm

theorem exists_standard_annulus_parameter :
    ∃ u : annulusParameterSpace ≃ₜ squareInnerAnnulus,
      u.IsFinitePL ∧ ∀ x : annulusParameterSpace,
        (u x : W) = annulusCoordinates x := by
  have hmem (x : V1 × V2) :
      annulusCoordinates x ∈ squareInnerAnnulus ↔ x ∈ annulusParameterSpace := by
    change (x.1 0 ∈ Icc (-1 : ℝ) 1 ∧
      (3 / 2 : ℝ) • (x.2 0, x.2 1) ∈ sphere (0 : ℝ × ℝ) (3 / 2)) ↔ _
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), freeCoordinates_norm]
    change _ ↔ (x.1 ∈ closedBall (0 : V1) 1 ∧ x.2 ∈ sphere (0 : V2) 1)
    rw [mem_closedBall_zero_iff, mem_sphere_zero_iff_norm, ← boundedCoordinate_norm,
      Real.norm_eq_abs]
    exact and_congr abs_le.symm (by constructor <;> intro h <;> nlinarith)
  have himage : annulusCoordinates '' annulusParameterSpace = squareInnerAnnulus := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hmem x).mpr hx
    · intro y hy
      refine ⟨annulusCoordinates.symm y, ?_, annulusCoordinates.apply_symm_apply y⟩
      exact (hmem _).mp ((annulusCoordinates.apply_symm_apply y).symm ▸ hy)
  let u := (annulusCoordinates.toHomeomorph.image annulusParameterSpace).trans
    (Homeomorph.setCongr himage)
  obtain ⟨K, hK, hKs⟩ := exists_annulus_parameter_complex
  refine ⟨u, ⟨annulusCoordinates, ?_, fun _ => rfl⟩, fun _ => rfl⟩
  exact ⟨K, hK, hKs, K.affineOnFaces_affine annulusCoordinates.toContinuousAffineMap⟩

end PoincareConjecture.M76.HamiltonIndexOne
