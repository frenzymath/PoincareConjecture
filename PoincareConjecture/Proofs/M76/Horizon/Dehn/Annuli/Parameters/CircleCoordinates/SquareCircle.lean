import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusSquares
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.WholeCircleAdjustments
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic









set_option autoImplicit false
open Set Geometry Metric PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Square" => _root_.Dehn.annulusSquare 8 0

private theorem zero_annulus_subset_square : squareAnnulus 8 0 ⊆ Square := by
  intro x hx
  exact (_root_.Dehn.mem_annulusSquare_iff 8 0 x).mpr
    (by simpa using (mem_squareAnnulus_iff_depth.mp hx).1)

private theorem zero_annulus_eq_frontier :
    squareAnnulus 8 0 = frontier Square := by
  ext x
  rw [mem_squareAnnulus_iff_depth, _root_.Dehn.mem_frontier_annulusSquare_iff]
  simp only [neg_zero, mem_Icc]
  exact ⟨fun h ↦ le_antisymm h.2 h.1, fun h ↦ ⟨h.ge, h.le⟩⟩



theorem exists_square_circle_coordinates :
    ∃ (j : Circle ≃ₜ Q2) (f : P2 → V2),
      FinitePiecewiseAffineOn f Square ∧
      (∀ z, (j z : V2) = f (annulusMap 8 (by norm_num) (z, 0))) ∧
      FinitePiecewiseAffineOn
        (fun s : ℝ ↦ (j ((32 * s : ℝ) : Circle) : V2)) (Icc 0 1) := by
  classical
  obtain ⟨e, he, heb⟩ := (_root_.Dehn.isFinitePLBallPair_annulusSquare
    (L := 8) (u := 0) (by norm_num)).exists_cube_chart
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  obtain ⟨f, hf, hev⟩ := he
  have heb' (x : Square) : (x : P2) ∈ squareAnnulus 8 0 ↔ (e x : V2) ∈ Q2 := by
    rw [zero_annulus_eq_frontier]
    simpa only [frontier_closedBall _ one_ne_zero] using heb x
  let b : squareAnnulus 8 0 ≃ₜ Q2 :=
    { toFun := fun x ↦ ⟨e ⟨x, zero_annulus_subset_square x.property⟩,
        (heb' _).mp x.property⟩
      invFun := fun y ↦ ⟨e.symm ⟨y, sphere_subset_closedBall y.property⟩,
        (heb' _).mpr (by simpa only [e.apply_symm_apply] using y.property)⟩
      left_inv := by
        intro x
        apply Subtype.ext
        change (e.symm (e ⟨x, zero_annulus_subset_square x.property⟩) : P2) = x
        exact congrArg Subtype.val (e.symm_apply_apply _)
      right_inv := by
        intro y
        apply Subtype.ext
        change (e (e.symm ⟨y, sphere_subset_closedBall y.property⟩) : V2) = y
        exact congrArg Subtype.val (e.apply_symm_apply _)
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  obtain ⟨a, ha⟩ := exists_annulus_homeomorph (L := 8) (d := 0)
    (by norm_num) (by norm_num) (by norm_num)
  let a₀ : Circle ≃ₜ squareAnnulus 8 0 :=
    { toFun := fun z ↦ a (z, ⟨0, by norm_num⟩)
      invFun := fun x ↦ (a.symm x).1
      left_inv := by intro z; exact congrArg Prod.fst (a.symm_apply_apply _)
      right_inv := by
        intro x
        have hz : (a.symm x).2 = ⟨0, by norm_num⟩ := by
          apply Subtype.ext
          exact le_antisymm (a.symm x).2.property.2
            (by simpa only [neg_zero] using (a.symm x).2.property.1)
        change a ((a.symm x).1, ⟨0, by norm_num⟩) = x
        rw [← hz]
        exact a.apply_symm_apply x
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let j := a₀.trans b
  have hj (z : Circle) : (j z : V2) = f (annulusMap 8 (by norm_num) (z, 0)) := by
    exact (hev _).trans (congrArg f (ha (z, ⟨0, by norm_num⟩)))
  refine ⟨j, f, hf, hj, ?_⟩
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  let scale : ℝ →ᴬ[ℝ] P2 :=
    ((32 : ℝ) • ContinuousAffineMap.id ℝ ℝ).prod (ContinuousAffineMap.const ℝ ℝ 0)
  have hscale : FinitePiecewiseAffineOn scale (Icc (0 : ℝ) 1) :=
    ⟨K, hK, hKI, K.affineOnFaces_affine scale⟩
  have hraw := (finitePiecewiseAffineOn_wrappedStripMap
    (L := 8) (d := 1) (by norm_num) (by norm_num)).comp hscale (by
      intro s hs
      change (32 * s, (0 : ℝ)) ∈ rectangle (4 * 8) 1
      exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, by norm_num⟩)
  have hrawval (s : ℝ) (hs : s ∈ Icc 0 1) :
      wrappedStripMap 8 (scale s) = annulusMap 8 (by norm_num)
        (((32 * s : ℝ) : Circle), 0) := by
    exact (annulusMap_coe (L := 8) (t := 0) (s := 32 * s) (by norm_num) (by norm_num)
      ⟨by linarith [hs.1], by linarith [hs.2]⟩).symm
  have hmap : MapsTo (wrappedStripMap 8 ∘ scale) (Icc 0 1) Square := by
    intro s hs
    rw [Function.comp_apply, hrawval s hs]
    apply zero_annulus_subset_square
    rw [← ha (((32 * s : ℝ) : Circle), ⟨0, by norm_num⟩)]
    exact (a (((32 * s : ℝ) : Circle), ⟨0, by norm_num⟩)).property
  exact (hf.comp hraw hmap).congr (fun s hs ↦ by
    dsimp only [Function.comp_apply]
    rw [hrawval s hs, hj])

end PoincareConjecture.M76.Dehn
