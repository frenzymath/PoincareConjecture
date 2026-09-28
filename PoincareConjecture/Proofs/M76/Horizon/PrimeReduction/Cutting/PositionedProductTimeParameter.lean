import PoincareConjecture.Proofs.M76.Mathlib.PLFiberCompression
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages








set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

theorem exists_positioned_product_time_parameter {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1/2) :
    ∃ (φ : ℝ → ℝ) (H : Icc (-1 : ℝ) 1 ≃ₜ Icc (0 : ℝ) 1),
      FinitePiecewiseAffineOn φ (Icc (-1 : ℝ) 1) ∧ H.IsFinitePL ∧
      (∀ t, (H t : ℝ) = φ t) ∧ StrictMono φ ∧
      φ (-1) = 0 ∧ φ 1 = 1 ∧ φ (-(1/2)) = δ ∧ φ (1/2) = 1-δ ∧
      φ '' Icc (-(1/2 : ℝ)) (1/2) = Icc δ (1-δ) ∧
      φ '' Ioo (-(1/2 : ℝ)) (1/2) = Ioo δ (1-δ) := by
  let a : ℝ := 1-2*δ
  have ha : 0 < a := by dsimp [a]; linarith
  let d : ℝ := 2*δ/a
  have hd : 0 < d := div_pos (by linarith) ha
  let φ : ℝ → ℝ := fun t => a * PLFiberCompression.value d (1/2) t + 1/2
  have hc : Continuous φ := by
    exact (continuous_const.mul ((PLFiberCompression.continuous_value d).comp
      (continuous_const.prodMk continuous_id))).add continuous_const
  have hm : StrictMono φ := by
    intro x y hxy
    have hh := mul_lt_mul_of_pos_left
      (PLFiberCompression.strictMono_value (w := (1/2 : ℝ)) hd (by norm_num) hxy) ha
    dsimp [φ]
    linarith
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ :=
    isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)
  have hw : FinitePiecewiseAffineOn (fun _ : ℝ => (1/2 : ℝ)) (Icc (-1 : ℝ) 1) :=
    ⟨K,hK,hKs,K.affineOnFaces_affine (ContinuousAffineMap.const ℝ ℝ (1/2 : ℝ))⟩
  have ht : FinitePiecewiseAffineOn (fun t : ℝ => t) (Icc (-1 : ℝ) 1) :=
    ⟨K,hK,hKs,K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  have hφ : FinitePiecewiseAffineOn φ (Icc (-1 : ℝ) 1) :=
    ((PLFiberCompression.finitePiecewiseAffineOn_value d hw ht).postcomp
      (a • ContinuousAffineMap.id ℝ ℝ + ContinuousAffineMap.const ℝ ℝ (1/2))).congr
      (fun _ _ => rfl)
  have hleft : φ (-1) = 0 := by
    dsimp [φ]
    rw [PLFiberCompression.value_of_le_neg (by norm_num) (by norm_num)]
    dsimp [d,a] at *
    field_simp
    ring
  have hright : φ 1 = 1 := by
    dsimp [φ]
    rw [PLFiberCompression.value_of_width_le (by norm_num) (by norm_num)]
    dsimp [d,a] at *
    field_simp
    ring
  have hlo : φ (-(1/2)) = δ := by
    dsimp [φ]
    rw [PLFiberCompression.value_of_mem (by norm_num)]
    dsimp [a]
    ring
  have hhi : φ (1/2) = 1-δ := by
    dsimp [φ]
    rw [PLFiberCompression.value_of_mem (by norm_num)]
    dsimp [a]
    ring
  have himage : φ '' Icc (-1 : ℝ) 1 = Icc (0 : ℝ) 1 := by
    rw [hc.image_Icc_of_strictMono hm,hleft,hright]
  obtain ⟨H,hH,hHval⟩ := hφ.exists_homeomorph_image hm.injective.injOn
  let H' := H.trans (Homeomorph.setCongr himage)
  refine ⟨φ,H',hφ,hH.setCongr rfl himage,hHval,hm,hleft,hright,hlo,hhi,?_,?_⟩
  · rw [hc.image_Icc_of_strictMono hm,hlo,hhi]
  · rw [hc.image_Ioo_of_strictMono hm,hlo,hhi]

end PoincareConjecture.M76
