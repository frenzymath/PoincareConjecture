import PoincareConjecture.Proofs.M34.Mathlib.RoundCylinderFiniteJets
import PoincareConjecture.Proofs.M34.Mathlib.MatrixInverseSmoothOn
import PoincareConjecture.Proofs.M34.Mathlib.ParameterSpatialDerivatives











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "Q" => Set.prod (Iio (1 : ℝ)) (univ : Set RoundCylinderCoordinates)



theorem roundCylinderGram_joint_contDiff (q : UnitTwoSphere) (a b : Fin 3) :
    ContDiff ℝ ∞ (fun z : ℝ × RoundCylinderCoordinates =>
      roundCylinderGram z.1 (chartAt E₂ q) z.2 a b) := by
  simp_rw [roundCylinderGram_eq_stereographic_formula]
  have hρ : ContDiff ℝ ∞ (fun z : ℝ × RoundCylinderCoordinates =>
      (16 : ℝ) / (‖z.2.1‖ ^ 2 + 4) ^ 2) :=
    contDiff_const.div
      (((contDiff_norm_sq ℝ).comp contDiff_snd.fst).add contDiff_const |>.pow 2)
      (fun _ => by positivity)
  exact ((contDiff_const.mul (contDiff_const.sub contDiff_fst)).mul hρ
    |>.mul contDiff_const).add contDiff_const



theorem roundCylinderGram_inv_joint_contDiffOn (q : UnitTwoSphere) (a b : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : ℝ × RoundCylinderCoordinates =>
      (roundCylinderGram z.1 (chartAt E₂ q) z.2)⁻¹ a b) Q :=
  ContDiffOn.matrix_inv (fun i j => (roundCylinderGram_joint_contDiff q i j).contDiffOn)
    (fun z hz => roundCylinderGram_det_ne_zero hz.1 q z.2) a b



theorem roundCylinderChristoffel_joint_contDiffOn (q : UnitTwoSphere) (a b d : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : ℝ × RoundCylinderCoordinates =>
      roundCylinderChristoffel z.1 (chartAt E₂ q) z.2 a b d) Q := by
  have hd (i j k : Fin 3) : ContDiffOn ℝ ∞
      (fun z : ℝ × RoundCylinderCoordinates => fderiv ℝ
        (fun y => roundCylinderGram z.1 (chartAt E₂ q) y i j) z.2
          (roundCylinderCoordinateBasis k)) Q :=
    ((roundCylinderGram_joint_contDiff q i j).contDiffOn.fderiv_snd_of_isOpen
      (S := Iio (1 : ℝ)) isOpen_univ).clm_apply contDiffOn_const
  unfold roundCylinderChristoffel
  exact contDiffOn_const.mul (ContDiffOn.sum fun j _ =>
    (roundCylinderGram_inv_joint_contDiffOn q a j).mul
      (((hd d j b).add (hd b j d)).sub (hd b d j)))




theorem roundCylinderChristoffel_uniform_spatial_jet_bound
    {T : ℝ} (hT : T < 1) {K : Set RoundCylinderCoordinates} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Icc (0 : ℝ) T, ∀ q : UnitTwoSphere,
      ∀ x ∈ K, ∀ a b d : Fin 3,
        ‖iteratedFDeriv ℝ m (fun y =>
          roundCylinderChristoffel u (chartAt E₂ q) y a b d) x‖ ≤ C := by
  classical
  let q₀ : UnitTwoSphere := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hcompact : IsCompact (Icc (0 : ℝ) T ×ˢ K) := isCompact_Icc.prod hK
  have hbounds (a : Fin 3 × Fin 3 × Fin 3) : ∃ C : ℝ,
      ∀ u ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (fun y =>
          roundCylinderChristoffel u (chartAt E₂ q₀) y a.1 a.2.1 a.2.2) x‖ ≤ C := by
    have hs := roundCylinderChristoffel_joint_contDiffOn q₀ a.1 a.2.1 a.2.2
    have hc := (hs.iteratedFDeriv_snd_of_isOpen isOpen_univ m).continuousOn
    obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
      (hc.mono (fun z hz => ⟨hz.1.2.trans_lt hT, mem_univ _⟩))
    exact ⟨C, fun u hu x hx => hC (u, x) ⟨hu, hx⟩⟩
  choose C hC using hbounds
  let D : ℝ := ∑ a : Fin 3 × Fin 3 × Fin 3, max (C a) 0
  refine ⟨D, Finset.sum_nonneg (fun _ _ => le_max_right _ _), ?_⟩
  intro u hu q x hx a b d
  rw [roundCylinderChristoffel_eq_chart_center u q₀ q]
  exact (hC (a, b, d) u hu x hx).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ (a, b, d))))

end PoincareConjecture.M34
