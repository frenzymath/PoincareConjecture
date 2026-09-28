import PoincareConjecture.Proofs.M34.Mathlib.NeckCovariantArrayBounds
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.CylinderCovariantJetBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff BigOperators Topology

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

theorem roundCylinderChristoffel_compact_time_jet_bound
    {I : Set ℝ} (hI : IsCompact I) (hI1 : I ⊆ Iio (1 : ℝ))
    {K : Set RoundCylinderCoordinates} (hK : IsCompact K) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ I, ∀ q : UnitTwoSphere,
      ∀ x ∈ K, ∀ a b d : Fin 3,
        ‖iteratedFDeriv ℝ m (fun y =>
          roundCylinderChristoffel u (chartAt E₂ q) y a b d) x‖ ≤ C := by
  classical
  let q₀ : UnitTwoSphere := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hbounds (a : Fin 3 × Fin 3 × Fin 3) : ∃ C : ℝ,
      ∀ u ∈ I, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (fun y =>
          roundCylinderChristoffel u (chartAt E₂ q₀) y a.1 a.2.1 a.2.2) x‖ ≤ C := by
    have hs := roundCylinderChristoffel_joint_contDiffOn q₀ a.1 a.2.1 a.2.2
    have hc := (hs.iteratedFDeriv_snd_of_isOpen isOpen_univ m).continuousOn
    obtain ⟨C, hC⟩ := (hI.prod hK).exists_bound_of_continuousOn
      (hc.mono (fun z hz => ⟨hI1 hz.1, mem_univ _⟩))
    exact ⟨C, fun u hu x hx => hC (u, x) ⟨hu, hx⟩⟩
  choose C hC using hbounds
  let D : ℝ := ∑ a : Fin 3 × Fin 3 × Fin 3, max (C a) 0
  refine ⟨D, Finset.sum_nonneg (fun _ _ => le_max_right _ _), ?_⟩
  intro u hu q x hx a b d
  rw [roundCylinderChristoffel_eq_chart_center u q₀ q]
  exact (hC (a, b, d) u hu x hx).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ (a, b, d))))

theorem exists_roundCylinder_covariant_difference_component_bound
    {I : Set ℝ} (hI : IsCompact I) (hI1 : I ⊆ Iio (1 : ℝ))
    {K : Set RoundCylinderCoordinates} (hK : IsCompact K) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ I, ∀ (q : UnitTwoSphere)
      (B D : RoundCylinderTwoTensor) (epsilon : ℝ),
      RoundCylinderTensorSmoothOn epsilon B → RoundCylinderTensorSmoothOn epsilon D →
      ∀ x ∈ K, x ∈ (chartAt E₂ q).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ A : ℝ, 0 ≤ A →
      (∀ j ≤ N, ∀ a b : Fin 3, ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
          roundCylinderTensorCoefficient D (chartAt E₂ q) y a b) x‖ ≤ A) →
      ∀ k ≤ N, ∀ a : Fin (2 + k) → Fin 3,
        |roundCylinderIteratedDerivative u (chartAt E₂ q) B k x a -
          roundCylinderIteratedDerivative u (chartAt E₂ q) D k x a| ≤ C * A := by
  classical
  choose G hG hGb using fun j : Fin (N + 1) =>
    roundCylinderChristoffel_compact_time_jet_bound hI hI1 hK j
  let G₀ : ℝ := ∑ j : Fin (N + 1), G j
  have hG₀ : 0 ≤ G₀ := Finset.sum_nonneg fun j _ => hG j
  let L : ℝ := max 1 ((∑ i : Fin 3,
    ‖ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis i)‖) +
      (2 + N : ℕ) * 3 * (2 : ℝ) ^ N * G₀)
  have hL₁ : 1 ≤ L := le_max_left _ _
  refine ⟨L ^ N, pow_nonneg (zero_le_one.trans hL₁) _, ?_⟩
  intro u hu q B D epsilon hB hD x hx hxdom A hA hb k hk a
  let Ω := (chartAt E₂ q).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹
  have hΩ : IsOpen Ω := (chartAt E₂ q).open_target.prod isOpen_Ioo
  have hu1 : u < 1 := hI1 hu
  have hg (i j : Fin 3) : ContDiff ℝ ∞
      (fun y => roundCylinderGram u (chartAt E₂ q) y i j) :=
    (roundCylinderGram_joint_contDiff q i j).comp (contDiff_const.prodMk contDiff_id)
  have hBs (y : RoundCylinderCoordinates) (hy : y ∈ Ω) (l : ℕ) (b : Fin (2 + l) → Fin 3) :
      ContDiffAt ℝ ∞ (fun z => roundCylinderIteratedDerivative u (chartAt E₂ q) B l z b) y :=
    roundCylinderIteratedDerivative_contDiffAt hu1 q
      (fun i j => ((hB q i j).contDiffAt (hΩ.mem_nhds hy)).sub (hg i j).contDiffAt) l b
  have hDs (y : RoundCylinderCoordinates) (hy : y ∈ Ω) (l : ℕ) (b : Fin (2 + l) → Fin 3) :
      ContDiffAt ℝ ∞ (fun z => roundCylinderIteratedDerivative u (chartAt E₂ q) D l z b) y :=
    roundCylinderIteratedDerivative_contDiffAt hu1 q
      (fun i j => ((hD q i j).contDiffAt (hΩ.mem_nhds hy)).sub (hg i j).contDiffAt) l b
  let T := fun (l : ℕ) (y : RoundCylinderCoordinates) (b : Fin (2 + l) → Fin 3) =>
    roundCylinderIteratedDerivative u (chartAt E₂ q) B l y b -
      roundCylinderIteratedDerivative u (chartAt E₂ q) D l y b
  have hTs (l : ℕ) (b : Fin (2 + l) → Fin 3) : ContDiffAt ℝ ∞ (fun y => T l y b) x :=
    (hBs x hxdom l b).sub (hDs x hxdom l b)
  have hΓ (j : ℕ) (hj : j ≤ N) (i b d : Fin 3) :
      ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderChristoffel u (chartAt E₂ q) y i b d) x‖ ≤ G₀ := by
    let l : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    exact (hGb l u hu q x hx i b d).trans
      (Finset.single_le_sum (fun j _ => hG j) (Finset.mem_univ l))
  have h := norm_covariantArray_jet_le_of_total_order
    roundCylinderCoordinateBasis 2 N x
    (roundCylinderChristoffel u (chartAt E₂ q)) T
    (fun i b d => (contDiff_roundCylinderChristoffel hu1 q i b d).contDiffAt)
    (fun l _ b => hTs l b) ?_ hG₀ hL₁ hA
    (by norm_num only [Fintype.card_fin]; exact le_max_right _ _) hΓ ?_ k 0
      (by simpa using hk) a
  · simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL₁ hk) hA)
  · intro l _ b
    filter_upwards [hΩ.mem_nhds hxdom] with y hy
    dsimp only [T, roundCylinderIteratedDerivative, roundCylinderTensorDerivative]
    have hfd : fderiv ℝ (fun z =>
        roundCylinderIteratedDerivative u (chartAt E₂ q) B l z (fun i => b i.succ) -
          roundCylinderIteratedDerivative u (chartAt E₂ q) D l z (fun i => b i.succ)) y =
        fderiv ℝ (fun z => roundCylinderIteratedDerivative u (chartAt E₂ q) B l z
          (fun i => b i.succ)) y -
        fderiv ℝ (fun z => roundCylinderIteratedDerivative u (chartAt E₂ q) D l z
          (fun i => b i.succ)) y :=
      fderiv_sub ((hBs y hy l (fun i => b i.succ)).differentiableAt (by simp))
        ((hDs y hy l (fun i => b i.succ)).differentiableAt (by simp))
    rw [hfd]
    have hzero : (⟨0, by omega⟩ : Fin (2 + (l + 1))) = 0 := by
      apply Fin.ext
      simp
    simp only [hzero, sub_apply, mul_sub, Finset.sum_sub_distrib]
    have hswap (v w z t : ℝ) : (v - w) - (z - t) = (v - z) - (w - t) := by ring
    exact hswap _ _ _ _
  · intro j hj b
    have heq : (fun y => T 0 y b) = (fun y =>
        roundCylinderTensorCoefficient B (chartAt E₂ q) y (b 0) (b 1) -
          roundCylinderTensorCoefficient D (chartAt E₂ q) y (b 0) (b 1)) := by
      funext y
      dsimp only [T, roundCylinderIteratedDerivative]
      ring
    rw [heq]
    exact hb j hj (b 0) (b 1)

end PoincareConjecture.M34
