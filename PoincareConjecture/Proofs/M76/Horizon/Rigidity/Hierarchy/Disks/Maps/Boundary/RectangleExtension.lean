import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.Boundary.SquareExtension



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

private theorem normalized_interval {l u x : ℝ} (h : l < u) :
    (2 * x - l - u) / (u - l) ∈ Icc (-1 : ℝ) 1 ↔ x ∈ Icc l u := by
  rw [mem_Icc, le_div_iff₀ (sub_pos.mpr h), div_le_iff₀ (sub_pos.mpr h)]
  constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith




theorem exists_finitePL_rectangle_extension_of_injective_rim
    (f : V2 → ℝ × ℝ) (hf : FinitePiecewiseAffineOn f D)
    {alpha beta a b : ℝ} (hab : alpha < beta) (horder : a < b)
    (hrange : MapsTo f D (Icc alpha beta ×ˢ Icc a b))
    (hedges : ∀ z ∈ Q, (f z).1 ∈ ({alpha, beta} : Set ℝ) ∨
      (f z).2 ∈ ({a, b} : Set ℝ)) (hinj : InjOn f Q) :
    ∃ H : D ≃ₜ (Icc alpha beta ×ˢ Icc a b), H.IsFinitePL ∧
      ∀ z : Q, (H ⟨z, sphere_subset_closedBall z.property⟩ : ℝ × ℝ) = f z := by
  let A : (ℝ × ℝ) →ᴬ[ℝ] V2 :=
    (ContinuousLinearMap.pi ![(2 / (beta - alpha)) • ContinuousLinearMap.fst ℝ ℝ ℝ,
      (2 / (b - a)) • ContinuousLinearMap.snd ℝ ℝ ℝ]).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ (ℝ × ℝ)
        ![-(alpha + beta) / (beta - alpha), -(a + b) / (b - a)]
  let B : V2 →ᴬ[ℝ] (ℝ × ℝ) :=
    ((((beta - alpha) / 2) • (ContinuousLinearMap.proj (0 : Fin 2) : V2 →L[ℝ] ℝ)).prod
      (((b - a) / 2) • (ContinuousLinearMap.proj (1 : Fin 2) : V2 →L[ℝ] ℝ))).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ V2 ((alpha + beta) / 2, (a + b) / 2)
  have hA (x : ℝ × ℝ) : A x =
      ![(2 * x.1 - alpha - beta) / (beta - alpha), (2 * x.2 - a - b) / (b - a)] := by
    ext i
    fin_cases i <;> dsimp [A] <;> simp only [smul_apply, smul_eq_mul] <;> dsimp <;> ring
  have hB (z : V2) : B z =
      (((beta - alpha) * z 0 + alpha + beta) / 2, ((b - a) * z 1 + a + b) / 2) := by
    dsimp [B]
    simp only [smul_apply, smul_eq_mul]
    apply Prod.ext <;> dsimp <;> ring
  have hBA (x : ℝ × ℝ) : B (A x) = x := by
    rw [hB, hA]
    apply Prod.ext <;> dsimp <;>
      field_simp [ne_of_gt (sub_pos.mpr hab), ne_of_gt (sub_pos.mpr horder)] <;> ring
  have hAB (z : V2) : A (B z) = z := by
    rw [hA, hB]
    ext i
    fin_cases i <;> dsimp <;>
      field_simp [ne_of_gt (sub_pos.mpr hab), ne_of_gt (sub_pos.mpr horder)] <;> ring
  have hAmem (x : ℝ × ℝ) : A x ∈ D ↔ x ∈ Icc alpha beta ×ˢ Icc a b := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one, hA]
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, abs_le, ← mem_Icc]
    exact and_congr (normalized_interval hab) (normalized_interval horder)
  have hBmem (z : V2) : B z ∈ Icc alpha beta ×ˢ Icc a b ↔ z ∈ D := by
    rw [← hAmem, hAB]
  have hAi : Function.Injective A := Function.LeftInverse.injective hBA
  have hBi : Function.Injective B := Function.RightInverse.injective hAB
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKD, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  let L := K.frontierSubcomplex D
  have hL : L.faces.Finite := K.frontierSubcomplex_finite _ hK
  have hLQ : L.space = Q := by
    rw [K.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKD,
      frontier_closedBall _ one_ne_zero]
  have hgPL : FinitePiecewiseAffineOn (A ∘ f) Q := by
    rw [← hLQ]
    exact (hf.postcomp A).restrict L hL (hLQ.subset.trans sphere_subset_closedBall)
  have hgmap : MapsTo (A ∘ f) Q Q := by
    intro z hz
    have hle : ‖A (f z)‖ ≤ 1 := (mem_closedBall_zero_iff.mp
      ((hAmem _).mpr (hrange (sphere_subset_closedBall hz))))
    rw [mem_sphere_zero_iff_norm]
    apply le_antisymm hle
    by_contra hge
    have hlt := (pi_norm_lt_iff zero_lt_one).mp (lt_of_not_ge hge)
    have h0 := hlt 0
    have h1 := hlt 1
    rw [hA] at h0 h1
    rcases hedges z hz with he | he <;>
      simp only [mem_insert_iff, mem_singleton_iff] at he
    · rcases he with he | he
      · simp only [Matrix.cons_val_zero, he, Real.norm_eq_abs] at h0
        have : (2 * alpha - alpha - beta) / (beta - alpha) = -1 := by
          apply (div_eq_iff (ne_of_gt (sub_pos.mpr hab))).mpr
          ring
        rw [this] at h0
        norm_num at h0
      · simp only [Matrix.cons_val_zero, he, Real.norm_eq_abs] at h0
        have : (2 * beta - alpha - beta) / (beta - alpha) = 1 := by
          apply (div_eq_iff (ne_of_gt (sub_pos.mpr hab))).mpr
          ring
        rw [this] at h0
        norm_num at h0
    · rcases he with he | he
      · simp only [Matrix.cons_val_one, he, Real.norm_eq_abs] at h1
        have : (2 * a - a - b) / (b - a) = -1 := by
          apply (div_eq_iff (ne_of_gt (sub_pos.mpr horder))).mpr
          ring
        rw [this] at h1
        norm_num at h1
      · simp only [Matrix.cons_val_one, he, Real.norm_eq_abs] at h1
        have : (2 * b - a - b) / (b - a) = 1 := by
          apply (div_eq_iff (ne_of_gt (sub_pos.mpr horder))).mpr
          ring
        rw [this] at h1
        norm_num at h1
  obtain ⟨H, hH, hHrim⟩ := exists_finitePL_square_extension_of_injective_rim
    (A ∘ f) hgPL hgmap (fun _ hx _ hy heq => hinj hx hy (hAi heq))
  have hBPL : FinitePiecewiseAffineOn B D :=
    ⟨K, hK, hKD, K.affineOnFaces_affine B⟩
  obtain ⟨J, hJ, hJval⟩ := hBPL.exists_homeomorph_image hBi.injOn
  have himage : B '' D = Icc alpha beta ×ˢ Icc a b := by
    apply subset_antisymm
    · rintro y ⟨z, hz, rfl⟩
      exact (hBmem z).mpr hz
    · intro y hy
      exact ⟨A y, (hAmem y).mpr hy, hBA y⟩
  let J' : D ≃ₜ (Icc alpha beta ×ˢ Icc a b) := J.trans (Homeomorph.setCongr himage)
  have hJ' : J'.IsFinitePL := ⟨B, hBPL, hJval⟩
  refine ⟨H.trans J', hH.trans hJ', fun z => ?_⟩
  change (J' (H ⟨z, sphere_subset_closedBall z.property⟩) : ℝ × ℝ) = f z
  rw [show ∀ x : D, (J' x : ℝ × ℝ) = B x from hJval, hHrim]
  exact hBA (f z)

end PoincareConjecture.M76
