import PoincareConjecture.Proofs.M25.AppA_1_Necks.TransitionHeight
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SharpDepth

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_buffered_slice_height_control :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (A D : EpsilonNeck g),
      A.epsilon ≤ epsilon0 → D.epsilon = A.epsilon →
      ∀ (p : UnitTwoSphere) (s : ℝ),
        s ∈ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ →
        A.coordinate_map (p, s) ∈ D.carrier →
        |(D.coordinate_inverse (A.coordinate_map (p, s))).2| ≤
          (99 / 100 : ℝ) * D.epsilon⁻¹ →
        let h : UnitTwoSphere → ℝ := fun q =>
          (D.coordinate_inverse (A.coordinate_map (q, s))).2
        (∀ q : UnitTwoSphere, A.coordinate_map (q, s) ∈ D.carrier) ∧
        (∀ p q : UnitTwoSphere, |h q - h p| ≤ Real.pi) ∧
        ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
          ∀ q : UnitTwoSphere,
            |deriv (fun r => (D.coordinate_inverse
                (A.coordinate_map (q, r))).2) s - sigma| ≤ (1 / 100 : ℝ) ∧
            0 < sigma * (D.scale * mvfderiv (𝓡 3)
              (fun x => (D.coordinate_inverse x).2) (A.coordinate_map (q, s))
              (A.normalizedAxialVector (A.coordinate_map (q, s)))) := by
  let B0 : ℝ := Real.sqrt 2 * (Real.pi + 1)
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  have hden : 0 < 10000 * (B0 + Real.pi + 1) := by positivity
  obtain ⟨es, hspos, hscap, hscale⟩ :=
    exists_intersecting_scale_control.{u} (α := (1 / 1000 : ℝ)) (by norm_num)
  obtain ⟨ea, hapos, _, horient⟩ :=
    exists_intersecting_coherent_orientation.{u}
      (η := (1 / 1000 : ℝ)) (by norm_num)
  obtain ⟨eh, hhpos, _, hhorizontal⟩ :=
    exists_intersecting_transition_height_horizontal_bound.{u}
      (α := (1 : ℝ)) (by norm_num)
  refine ⟨min es (min ea (min eh (min (1 / 10000)
    (1 / (10000 * (B0 + Real.pi + 1)))))),
    lt_min hspos (lt_min hapos (lt_min hhpos
      (lt_min (by norm_num) (div_pos zero_lt_one hden)))),
    (min_le_left _ _).trans hscap, ?_⟩
  intro M _ _ _ _ _ _ g A D hA heD p s hs hp hbuffer
  classical
  dsimp only
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let L : ℝ := A.epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr A.epsilon_pos
  rcases le_min_iff.mp hA with ⟨hes, hrest⟩
  rcases le_min_iff.mp hrest with ⟨hea, hrest⟩
  rcases le_min_iff.mp hrest with ⟨heh, hrest⟩
  rcases le_min_iff.mp hrest with ⟨hesmall, henumeric⟩
  have hDs : D.epsilon ≤ es := by rw [heD]; exact hes
  have hDa : D.epsilon ≤ ea := by rw [heD]; exact hea
  have hDh : D.epsilon ≤ eh := by rw [heD]; exact heh
  have hbudget : (B0 + Real.pi + 1) * A.epsilon ≤ 1 / 10000 := by
    have h := (le_div_iff₀ hden).mp henumeric
    nlinarith only [h]
  have hB0budget : B0 * A.epsilon ≤ 1 / 10000 := by
    nlinarith only [hbudget, A.epsilon_pos, mul_pos Real.pi_pos A.epsilon_pos]
  have hB0L : B0 ≤ L / 10000 := by
    calc
      B0 ≤ (1 / 10000) / A.epsilon :=
        (le_div_iff₀ A.epsilon_pos).mpr hB0budget
      _ = L / 10000 := by dsimp only [L]; ring
  have hsqlo : (999 : ℝ) / 1000 ≤ Real.sqrt (1 - A.epsilon) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hesmall])
  have hsqhi : Real.sqrt (1 + A.epsilon) ≤ (1001 : ℝ) / 1000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [hesmall]⟩
  have hsqpos : 0 < Real.sqrt (1 - A.epsilon) := by linarith only [hsqlo]
  have hratio : |A.scale / D.scale - 1| < (1 / 1000 : ℝ) :=
    (hscale D A hDs hes
      ⟨A.coordinate_map (p, s), hp, A.coordinate_map_mem ⟨mem_univ _, hs⟩⟩).2
  have hscaleAD : A.scale ≤ (1001 / 1000 : ℝ) * D.scale := by
    apply (div_le_iff₀ D.scale_pos).mp
    linarith only [(abs_lt.mp hratio).2]
  have hcoeff : A.scale * Real.sqrt (1 + A.epsilon) ≤
      (101 / 100 : ℝ) * (D.scale * Real.sqrt (1 - A.epsilon)) := by
    calc
      _ ≤ ((1001 / 1000 : ℝ) * D.scale) * (1001 / 1000) :=
        mul_le_mul hscaleAD hsqhi (Real.sqrt_nonneg _)
          (mul_nonneg (by norm_num) D.scale_pos.le)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hsqlo D.scale_pos.le
        linarith only [h, D.scale_pos]
  have hbuffer' : |(D.coordinate_inverse (A.coordinate_map (p, s))).2| ≤
      (99 / 100 : ℝ) * L := by
    simpa only [heD, L] using hbuffer
  have hdepthnonneg :
      0 ≤ L - |(D.coordinate_inverse (A.coordinate_map (p, s))).2| := by
    linarith only [hbuffer', hL]
  have hwhole (q : UnitTwoSphere) : A.coordinate_map (q, s) ∈ D.carrier := by
    by_contra hout
    have hdist := A.edist_le_axial_add
      (x := A.coordinate_map (p, s)) (y := A.coordinate_map (q, s))
      (A.coordinate_map_mem ⟨mem_univ _, hs⟩)
      (A.coordinate_map_mem ⟨mem_univ _, hs⟩)
    rw [A.coordinate_inverse_coordinate_map ⟨mem_univ q, hs⟩,
      A.coordinate_inverse_coordinate_map ⟨mem_univ p, hs⟩,
      sub_self, abs_zero, zero_add] at hdist
    have hdepth := D.axialDepth_edist_le
      (A.coordinate_map (p, s)) (A.coordinate_map (q, s))
    simp only [axialDepth, if_pos hp, if_neg hout, heD, sub_zero] at hdepth
    change ENNReal.ofReal (D.scale * Real.sqrt (1 - A.epsilon) *
      abs (L - |(D.coordinate_inverse (A.coordinate_map (p, s))).2|)) ≤ _ at hdepth
    rw [abs_of_nonneg hdepthnonneg] at hdepth
    have hreal := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg A.scale_pos.le (Real.sqrt_nonneg _)) hB0.le)).mp
        (hdepth.trans hdist)
    have hscaled : D.scale * Real.sqrt (1 - A.epsilon) *
        (L - |(D.coordinate_inverse (A.coordinate_map (p, s))).2|) ≤
        (D.scale * Real.sqrt (1 - A.epsilon)) * ((101 / 100 : ℝ) * B0) := by
      calc
        _ ≤ A.scale * Real.sqrt (1 + A.epsilon) * B0 := hreal
        _ ≤ ((101 / 100 : ℝ) * (D.scale * Real.sqrt (1 - A.epsilon))) * B0 :=
          mul_le_mul_of_nonneg_right hcoeff hB0.le
        _ = _ := by ring
    have hbound :=
      (mul_le_mul_iff_right₀ (mul_pos D.scale_pos hsqpos)).mp hscaled
    nlinarith only [hbound, hbuffer', hB0L, hL]
  refine ⟨hwhole, ?_, ?_⟩
  · intro p' q
    have hsmooth := A.contMDiff_transition_height_slice D hs hwhole
    have hslope (z : UnitTwoSphere) (v : TangentSpace (𝓡 2) z) :
        |mvfderiv (𝓡 2)
          (fun q : UnitTwoSphere => (D.coordinate_inverse (A.coordinate_map (q, s))).2)
          z v| ≤ (1 : ℝ) * (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
            (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1) z v) :=
      hhorizontal A D heh hDh (z, s) ⟨mem_univ _, hs⟩ (hwhole z) v
    simpa only [one_mul] using
      sphere_height_oscillation_of_intrinsic_slope hsmooth
        (show (0 : ℝ) < 1 by norm_num) hslope p' q
  · let S : Set RoundCylinderSpace := univ ×ˢ Icc s s
    have hpre : IsPreconnected S :=
      isPreconnected_univ.prod (convex_Icc _ _).isPreconnected
    have hsub : S ⊆ A.cylinderDomain ∩ A.coordinate_map ⁻¹' D.carrier := by
      rintro ⟨q, t⟩ ⟨_, ht⟩
      have ht' : t = s := le_antisymm ht.2 ht.1
      subst t
      exact ⟨⟨mem_univ _, hs⟩, hwhole q⟩
    obtain ⟨sigma, hsigma, haxis⟩ := horient A D hea hDa S hpre hsub
    refine ⟨sigma, hsigma, ?_⟩
    intro q
    have hz : (q, s) ∈ S := ⟨mem_univ _, le_rfl, le_rfl⟩
    have hax : |1 - sigma * (D.scale * mvfderiv (𝓡 3)
        (fun x => (D.coordinate_inverse x).2) (A.coordinate_map (q, s))
        (A.normalizedAxialVector (A.coordinate_map (q, s))))| < (1 / 1000 : ℝ) := by
      simpa only [mul_assoc] using haxis (q, s) hz
    have hder := A.transition_height_axial_error D
      ⟨mem_univ q, hs⟩ (hwhole q) hsigma (by norm_num : (0 : ℝ) ≤ 1 / 1000)
      hratio.le (by linarith only [(abs_lt.mp hratio).2]) hax.le
    constructor
    · exact hder.trans (by norm_num)
    · linarith only [(abs_lt.mp hax).2]

end PoincareConjecture.EpsilonNeck
