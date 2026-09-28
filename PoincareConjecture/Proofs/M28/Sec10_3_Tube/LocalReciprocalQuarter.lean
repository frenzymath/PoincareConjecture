import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalFrontierSeed
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalPrefixSign
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalAxialContinuation










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck



theorem exists_reciprocal_quarter_of_positive_frontier_contact_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N P : EpsilonNeck g), N.epsilon ≤ ε₀ → P.epsilon = N.epsilon →
        ∀ x : M, x ∈ frontier N.carrier →
        x ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) →
        x ∈ P.central_sphere →
        ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          {y : M | y ∈ P.carrier ∧ -N.epsilon⁻¹ < σ * (P.coordinate_inverse y).2 ∧
            σ * (P.coordinate_inverse y).2 < -N.epsilon⁻¹ / 2} ⊆
              N.region (-(0.2 : ℝ) * N.epsilon⁻¹) ((0.6 : ℝ) * N.epsilon⁻¹) := by
  obtain ⟨ε₁, hε₁, hsmall, hseed⟩ := exists_frontier_axial_seed_threshold_m28.{u}
  obtain ⟨ε₂, hε₂, _, hprefix⟩ := exists_transition_axis_prefix_signed_deriv_bounds_m28.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N P hε heq x hxfront hx hxP
  obtain ⟨σ, hσ, hband, horder⟩ := hseed N P (hε.trans (min_le_left _ _)) heq x hxfront hx hxP
  refine ⟨σ, hσ, ?_⟩
  rintro y ⟨hyP, hylo, hyhi⟩
  let R := N.epsilon⁻¹
  let q := (P.coordinate_inverse y).1
  let u := σ * (P.coordinate_inverse y).2
  let t₀ := σ * (-(0.03 : ℝ) * R)
  let v := -σ
  let δ := (0.04 : ℝ) * R
  let L := -u - (0.03 : ℝ) * R
  let s₀ := (N.coordinate_inverse (P.coordinate_map (q, t₀))).2
  have hR : 0 < R := inv_pos.mpr N.epsilon_pos
  have hu : -R < u ∧ u < -R / 2 := ⟨hylo, hyhi⟩
  have hL : (0.47 : ℝ) * R < L ∧ L < (0.97 : ℝ) * R := by
    dsimp only [L]
    constructor <;> linarith [hu.1, hu.2]
  have hLpos : 0 < L := (mul_pos (by norm_num) hR).trans hL.1
  have hδ : 0 < δ := mul_pos (by norm_num) hR
  have hδL : δ ≤ L := by dsimp only [δ]; linarith [hL.1]
  have hv : v = 1 ∨ v = -1 := by
    dsimp only [v]
    rcases hσ with rfl | rfl <;> norm_num
  have hcoord (s : ℝ) : t₀ + v * s = σ * (-(0.03 : ℝ) * R - s) := by
    dsimp only [t₀, v]
    ring
  have hdom (s : ℝ) (hs : s ∈ Icc 0 L) :
      t₀ + v * s ∈ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹ := by
    rw [hcoord, heq]
    change -R < σ * (-(0.03 : ℝ) * R - s) ∧
      σ * (-(0.03 : ℝ) * R - s) < R
    rcases hσ with rfl | rfl <;> constructor <;> nlinarith [hs.1, hs.2, hL.2]
  have hseedCarrier : MapsTo (fun s => P.coordinate_map (q, t₀ + v * s))
      (Icc 0 δ) N.carrier := by
    intro s hs
    change P.coordinate_map (q, t₀ + v * s) ∈ N.carrier
    rw [hcoord]
    apply (hband q (-(0.03 : ℝ) * R - s) ?_).1
    change -(0.08 : ℝ) * R < -(0.03 : ℝ) * R - s ∧
      -(0.03 : ℝ) * R - s < -(0.02 : ℝ) * R
    dsimp only [δ] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hstart := hband q (-(0.03 : ℝ) * R) (by
    change -(0.08 : ℝ) * R < -(0.03 : ℝ) * R ∧
      -(0.03 : ℝ) * R < -(0.02 : ℝ) * R
    constructor <;> linarith)
  have hs₀ : (0.9 : ℝ) * R < s₀ ∧ s₀ < (0.99 : ℝ) * R := hstart.2
  have hdrop : (N.coordinate_inverse (P.coordinate_map (q, t₀ + v * δ))).2 < s₀ := by
    have he : t₀ + v * δ = σ * (-(0.07 : ℝ) * R) := by
      dsimp only [t₀, v, δ]
      ring
    rw [he]
    exact horder q
  have hderiv (s : ℝ) (hs : s ∈ Icc 0 L)
      (hcontained : MapsTo (fun r => P.coordinate_map (q, t₀ + v * r)) (Icc 0 s) N.carrier) :
      (-1.1 : ℝ) ≤ v * deriv (fun t => (N.coordinate_inverse (P.coordinate_map (q, t))).2)
        (t₀ + v * s) ∧
      v * deriv (fun t => (N.coordinate_inverse (P.coordinate_map (q, t))).2)
        (t₀ + v * s) ≤ (-0.9 : ℝ) := by
    apply hprefix N P (hε.trans (min_le_right _ _))
      (heq.trans_le (hε.trans (min_le_right _ _))) q hv hδ hseedCarrier hdrop hs.1
      (fun r hr => hdom r ⟨hr.1, hr.2.trans (max_le hδL hs.2)⟩) hcontained s
    exact ⟨hs.1, le_rfl⟩
  obtain ⟨hcontained, hheight⟩ := N.axial_segment_contained_of_signed_deriv_bounds_m28 P q
    hdom hstart.1 (rfl : (N.coordinate_inverse (P.coordinate_map (q, t₀))).2 = s₀)
    hderiv (by
      apply lt_min <;> change -R < _ <;> linarith [hs₀.1, hL.2]) (by
      apply max_lt <;> change _ < R <;> linarith [hs₀.2])
  have htarget : t₀ + v * L = (P.coordinate_inverse y).2 := by
    calc
      _ = σ * u := by dsimp only [t₀, v, L]; ring
      _ = _ := by dsimp only [u]; rcases hσ with rfl | rfl <;> ring
  have hyEq : P.coordinate_map (q, t₀ + v * L) = y := by
    rw [htarget]
    exact P.coordinate_map_coordinate_inverse hyP
  have hbounds := hheight L ⟨hLpos.le, le_rfl⟩
  rw [hyEq] at hbounds
  refine ⟨hyEq ▸ hcontained ⟨hLpos.le, le_rfl⟩, ?_, ?_⟩
  · change -(0.2 : ℝ) * R < _
    linarith [hbounds.1, hs₀.1, hL.2]
  · change _ < (0.6 : ℝ) * R
    linarith [hbounds.2, hs₀.2, hL.1]

end PoincareConjecture.EpsilonNeck
