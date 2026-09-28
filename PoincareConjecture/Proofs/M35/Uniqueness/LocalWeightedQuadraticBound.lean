import PoincareConjecture.Proofs.M35.Uniqueness.RawQuadraticBound
import PoincareConjecture.Proofs.M35.Uniqueness.RawCommonCarrier









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.Uniqueness

theorem exists_raw_local_weighted_quadratic_heat_bound
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T c d a I : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hc : 0 < c) (hd : 0 ≤ d)
    (ha : 0 ≤ a) (hI : 0 ≤ I) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ C₀ : Set StandardCapSpace, IsCompact C₀ →
      ∃ E : Set StandardCapSpace, IsCompact E ∧ C₀ ⊆ interior E ∧
      ∀ Q : ℝ → StandardCapSpace → ℝ,
        ContinuousOn (Function.uncurry Q) (Icc 0 T ×ˢ E) →
        (∀ t ∈ Icc 0 T, ∀ x ∈ E, 0 ≤ Q t x) →
        (∀ x ∈ E, a * Q 0 x ≤ I) →
        (∀ t ∈ Ioc 0 T, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (Q t)) →
        (∀ t ∈ Ioc 0 T, ∀ x ∈ E, ∃ v : ℝ,
          HasDerivWithinAt (fun s => Q s x) v (Icc 0 t) t ∧
            v - (G.flow.connection t).laplacian (Q t) x ≤ -c * Q t x ^ 2 + d) →
        ∀ t ∈ Icc 0 T, ∀ p ∈ C₀, (a + t) * Q t p ≤ C := by
  obtain ⟨K₀, hK₀, hbound⟩ := G.curvature_locally_bounded T hT.le hTlt
  let K := K₀ + 1
  have hK : 0 < K := by dsimp only [K]; linarith
  have hRm (t : ℝ) (ht : t ∈ Icc 0 T) (x : StandardCapSpace) :
      (G.flow.connection t).curvatureTensorNorm x ≤ K := by
    have hh := (le_abs_self _).trans (hbound t ht x)
    dsimp only [K]
    linarith
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow G.flow
    (K := Icc 0 T) (fun t ht => ⟨ht.1, ht.2.trans_lt hTlt⟩)
    (ordConnected_Icc : (Icc (0 : ℝ) T).OrdConnected)
    (show (Icc (0 : ℝ) T).Nontrivial from
      ⟨0, ⟨le_rfl, hT.le⟩, T, ⟨hT.le, le_rfl⟩, hT.ne⟩)
  obtain ⟨L, H, hL, hH, hcutoff⟩ :=
    M04.exists_shi_geometric_cutoff 3 K (K * T) 1 hK (by norm_num)
  let C := max I (M04.shiCutoffThreshold c d L H (a + T))
  refine ⟨C, hI.trans (le_max_left _ _), ?_⟩
  intro C₀ hC₀
  let R := M04.shiRetainedFlowRadius 3 (K * T) 1
  have hR : 0 < R := M04.shiRetainedFlowRadius_pos (by norm_num)
  obtain ⟨E, hE, hCE, hballs⟩ := exists_raw_common_ball_carrier P G hT hTlt hR hC₀
  refine ⟨E, hE, hCE, ?_⟩
  intro Q hcont hQ hinit hspace hheat t ht p hp
  have htime : T ≤ K * T / K := by rw [mul_div_cancel_left₀ T hK.ne']
  obtain ⟨_, η, hη, hη0, hη1, hboundary, hηp, hsupport⟩ :=
    hcutoff StandardCapSpace T hT.le htime F p E hE
      (fun s hs => hballs s hs p hp) (fun s hs y _ => hRm s hs y)
  have hestimate := M04.shi_cutoff_bound F.metric F.connection hE
    (S := T) (κ := 1) (c := c) (d := d) (L := L) (G := H) (Θ := a + T) (a := a) (I := I)
    hT (by norm_num) hc hd hL hH ha hI le_rfl
    Q η hcont hη hQ hη0 hη1 hboundary
    (fun y hy => by
      calc
        a * η 0 y * Q 0 y = η 0 y * (a * Q 0 y) := by ring
        _ ≤ 1 * (a * Q 0 y) := mul_le_mul_of_nonneg_right
          (hη1 0 ⟨le_rfl, hT.le⟩ y hy) (mul_nonneg ha (hQ 0 ⟨le_rfl, hT.le⟩ y hy))
        _ ≤ I := by simpa only [one_mul] using hinit y hy) hspace
    (fun s hs y hy => by simpa only [one_mul] using! hheat s hs y (interior_subset hy))
    (by simpa only [M04.shiPhysicalCutoffSupports, one_mul] using hsupport)
  simpa only [hηp t ht, mul_one, C] using
    hestimate t ht p (interior_subset (hCE hp))

end PoincareConjecture.M35.Uniqueness
