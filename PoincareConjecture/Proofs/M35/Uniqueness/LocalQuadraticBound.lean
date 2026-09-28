import PoincareConjecture.Proofs.M35.Uniqueness.RawQuadraticBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.Uniqueness

theorem exists_raw_local_quadratic_heat_bound
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T c d : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hc : 0 < c) (hd : 0 ≤ d)
    (p : StandardCapSpace) :
    ∃ E : Set StandardCapSpace, IsCompact E ∧ p ∈ E ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℝ → StandardCapSpace → ℝ,
        ContinuousOn (Function.uncurry Q) (Icc 0 T ×ˢ E) →
        (∀ t ∈ Icc 0 T, ∀ x ∈ E, 0 ≤ Q t x) →
        (∀ t ∈ Ioc 0 T, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (Q t)) →
        (∀ t ∈ Ioc 0 T, ∀ x ∈ E, ∃ a : ℝ,
          HasDerivWithinAt (fun s => Q s x) a (Icc 0 t) t ∧
            a - (G.flow.connection t).laplacian (Q t) x ≤ -c * Q t x ^ 2 + d) →
        ∀ t ∈ Icc 0 T, t * Q t p ≤ C := by
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
  let R := M04.shiRetainedFlowRadius 3 (K * T) 1
  have hR : 0 < R := M04.shiRetainedFlowRadius_pos (by norm_num)
  obtain ⟨E, hE, hp, hexhaust⟩ := exists_raw_distance_square_compact_exhaustion
    P G hT.le hTlt p p (A := R ^ 2 + 2) (by positivity)
  have hballs (s : ℝ) (hs : s ∈ Icc 0 T) :
      closure ((F.metric s).ball p R) ⊆ E := by
    apply closure_minimal _ hE.isClosed
    intro y hy
    by_contra hn
    have hnot : y ∉ interior E := fun h => hn (interior_subset h)
    have hlarge := hexhaust s hs y hnot
    have hsmall : ((G.flow.metric s).edist p y).toReal < R := by
      have hh := (ENNReal.toReal_lt_toReal ((G.flow.metric s).edist_ne_top p y)
        ENNReal.ofReal_ne_top).mpr hy
      simpa only [ENNReal.toReal_ofReal hR.le] using hh
    change R ^ 2 + 2 ≤ 1 + ((G.flow.metric s).edist p y).toReal ^ 2 at hlarge
    have hdist : 0 ≤ ((G.flow.metric s).edist p y).toReal := ENNReal.toReal_nonneg
    nlinarith
  have htime : T ≤ K * T / K := by rw [mul_div_cancel_left₀ T hK.ne']
  obtain ⟨_, η, hη, hη0, hη1, hboundary, hηp, hsupport⟩ :=
    hcutoff StandardCapSpace T hT.le htime F p E hE hballs
      (fun s hs y _ => hRm s hs y)
  let C := max 0 (M04.shiCutoffThreshold c d L H T)
  refine ⟨E, hE, hp, C, le_max_left _ _, ?_⟩
  intro Q hcont hQ hspace hheat t ht
  have hestimate := M04.shi_cutoff_bound F.metric F.connection hE
    (S := T) (κ := 1) (c := c) (d := d) (L := L) (G := H) (Θ := T) (a := 0) (I := 0)
    hT (by norm_num) hc hd hL hH (by norm_num) (by norm_num) (by simp)
    Q η hcont hη hQ hη0 hη1 hboundary (fun _ _ => by simp) hspace
    (fun s hs y hy => by simpa only [one_mul] using! hheat s hs y (interior_subset hy))
    (by simpa only [M04.shiPhysicalCutoffSupports, one_mul] using hsupport)
  simpa only [zero_add, hηp t ht, mul_one, C] using hestimate t ht p hp

end PoincareConjecture.M35.Uniqueness
