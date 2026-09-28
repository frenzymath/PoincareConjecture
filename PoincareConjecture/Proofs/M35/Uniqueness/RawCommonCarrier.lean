import PoincareConjecture.Proofs.M35.Uniqueness.RawDistanceExhaustion
import PoincareConjecture.Proofs.M35.Uniqueness.RawDistanceContinuity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold Bundle ENNReal

namespace PoincareConjecture.M35.Uniqueness

theorem exists_raw_common_ball_carrier
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T R : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hR : 0 < R)
    {C : Set StandardCapSpace} (hC : IsCompact C) :
    ∃ E : Set StandardCapSpace, IsCompact E ∧ C ⊆ interior E ∧
      ∀ t ∈ Icc 0 T, ∀ p ∈ C, closure ((G.flow.metric t).ball p R) ⊆ E := by
  let o : StandardCapSpace := 0
  have hc : ContinuousOn (fun z : ℝ × StandardCapSpace =>
      ((G.flow.metric z.1).edist o z.2).toReal) (Icc 0 T ×ˢ C) :=
    (continuousOn_raw_distance G hT hTlt o).mono (prod_mono Subset.rfl (subset_univ C))
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc.prod hC).exists_bound_of_continuousOn hc
  let B := max 0 B₀
  have hB : 0 ≤ B := le_max_left _ _
  have hcenter (t : ℝ) (ht : t ∈ Icc 0 T) (p : StandardCapSpace) (hp : p ∈ C) :
      ((G.flow.metric t).edist o p).toReal ≤ B :=
    (le_abs_self _).trans ((hB₀ (t, p) ⟨ht, hp⟩).trans (le_max_right _ _))
  obtain ⟨E, hE, _, hexhaust⟩ := exists_raw_distance_square_compact_exhaustion
    P G hT.le hTlt o o (A := (B + R) ^ 2 + 2) (by positivity)
  have hballs (t : ℝ) (ht : t ∈ Icc 0 T) (p : StandardCapSpace) (hp : p ∈ C) :
      (G.flow.metric t).ball p R ⊆ E := by
    intro y hy
    by_contra hn
    have hlarge := hexhaust t ht y (fun h => hn (interior_subset h))
    have hsmall : ((G.flow.metric t).edist p y).toReal < R := by
      have hh := (ENNReal.toReal_lt_toReal ((G.flow.metric t).edist_ne_top p y)
        ENNReal.ofReal_ne_top).mpr hy
      simpa only [ENNReal.toReal_ofReal hR.le] using hh
    have htri : (G.flow.metric t).edist o y ≤
        (G.flow.metric t).edist o p + (G.flow.metric t).edist p y := by
      let : Bundle.RiemannianBundle
          (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
        ⟨(G.flow.metric t).toRiemannianMetric⟩
      exact Manifold.riemannianEDist_triangle
    have htr := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨(G.flow.metric t).edist_ne_top o p,
        (G.flow.metric t).edist_ne_top p y⟩) htri
    rw [ENNReal.toReal_add ((G.flow.metric t).edist_ne_top o p)
      ((G.flow.metric t).edist_ne_top p y)] at htr
    have hdist : 0 ≤ ((G.flow.metric t).edist o y).toReal := ENNReal.toReal_nonneg
    have hupper : ((G.flow.metric t).edist o y).toReal < B + R :=
      htr.trans_lt (add_lt_add_of_le_of_lt (hcenter t ht p hp) hsmall)
    change (B + R) ^ 2 + 2 ≤ 1 + ((G.flow.metric t).edist o y).toReal ^ 2 at hlarge
    have hsquare := (sq_le_sq₀ hdist (add_nonneg hB hR.le)).mpr hupper.le
    linarith only [hlarge, hsquare]
  refine ⟨E, hE, ?_, fun t ht p hp => closure_minimal (hballs t ht p hp) hE.isClosed⟩
  intro p hp
  have hpball : p ∈ (G.flow.metric 0).ball p R := by
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
      ⟨(G.flow.metric 0).toRiemannianMetric⟩
    change (G.flow.metric 0).edist p p < ENNReal.ofReal R
    have hz : (G.flow.metric 0).edist p p = 0 := Manifold.riemannianEDist_self
    rw [hz]
    exact ENNReal.ofReal_pos.mpr hR
  have hopen : IsOpen ((G.flow.metric 0).ball p R) :=
    M04.initial_ball_isOpen (G.flow.metric 0) p R
  exact (hopen.subset_interior_iff.mpr (hballs 0 ⟨le_rfl, hT.le⟩ p hp)) hpball

end PoincareConjecture.M35.Uniqueness
