import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.CompactLocal
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace Poincare.CurvatureIntegral

variable {X : Type*} [MetricSpace X]


def HasLocalDistanceAscent (c : ℝ) (p y : X) : Prop :=
  ∀ s : ℝ, 0 < s → ∃ z : X,
    dist y z < s ∧ c * dist y z < dist p z - dist p y



def badAscentRadius (c b : ℝ) (p : X) : ℝ :=
  sSup (insert 0 ((fun y : X => dist p y) ''
    {y | 0 < dist p y ∧ dist p y ≤ b ∧ ¬ HasLocalDistanceAscent c p y}))

private theorem badAscentRadii_bddAbove (c b : ℝ) (p : X) :
    BddAbove (insert 0 ((fun y : X => dist p y) ''
      {y | 0 < dist p y ∧ dist p y ≤ b ∧ ¬ HasLocalDistanceAscent c p y})) := by
  refine ⟨max 0 b, ?_⟩
  rintro r (rfl | ⟨y, hy, rfl⟩)
  · exact le_max_left _ _
  · exact hy.2.1.trans (le_max_right _ _)

theorem badAscentRadius_nonneg (c b : ℝ) (p : X) :
    0 ≤ badAscentRadius c b p :=
  le_csSup (badAscentRadii_bddAbove c b p) (mem_insert _ _)

theorem badAscentRadius_le {c b : ℝ} (hb : 0 ≤ b) (p : X) :
    badAscentRadius c b p ≤ b := by
  apply csSup_le (insert_nonempty _ _)
  rintro r (rfl | ⟨y, hy, rfl⟩)
  · exact hb
  · exact hy.2.1

theorem dist_le_badAscentRadius {c b : ℝ} {p y : X}
    (hpos : 0 < dist p y) (hcap : dist p y ≤ b)
    (hbad : ¬ HasLocalDistanceAscent c p y) :
    dist p y ≤ badAscentRadius c b p :=
  le_csSup (badAscentRadii_bddAbove c b p)
    (mem_insert_of_mem _ ⟨y, ⟨hpos, hcap, hbad⟩, rfl⟩)



theorem hasLocalDistanceAscent_of_badAscentRadius_lt {c b : ℝ} {p y : X}
    (hinner : badAscentRadius c b p < dist p y) (houter : dist p y ≤ b) :
    HasLocalDistanceAscent c p y := by
  by_contra hbad
  exact (not_le_of_gt hinner) (dist_le_badAscentRadius
    ((badAscentRadius_nonneg c b p).trans_lt hinner) houter hbad)



theorem exists_bad_point_of_lt_badAscentRadius {c b r : ℝ} {p : X}
    (hr : 0 ≤ r) (hsmall : r < badAscentRadius c b p) :
    ∃ y : X, r < dist p y ∧ dist p y ≤ badAscentRadius c b p ∧
      dist p y ≤ b ∧ ¬ HasLocalDistanceAscent c p y := by
  obtain ⟨d, hd, hrd⟩ := exists_lt_of_lt_csSup (insert_nonempty _ _) hsmall
  rcases hd with rfl | ⟨y, hy, rfl⟩
  · exact False.elim ((not_lt_of_ge hr) hrd)
  · exact ⟨y, hrd, dist_le_badAscentRadius hy.1 hy.2.1 hy.2.2, hy.2.1, hy.2.2⟩

theorem badAscentRadius_le_of_annular_ascent {c b r : ℝ} {p : X}
    (hr : 0 ≤ r)
    (hascent : ∀ y : X, r < dist p y → dist p y ≤ b →
      HasLocalDistanceAscent c p y) :
    badAscentRadius c b p ≤ r := by
  apply csSup_le (insert_nonempty _ _)
  rintro d (rfl | ⟨y, hy, rfl⟩)
  · exact hr
  · by_contra! hlt
    exact hy.2.2 (hascent y hlt hy.2.1)

theorem badAscentRadius_eq_zero_iff (c b : ℝ) (p : X) :
    badAscentRadius c b p = 0 ↔
      ∀ y : X, 0 < dist p y → dist p y ≤ b → HasLocalDistanceAscent c p y := by
  constructor
  · intro h y hy hb
    apply hasLocalDistanceAscent_of_badAscentRadius_lt _ hb
    rwa [h]
  · intro h
    exact le_antisymm (badAscentRadius_le_of_annular_ascent (le_refl 0) h)
      (badAscentRadius_nonneg c b p)

end Poincare.CurvatureIntegral

namespace PoincareConjecture.RiemannianMetric

open Poincare.CurvatureIntegral

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_pos_le_badAscentRadius_of_pos_on_isCompact
    (g : RiemannianMetric n M) (hc : MetricComplete g) {c b : ℝ}
    (hc1 : c < 1) {K : Set M} (hK : IsCompact K) :
    letI := g.toMetricSpace
    ∃ r : ℝ, 0 < r ∧ ∀ p ∈ K,
      0 < badAscentRadius c b p → r ≤ badAscentRadius c b p := by
  let := g.toMetricSpace
  obtain ⟨r, hr, hbound⟩ :=
    g.exists_pos_le_truncatedInjectivityRadius_on_isCompact_of_complete hc
      (by norm_num : (0 : ℝ) < 1) hK
  refine ⟨r, hr, ?_⟩
  intro p hp hapos
  obtain ⟨y, hypos, hybound, _, hybad⟩ :=
    exists_bad_point_of_lt_badAscentRadius (le_refl (0 : ℝ)) hapos
  have hrle : r ≤ dist p y := by
    by_contra! hlt
    apply hybad
    exact g.exists_local_distance_ascent_of_lt_truncatedInjectivityRadius hc
      (by norm_num : (0 : ℝ) ≤ 1) hc1 p y hypos (hlt.trans_le (hbound p hp))
  exact hrle.trans hybound



theorem exists_near_min_badAscentRadius_on_isCompact
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    {c b : ℝ} (hc1 : c < 1) (hb : 0 < b)
    {K : Set M} (hK : IsCompact K) {p₀ : M} (hp₀ : p₀ ∈ K) :
    letI := g.toMetricSpace
    ∃ p ∈ K, badAscentRadius c b p ≤ badAscentRadius c b p₀ ∧
      ∀ q ∈ K, badAscentRadius c b p ≤ 2 * badAscentRadius c b q := by
  classical
  let := g.toMetricSpace
  by_cases hzero : ∃ p ∈ K, badAscentRadius c b p = 0
  · obtain ⟨p, hp, hzero⟩ := hzero
    refine ⟨p, hp, ?_, ?_⟩
    · rw [hzero]
      exact badAscentRadius_nonneg c b p₀
    · intro q _
      rw [hzero]
      positivity [badAscentRadius_nonneg c b q]
  obtain ⟨r, hr, hgap⟩ := g.exists_pos_le_badAscentRadius_of_pos_on_isCompact hc hc1 hK
  let V := badAscentRadius c b '' K
  have hV : V.Nonempty := ⟨_, p₀, hp₀, rfl⟩
  have hVbound : Bornology.IsBounded V := by
    apply (Metric.isBounded_Icc (0 : ℝ) b).subset
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨badAscentRadius_nonneg c b p, badAscentRadius_le hb.le p⟩
  have hinf : r ≤ sInf V := by
    apply le_csInf hV
    rintro _ ⟨p, hp, rfl⟩
    apply hgap p hp
    exact lt_of_le_of_ne (badAscentRadius_nonneg c b p)
      (fun h => hzero ⟨p, hp, h.symm⟩)
  have hinfpos : 0 < sInf V := hr.trans_le hinf
  obtain ⟨v, ⟨p, hp, rfl⟩, hpnear⟩ := exists_lt_of_csInf_lt hV
    (by linarith : sInf V < 2 * sInf V)
  have hbound (q : M) (hq : q ∈ K) : badAscentRadius c b p ≤ 2 * badAscentRadius c b q := by
    have h := csInf_le hVbound.bddBelow (show badAscentRadius c b q ∈ V from ⟨q, hq, rfl⟩)
    linarith
  by_cases hpp₀ : badAscentRadius c b p ≤ badAscentRadius c b p₀
  · exact ⟨p, hp, hpp₀, hbound⟩
  · exact ⟨p₀, hp₀, le_rfl, fun q hq => (le_of_not_ge hpp₀).trans (hbound q hq)⟩

end PoincareConjecture.RiemannianMetric
