import PoincareConjecture.Proofs.M47.JointSeedMetric
import PoincareConjecture.Proofs.M34.Mathlib.FirstExitOpen
import PoincareConjecture.Proofs.M34.Standard.MetricComparisonCompleteness
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CompactConfinement

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem jointSeed_ball_subset_of_local_tangent_lower
    (g h : RiemannianMetric n M) (q : M) {R r K : ℝ}
    (hR : 0 < R) (hK : 0 < K) (hscale : K * r ≤ R)
    (hbound : ∀ x ∈ closure (g.ball q R), ∀ w : TangentSpace (𝓡 n) x,
      g.tangentNorm x w ≤ K * h.tangentNorm x w) :
    h.ball q r ⊆ g.ball q R := by
  let : PseudoEMetricSpace M := g.comparisonPseudoEMetric
  have hopen : IsOpen (g.ball q R) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hq : q ∈ g.ball q R := by
    change edist q q < ENNReal.ofReal R
    simpa only [edist_self] using ENNReal.ofReal_pos.mpr hR
  intro y hy
  by_contra hyout
  obtain ⟨gamma, hzero, hone, hsmooth, hlength, _⟩ := h.exists_short_path_in_ball q y hy
  obtain ⟨t, ht, hfront, hbefore⟩ := hsmooth.continuousOn.exists_first_exit_open zero_le_one
    hopen (hzero.symm ▸ hq) (hone.symm ▸ hyout)
  have hclosure : MapsTo gamma (Icc (0 : ℝ) t) (closure (g.ball q R)) := by
    intro u hu
    rcases hu.2.eq_or_lt with rfl | hut
    · exact frontier_subset_closure hfront
    · exact subset_closure (hbefore u ⟨hu.1, hut⟩)
  have hcomparison := h.pathELength_le_of_tangentNorm_le g gamma 0 t K hK.le
    (fun u hu => hbound (gamma u) (hclosure hu))
  have hmono : h.pathELength gamma 0 t ≤ h.pathELength gamma 0 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨h.toRiemannianMetric⟩
    exact Manifold.pathELength_mono le_rfl ht.2
  have hdist : g.edist q (gamma t) ≤ g.pathELength gamma 0 t := by
    simpa only [hzero] using g.edist_le_pathELength_of_mem_Icc
      (hsmooth.mono (Icc_subset_Icc_right ht.2)) (show t ∈ Icc (0 : ℝ) t from ⟨ht.1.le, le_rfl⟩)
  have hstrict := ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hK).ne'
    ENNReal.ofReal_ne_top hlength
  rw [← ENNReal.ofReal_mul hK.le] at hstrict
  have hinside : gamma t ∈ g.ball q R :=
    ((hdist.trans hcomparison).trans (mul_le_mul_right hmono _)).trans_lt
      (hstrict.trans_le (ENNReal.ofReal_le_ofReal hscale))
  exact hfront.2 (hopen.interior_eq.symm ▸ hinside)

omit [T3Space M] in

theorem jointSeed_tangent_reverse_le_two
    (g h : RiemannianMetric n M) (x : M) (w : TangentSpace (𝓡 n) x)
    (hlower : Real.exp (-1 / 4 : ℝ) * g.inner x w w ≤ h.inner x w w) :
    g.tangentNorm x w ≤ 2 * h.tangentNorm x w := by
  have hg : 0 ≤ g.inner x w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact (g.pos x w hw).le
  have hh : 0 ≤ h.inner x w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact (h.pos x w hw).le
  have hexp : (1 / 4 : ℝ) ≤ Real.exp (-1 / 4 : ℝ) := by
    have h := Real.add_one_le_exp (-1 / 4 : ℝ)
    linarith
  have hquad : g.inner x w w ≤ 4 * h.inner x w w := by
    have h := mul_le_mul_of_nonneg_right hexp hg
    linarith
  change Real.sqrt (g.inner x w w) ≤ 2 * Real.sqrt (h.inner x w w)
  apply (Real.sqrt_le_iff).2
  exact ⟨by positivity, by nlinarith [Real.sq_sqrt hh]⟩

theorem jointSeed_seed_ball_inclusions
    (g h : RiemannianMetric n M) (q : M) {R : ℝ} (hR : 0 < R)
    (hupper : ∀ x : M, ∀ w : TangentSpace (𝓡 n) x, h.inner x w w ≤ g.inner x w w)
    (hlower : ∀ x ∈ closure (g.ball q R), ∀ w : TangentSpace (𝓡 n) x,
      Real.exp (-1 / 4 : ℝ) * g.inner x w w ≤ h.inner x w w) :
    g.ball q (R / 2) ⊆ h.ball q (R / 2) ∧ h.ball q (R / 2) ⊆ g.ball q R := by
  constructor
  · have h := g.ball_subset_ball_of_tangentNorm_le h q (R / 2) 1 zero_lt_one
      (fun x _hx w => by
        change Real.sqrt (h.inner x w w) ≤ 1 * Real.sqrt (g.inner x w w)
        simpa only [one_mul] using Real.sqrt_le_sqrt (hupper x w))
    simpa only [one_mul] using h
  · exact jointSeed_ball_subset_of_local_tangent_lower g h q hR (by norm_num : (0 : ℝ) < 2)
      (by linarith) (fun x hx w => jointSeed_tangent_reverse_le_two g h x w (hlower x hx w))

end PoincareConjecture.M47
