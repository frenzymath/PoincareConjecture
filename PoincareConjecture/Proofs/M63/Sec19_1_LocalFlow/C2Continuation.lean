import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ArbitraryC2IntrinsicRegularity
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.BoundedCurvatureC2Endpoint
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2AdjacentIntervals
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.IntrinsicC2LocalExistence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem c2ShrinkingCurve_continuation
    [T2Space M] (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Ico a T))
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Ico a T, ∀ x, m62Curvature F c t x ≤ K) :
    ∃ T' : ℝ, T ≤ T' ∧ T' ≤ b ∧ (T < b → T < T') ∧
      ∃ d : ℝ → ℝ → M, M63C2ShrinkingCurveOn F d (Icc a T') ∧
        ∀ t ∈ Ico a T, ∀ x, d x t = c x t := by
  classical
  have hi := c2ShrinkingCurve_intrinsic_regularity F hcompact haT hTb (Or.inr rfl) hc
  obtain ⟨cbar, hcbar, hbar⟩ :=
    exists_closed_c2_endpoint_of_intrinsic_bounded_curvature F hcompact haT hTb hc hi hK hcurv
  by_cases hTb' : T < b
  · let : CompactSpace M := isCompact_univ_iff.mp hcompact
    let : Nonempty M := ⟨c 0 a⟩
    let FS := m63RestrictClosedFlow F T b (Icc_subset_Icc_left haT.le) hTb'
    have hT : T ∈ Icc a T := ⟨haT.le, le_rfl⟩
    obtain ⟨T', hTT', hT'b, q, hq, hqinitial, _hqi⟩ :=
      exists_intrinsic_c2_local_curve FS (fun x => cbar x T)
        (hcbar.periodic T hT) (hcbar.spatial_regular T hT) (hcbar.immersed T hT)
    have hqF : M63C2ShrinkingCurveOn F q (Icc T T') :=
      { domain_subset := fun t ht => ⟨haT.le.trans ht.1, ht.2.trans hT'b.le⟩
        periodic := hq.periodic
        spatial_regular := hq.spatial_regular
        joint_c1 := hq.joint_c1
        immersed := hq.immersed
        continuous := hq.continuous
        velocity_continuous := hq.velocity_continuous
        curvature_continuous := hq.curvature_continuous
        equation := hq.equation }
    let d : ℝ → ℝ → M := fun x t => if t ≤ T then cbar x t else q x t
    have hleft : M63C2ShrinkingCurveOn F d (Icc a T) :=
      c2_congr hcbar (fun t ht x => by simp only [d, if_pos ht.2])
    have hright : M63C2ShrinkingCurveOn F d (Icc T T') := by
      apply c2_congr hqF
      intro t ht x
      by_cases htT : t ≤ T
      · have htEq : t = T := le_antisymm htT ht.1
        subst t
        simpa only [d, if_pos le_rfl] using (hqinitial x).symm
      · simp only [d, if_neg htT]
    obtain ⟨N, e, he, hemb, hinj⟩ :=
      exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
    obtain ⟨U, ρ, hU, heU, hρ, hρe, _hmin, _huniq⟩ :=
      exists_smooth_compact_embedded_retraction e hemb he hinj
    refine ⟨T', hTT'.le, hT'b.le, fun _ => hTT', d,
      c2_of_adjacent_closed_intervals F haT hTT' he hU heU hρ hρe hleft hright, ?_⟩
    intro t ht x
    simpa only [d, if_pos ht.2.le] using hbar t ht x
  · exact ⟨T, le_rfl, hTb, fun h => (hTb' h).elim, cbar, hcbar, hbar⟩

end PoincareConjecture.M63
