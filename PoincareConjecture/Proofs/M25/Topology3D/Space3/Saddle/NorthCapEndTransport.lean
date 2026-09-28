import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ContainedNorthCapCommonCharts
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallCommonCap
import Mathlib.Topology.NhdsSet
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_north_cap_end_transport
    (A N : BallNeighborhoodChart E3 E3) (o : ℝ)
    (ho : 0 < o) (ho1 : o < 1)
    (hpatch : ∀ q : UnitTwoSphere, -o < (heightCoordinates (q : E3)).2 →
      N.chart (q : E3) ∈ A.boundary)
    (hcontain : N.closedRegion ⊆ A.closedRegion)
    (E B K : Set E3) (hK : IsClosed K)
    (hA : A.boundary = E ∪ N.chart ''
      {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2})
    (hN : N.boundary = B ∪ N.chart ''
      {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2})
    (hmeet : E ∩ N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} =
      B ∩ N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2})
    (havoid : A.closedRegion ∩ K ⊆ N.chart ''
      {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}) :
    let Delta := N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
    ∃ (G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) (C : Set E3),
      G '' E = B ∧ G.symm '' B = E ∧
      (∀ y ∈ Delta ∪ K, G y = y ∧ G.symm y = y) ∧
      IsCompact C ∧ C ⊆ (Delta ∪ K)ᶜ ∧
      tsupport (fun y => G y - y) ⊆ C ∧
      tsupport (fun y => G.symm y - y) ⊆ C := by
  classical
  let Da : Set E3 := {y | ‖y‖ = 1 ∧ (3 / 4 : ℝ) ≤ (heightCoordinates y).2}
  let Delta := N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
  change A.boundary = E ∪ Delta at hA
  change N.boundary = B ∪ Delta at hN
  change E ∩ Delta = B ∩ Delta at hmeet
  change A.closedRegion ∩ K ⊆ Delta at havoid
  obtain ⟨G0, G1, F, Ahat, Nhat, V, hnorm, hFs, hFo, hFc,
      hAch, hNch, hAs, hNs, hAt, hNt, hpoint, hinv,
      hAi, hAc, hAb, hNi, hNc, hNb, hAD, hND,
      hV, hDV, hVs, hEq⟩ :=
    exists_contained_north_cap_common_charts A N o ho ho1 hpatch hcontain
  change Ahat.chart '' Da = Delta at hAD
  change Nhat.chart '' Da = Delta at hND
  change Da ⊆ V at hDV
  let v : E3 := heightCoordinates.symm (0, 1)
  have hv : ‖v‖ = 1 := by
    have hh := heightCoordinates_symm_norm_sq ((0 : E2), (1 : ℝ))
    change ‖v‖ ^ 2 = ‖(0 : E2)‖ ^ 2 + (1 : ℝ) ^ 2 at hh
    simp only [norm_zero, one_pow] at hh
    nlinarith [norm_nonneg v]
  have hvh (y : E3) : ⟪v, y⟫_ℝ = (heightCoordinates y).2 := by
    simp only [v, heightCoordinates_symm_apply,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      Fin.sum_univ_three, heightCoordinates_snd_apply]
    simp
  have hD : {y : E3 | ‖y‖ = 1 ∧ (3 / 4 : ℝ) ≤ ⟪v, y⟫_ℝ} = Da := by
    ext y
    simp only [mem_ofPred_eq, hvh, Da]
  have hcommon : ∀ᶠ y in 𝓝ˢ
      {y : E3 | ‖y‖ = 1 ∧ (3 / 4 : ℝ) ≤ ⟪v, y⟫_ℝ},
      Ahat.chart y = Nhat.chart y := by
    rw [hD]
    exact eventually_nhdsSet_iff_exists.mpr ⟨V, hV, hDV, hEq⟩
  have hcap : Ahat.chart ''
      {y : E3 | ‖y‖ = 1 ∧ (3 / 4 : ℝ) ≤ ⟪v, y⟫_ℝ} = Delta := by
    rw [hD]
    exact hAD
  have hAO : Ahat.closedRegion \ (Ahat.chart ''
      {y : E3 | ‖y‖ = 1 ∧ (3 / 4 : ℝ) ≤ ⟪v, y⟫_ℝ}) ⊆ Kᶜ := by
    rw [hAc, hcap]
    intro y hy hyK
    exact hy.2 (havoid ⟨hy.1, hyK⟩)
  have hNO : Nhat.closedRegion \ (Ahat.chart ''
      {y : E3 | ‖y‖ = 1 ∧ (3 / 4 : ℝ) ≤ ⟪v, y⟫_ℝ}) ⊆ Kᶜ := by
    rw [hNc, hcap]
    intro y hy hyK
    exact hy.2 (havoid ⟨hcontain hy.1, hyK⟩)
  obtain ⟨G, hball, hGi, hGc, hGb, hfix, C, hC, hCs, hfar⟩ :=
    exists_ball_transport_of_common_cap_germ Ahat Nhat v hv
      (3 / 4 : ℝ) (by norm_num) hcommon hK.isOpen_compl hAO hNO
  rw [hAb, hNb] at hGb
  rw [hcap] at hfix hCs
  have hCs' : C ⊆ (Delta ∪ K)ᶜ := by
    intro y hy
    rcases hCs hy with ⟨hyK, hyD⟩
    exact fun hh => hh.elim hyD hyK
  have hfixed (y : E3) (hy : y ∈ Delta ∪ K) : G y = y ∧ G.symm y = y := by
    have hyC : y ∉ C := fun hh => hCs' hh hy
    have hg : G y = y := hfar y hyC
    exact ⟨hg, equiv_symm_fixed_of_fixed G.toEquiv hg⟩
  have hforward : G '' E = B := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxA : x ∈ A.boundary := by
        rw [hA]
        exact Or.inl hx
      have hg : G x ∈ N.boundary := hGb ▸ ⟨x, hxA, rfl⟩
      rw [hN] at hg
      rcases hg with hg | hg
      · exact hg
      · have hxx : G x = x := by
          have hgg : G (G x) = G x := hfix _ hg
          exact G.injective hgg
        have hxD : x ∈ Delta := hxx ▸ hg
        have hxB : x ∈ B := (hmeet.subset ⟨hx, hxD⟩).1
        simpa only [hxx] using hxB
    · intro hy
      have hyN : y ∈ N.boundary := by
        rw [hN]
        exact Or.inl hy
      rw [← hGb] at hyN
      obtain ⟨x, hx, hxy⟩ := hyN
      rw [hA] at hx
      rcases hx with hx | hx
      · exact ⟨x, hx, hxy⟩
      · have hxy' : x = y := (hfix x hx).symm.trans hxy
        have hyD : y ∈ Delta := hxy' ▸ hx
        have hyE : y ∈ E := (hmeet.superset ⟨hy, hyD⟩).1
        exact ⟨y, hyE, hfix y hyD⟩
  have hreverse : G.symm '' B = E := by
    rw [← hforward, image_image]
    simp only [G.symm_apply_apply, image_id']
  refine ⟨G, C, hforward, hreverse, hfixed, hC, hCs', ?_, ?_⟩
  · apply closure_minimal ?_ hC.isClosed
    intro y hy
    by_contra hyC
    exact hy (sub_eq_zero.mpr (hfar y hyC))
  · apply closure_minimal ?_ hC.isClosed
    intro y hy
    by_contra hyC
    exact hy (sub_eq_zero.mpr (equiv_symm_fixed_of_fixed G.toEquiv (hfar y hyC)))

end PoincareConjecture.M25.Topology3D
