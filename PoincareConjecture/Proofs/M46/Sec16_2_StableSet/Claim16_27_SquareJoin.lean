import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CornerRecovery
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

theorem squareCurveDensity_germ_eq {gamma beta : ℝ → G.Point} {A B : Set ℝ} {s : ℝ}
    (hA : A ∈ 𝓝 s) (hB : B ∈ 𝓝 s) (h : gamma =ᶠ[𝓝 s] beta) :
    M14.squareCurveDensity G gamma A s = M14.squareCurveDensity G beta B s := by
  unfold M14.squareCurveDensity M14.projectedCurveVelocityWithin
  rw [mfderivWithin_of_mem_nhds hA, mfderivWithin_of_mem_nhds hB,
    h.mfderiv_eq, h.eq_of_nhds]

theorem exists_oneCorner_square_join {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (alpha beta : ℝ → G.Point)
    (halpha : ContMDiffOn 𝓘(ℝ, ℝ) (spacetimeModel 3) 1 alpha (Icc a c))
    (hbeta : ContMDiffOn 𝓘(ℝ, ℝ) (spacetimeModel 3) 1 beta (Icc c b))
    (hjoin : alpha c = beta c) :
    ∃ gamma : ℝ → G.Point, Continuous gamma ∧
      EqOn gamma alpha (Icc a c) ∧ EqOn gamma beta (Icc c b) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (spacetimeModel 3) 1 gamma (Icc a c) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (spacetimeModel 3) 1 gamma (Icc c b) := by
  classical
  let g := (Iic c).piecewise alpha beta
  have hgl (s : ℝ) (hs : s ≤ c) : g s = alpha s := piecewise_eq_of_mem _ _ _ hs
  have hgr (s : ℝ) (hs : c ≤ s) : g s = beta s := by
    by_cases hsc : s ≤ c
    · have heq := le_antisymm hsc hs
      rw [heq, hgl c le_rfl, hjoin]
    · exact piecewise_eq_of_notMem _ _ _ hsc
  have hg : ContinuousOn g (Icc a b) := by
    apply ContinuousOn.piecewise
    · intro s hs
      have hsc : s = c := by simpa only [frontier_Iic, mem_singleton_iff] using hs.2
      simpa only [hsc] using hjoin
    · apply halpha.continuousOn.mono
      intro s hs
      exact ⟨hs.1.1, by simpa only [closure_Iic, mem_Iic] using hs.2⟩
    · apply hbeta.continuousOn.mono
      intro s hs
      exact ⟨by simpa only [compl_Iic, closure_Ioi, mem_Ici] using hs.2, hs.1.2⟩
  let gamma s := g (projIcc a b (hac.trans hcb) s).val
  have hgamma : Continuous gamma := hg.domRestrict.comp continuous_projIcc
  have heq (s : ℝ) (hs : s ∈ Icc a b) : gamma s = g s := by
    simp only [gamma, projIcc_of_mem _ hs]
  have hleft : EqOn gamma alpha (Icc a c) := fun s hs =>
    (heq s ⟨hs.1, hs.2.trans hcb⟩).trans (hgl s hs.2)
  have hright : EqOn gamma beta (Icc c b) := fun s hs =>
    (heq s ⟨hac.trans hs.1, hs.2⟩).trans (hgr s hs.1)
  exact ⟨gamma, hgamma, hleft, hright,
    halpha.congr (fun _ hs => hleft hs), hbeta.congr (fun _ hs => hright hs)⟩

end PoincareConjecture.Proofs.M46
