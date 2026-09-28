import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceDiscNormalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceDiscComplement













set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

attribute [local instance] space3_stereographic_dimension



theorem source_sphere_two_discs_of_planar (hP : PlanarSchoenfliesService)
    (q : UnitCircle → UnitTwoSphere) (hq : ContMDiff (𝓡 1) (𝓡 2) ∞ q)
    (hqi : Injective q) (hqd : ∀ θ, Injective (mfderiv (𝓡 1) (𝓡 2) q θ))
    (v : UnitTwoSphere) (hv : v ∉ range q) :
    ∃ e f : OpenPartialHomeomorph E2 UnitTwoSphere,
      closedBall 0 1 ⊆ e.source ∧ closedBall 0 1 ⊆ f.source ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ f f.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ f.symm f.target ∧
      (∀ θ : UnitCircle, e θ.1 = q θ) ∧
      e '' sphere 0 1 = range q ∧ f '' sphere 0 1 = range q ∧
      (e '' closedBall 0 1) ∪ (f '' closedBall 0 1) = univ ∧
      (e '' closedBall 0 1) ∩ (f '' closedBall 0 1) = range q ∧
      Disjoint (e '' ball 0 1) (f '' ball 0 1) ∧
      (e '' ball 0 1) ∪ (f '' ball 0 1) = (range q)ᶜ := by
  obtain ⟨D, e, he, hes, hem, hei, heb⟩ :=
    exists_source_circle_disc_chart hP q hq hqi hqd v hv
  obtain ⟨r, hr, _, G, hG⟩ := sourceDisc_round_of_planarData D v
  have hGe : G '' (e '' closedBall 0 1) = (stereographic' 2 v).symm '' closedBall 0 r := by
    rwa [he]
  obtain ⟨f, hfs, hfm, hfi, hu, hi, hb, hd, ho⟩ :=
    exists_source_disc_complement e hes G v hr hGe
  have heboundary : e '' sphere 0 1 = range q := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (heb ⟨x, hx⟩).symm⟩
    · rintro ⟨θ, rfl⟩
      exact ⟨θ.1, θ.2, heb θ⟩
  refine ⟨e, f, hes, ?_, hem, hei, hfm.contMDiffOn, hfi, heb,
    heboundary, hb.trans heboundary, hu, hi.trans heboundary, hd, ?_⟩
  · rw [hfs]
    exact subset_univ _
  · rwa [heboundary] at ho

end PoincareConjecture.M25.Topology3D
