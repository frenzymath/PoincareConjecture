import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceDiscSides
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceCircleChart

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem source_sphere_signed_discs_of_planar (hP : PlanarSchoenfliesService)
    (Q : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere)
    (hQ : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ Q Q.source)
    (hQi : ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ Q.symm Q.target)
    {d : ℝ} (hd : 0 < d) (hQs : Q.source = univ ×ˢ Ioo (-d) d)
    (v : UnitTwoSphere) (hv : v ∉ range (fun θ : UnitCircle => Q (θ, 0))) :
    ∃ e f : OpenPartialHomeomorph E2 UnitTwoSphere,
      closedBall 0 1 ⊆ e.source ∧ closedBall 0 1 ⊆ f.source ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ f f.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ f.symm f.target ∧
      (∀ θ : UnitCircle, e θ.1 = Q (θ, 0)) ∧
      (∀ θ : UnitCircle, f θ.1 = Q (θ, 0)) ∧
      (e '' closedBall 0 1) ∪ (f '' closedBall 0 1) = univ ∧
      (e '' closedBall 0 1) ∩ (f '' closedBall 0 1) =
        range (fun θ : UnitCircle => Q (θ, 0)) ∧
      Disjoint (e '' ball 0 1) (f '' ball 0 1) ∧
      (e '' ball 0 1) ∪ (f '' ball 0 1) =
        (range (fun θ : UnitCircle => Q (θ, 0)))ᶜ ∧
      Q '' (univ ×ˢ Ioo 0 d) ⊆ e '' ball 0 1 ∧
      Q '' (univ ×ˢ Ioo (-d) 0) ⊆ f '' ball 0 1 := by
  have hzero (θ : UnitCircle) : (θ, (0 : ℝ)) ∈ Q.source := by
    rw [hQs]
    exact ⟨mem_univ _, neg_neg_of_pos hd, hd⟩
  obtain ⟨hqm, hqi, hqd⟩ := source_collar_slice_smooth_immersion Q hQ hQi 0 hzero
  obtain ⟨e, f, hes, hfs, hem, hei, hfm, hfi, heb, hfb, hu, hi, hdis, hcover⟩ :=
    source_sphere_two_parametrized_discs_of_planar hP _ hqm hqi hqd v hv
  rcases source_disc_collar_halves Q hd hQs e f hes hfs _ (fun _ => rfl)
    heb hfb hdis hcover with hs | hs
  · refine ⟨f, e, hfs, hes, hfm, hfi, hem, hei, hfb, heb, ?_, ?_, hdis.symm, ?_,
      hs.2, hs.1⟩
    · simpa only [union_comm] using hu
    · simpa only [inter_comm] using hi
    · simpa only [union_comm] using hcover
  · exact ⟨e, f, hes, hfs, hem, hei, hfm, hfi, heb, hfb, hu, hi, hdis, hcover,
      hs.2, hs.1⟩

theorem source_disc_nonpositive_exterior
    (Q : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere)
    (e f : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : closedBall 0 1 ⊆ e.source)
    (hb : ∀ θ : UnitCircle, e θ.1 = Q (θ, 0))
    (hdis : Disjoint (e '' ball 0 1) (f '' ball 0 1))
    {d : ℝ} (hneg : Q '' (univ ×ˢ Ioo (-d) 0) ⊆ f '' ball 0 1)
    (θ : UnitCircle) (s : ℝ) (hs : s ∈ Ioo (-d) d) (hs0 : s ≤ 0) :
    Q (θ, s) ∉ e '' ball 0 1 := by
  intro hmem
  rcases lt_or_eq_of_le hs0 with hlt | rfl
  · exact Set.disjoint_left.mp hdis hmem
      (hneg ⟨(θ, s), ⟨mem_univ _, hs.1, hlt⟩, rfl⟩)
  · obtain ⟨x, hx, hxe⟩ := hmem
    have heq := e.injOn (he (ball_subset_closedBall hx))
      (he (sphere_subset_closedBall θ.2)) (hxe.trans (hb θ).symm)
    have hn := mem_ball_zero_iff.mp hx
    rw [heq, norm_eq_of_mem_sphere θ] at hn
    exact lt_irrefl 1 hn

end PoincareConjecture.M25.Topology3D
