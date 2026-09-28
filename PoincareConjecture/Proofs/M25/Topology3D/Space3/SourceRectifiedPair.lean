import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceSignedDiscs
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceCollarRectification
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceCollarReflection

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

structure RectifiedSourceDiscPair
    (Q : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere) (d k : ℝ) where
  positive : OpenPartialHomeomorph E2 UnitTwoSphere
  negative : OpenPartialHomeomorph E2 UnitTwoSphere
  positive_source : closedBall 0 1 ⊆ positive.source
  negative_source : closedBall 0 1 ⊆ negative.source
  positive_smooth : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ positive positive.source
  positive_inverse : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ positive.symm positive.target
  negative_smooth : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ negative negative.source
  negative_inverse : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ negative.symm negative.target
  positive_boundary : ∀ θ : UnitCircle, positive θ.1 = Q (θ, 0)
  negative_boundary : ∀ θ : UnitCircle, negative θ.1 = Q (θ, 0)
  closed_cover : (positive '' closedBall 0 1) ∪ (negative '' closedBall 0 1) = univ
  closed_inter : (positive '' closedBall 0 1) ∩ (negative '' closedBall 0 1) =
    range (fun θ : UnitCircle => Q (θ, 0))
  open_disjoint : Disjoint (positive '' ball 0 1) (negative '' ball 0 1)
  open_cover : (positive '' ball 0 1) ∪ (negative '' ball 0 1) =
    (range (fun θ : UnitCircle => Q (θ, 0)))ᶜ
  positive_side : Q '' (univ ×ˢ Ioo 0 d) ⊆ positive '' ball 0 1
  negative_side : Q '' (univ ×ˢ Ioo (-d) 0) ⊆ negative '' ball 0 1
  positive_near : ∀ᶠ x in 𝓝ˢ (sphere (0 : E2) 1),
    x ∈ positive.source ∧ positive x = Q (circleDirection x, k * (1 - ‖x‖))
  negative_near : ∀ᶠ x in 𝓝ˢ (sphere (0 : E2) 1),
    x ∈ negative.source ∧ negative x = Q (circleDirection x, -(k * (1 - ‖x‖)))

theorem exists_rectified_source_disc_pair (hP : PlanarSchoenfliesService)
    (Q : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere)
    (hQ : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ Q Q.source)
    (hQi : ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ Q.symm Q.target)
    {d : ℝ} (hd : 0 < d) (hQs : Q.source = univ ×ˢ Ioo (-d) d)
    (v : UnitTwoSphere) (hv : v ∉ range (fun θ : UnitCircle => Q (θ, 0)))
    {k : ℝ} (hk : 0 < k) : Nonempty (RectifiedSourceDiscPair Q d k) := by
  obtain ⟨e, f, hes, hfs, hem, hei, hfm, hfi, heb, hfb, hu, hi, hdis, ho, hpos, hneg⟩ :=
    source_sphere_signed_discs_of_planar hP Q hQ hQi hd hQs v hv
  obtain ⟨e', hes', hem', hei', heo, hec, heb', hen⟩ :=
    exists_rectified_source_disc_chart Q hQ hQi hd hQs e hes hem hei heb
      (source_disc_nonpositive_exterior Q e f hes heb hdis hneg) hk
  obtain ⟨N, hNs, hNm, hNi, hN⟩ := exists_reflected_source_collar Q hQ hQi d hQs
  have hfbN (θ : UnitCircle) : f θ.1 = N (θ, 0) := by
    rw [hN]
    simpa only [neg_zero] using hfb θ
  have hnegN : N '' (univ ×ˢ Ioo (-d) 0) ⊆ e '' ball 0 1 := by
    rintro _ ⟨⟨θ, s⟩, ⟨_, hs⟩, rfl⟩
    rw [hN]
    exact hpos ⟨(θ, -s), ⟨mem_univ _, by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩
  obtain ⟨f', hfs', hfm', hfi', hfo, hfc, hfb', hfn⟩ :=
    exists_rectified_source_disc_chart N hNm hNi hd hNs f hfs hfm hfi hfbN
      (source_disc_nonpositive_exterior N f e hfs hfbN hdis.symm hnegN) hk
  refine ⟨{
    positive := e'
    negative := f'
    positive_source := hes'
    negative_source := hfs'
    positive_smooth := hem'
    positive_inverse := hei'
    negative_smooth := hfm'
    negative_inverse := hfi'
    positive_boundary := heb'
    negative_boundary := ?_
    closed_cover := ?_
    closed_inter := ?_
    open_disjoint := ?_
    open_cover := ?_
    positive_side := ?_
    negative_side := ?_
    positive_near := hen
    negative_near := ?_ }⟩
  · intro θ
    rw [hfb', hN]
    simp only [neg_zero]
  · rwa [hec, hfc]
  · rwa [hec, hfc]
  · rwa [heo, hfo]
  · rwa [heo, hfo]
  · rwa [heo]
  · rwa [hfo]
  · filter_upwards [hfn] with x hx
    exact ⟨hx.1, hx.2.trans (hN _)⟩

end PoincareConjecture.M25.Topology3D
