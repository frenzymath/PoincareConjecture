import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.SphereCircle.Projection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.DiskComplement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BallImages
import Mathlib.Analysis.Normed.Module.Ball.Pointwise











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function IsManifold
open scoped Manifold ContDiff Pointwise

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

private theorem normalize_disk_neighborhood
    {R : Real} (hR : 0 < R) (e : OpenPartialHomeomorph E2 S2)
    (hsource : closedBall 0 R ⊆ e.source)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target) :
    ∃ d : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      d '' closedBall 0 1 = e '' closedBall 0 R := by
  let L : E2 ≃L[Real] E2 :=
    (LinearEquiv.smulOfNeZero Real E2 R hR.ne').toContinuousLinearEquiv
  have hL : L '' closedBall (0 : E2) 1 = closedBall 0 R := by
    change (fun x : E2 => R • x) '' closedBall 0 1 = _
    rw [image_smul, _root_.smul_closedBall' hR.ne', smul_zero, Real.norm_eq_abs,
      abs_of_pos hR, mul_one]
  let d := L.toHomeomorph.toOpenPartialHomeomorph.trans e
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨mem_univ _, hsource (hL ▸ mem_image_of_mem L hx)⟩
  · exact he.comp L.contDiff.contMDiff.contMDiffOn (fun _ hx => hx.2)
  · exact L.symm.contDiff.contMDiff.comp_contMDiffOn
      (hei.mono (fun _ hx => hx.1))
  · change (e ∘ L) '' closedBall 0 1 = _
    rw [image_comp, hL]

private theorem closure_image_unit_disk
    (e : OpenPartialHomeomorph E2 S2) (hs : closedBall 0 1 ⊆ e.source) :
    closure (e '' ball 0 1) = e '' closedBall 0 1 := by
  have hK : IsCompact (e '' closedBall 0 1) :=
    (isCompact_closedBall 0 1).image_of_continuousOn (e.continuousOn.mono hs)
  apply Subset.antisymm (closure_minimal (image_mono ball_subset_closedBall) hK.isClosed)
  have hcont : ContinuousOn e (closure (ball (0 : E2) 1)) := by
    rw [closure_ball _ (by norm_num : (1 : Real) ≠ 0)]
    exact e.continuousOn.mono hs
  simpa only [closure_ball _ (by norm_num : (1 : Real) ≠ 0)] using hcont.image_closure





theorem exists_sphere_disk_neighborhoods_of_stereographic_boundary
    {f : S1 -> S2} {p : S2} (hp : p ∉ range f)
    (A : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hboundary : A '' sphere (0 : E2) 1 = range (stereographic' 2 p ∘ f)) :
    ∃ e₀ e₁ : OpenPartialHomeomorph E2 S2,
      (∀ x, e₀ x = (stereographic' 2 p).symm (A x)) ∧
      closedBall 0 1 ⊆ e₀.source ∧ closedBall 0 1 ⊆ e₁.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e₀ e₀.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e₀.symm e₀.target ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e₁ e₁.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e₁.symm e₁.target ∧
      e₀ '' sphere (0 : E2) 1 = range f ∧
      e₁ '' sphere (0 : E2) 1 = range f ∧
      e₁ '' closedBall 0 1 = (e₀ '' ball 0 1)ᶜ ∧
      Disjoint (e₀ '' ball 0 1) (e₁ '' ball 0 1) ∧
      e₀ '' closedBall 0 1 ∪ e₁ '' closedBall 0 1 = univ ∧
      e₀ '' closedBall 0 1 ∩ e₁ '' closedBall 0 1 = range f := by
  let s := stereographic' 2 p
  have hs : s ∈ maximalAtlas (𝓡 2) ∞ S2 :=
    IsManifold.subset_maximalAtlas ⟨p, rfl⟩
  have hsi : ContMDiff (𝓡 2) (𝓡 2) ∞ s.symm := by
    rw [← contMDiffOn_univ]
    simpa only [s, stereographic'_target] using contMDiffOn_symm_of_mem_maximalAtlas hs
  let e₀ := A.toHomeomorph.toOpenPartialHomeomorph.trans s.symm
  have hs₀ : e₀.source = univ := by
    simp [e₀, s, stereographic'_target]
  have hclosed₀ : closedBall (0 : E2) 1 ⊆ e₀.source := by rw [hs₀]; exact subset_univ _
  have he₀ : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e₀ e₀.source :=
    (hsi.comp A.contMDiff).contMDiffOn
  have hei₀ : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e₀.symm e₀.target :=
    A.symm.contMDiff.comp_contMDiffOn
      ((contMDiffOn_of_mem_maximalAtlas hs).mono (fun _ hx => hx.1))
  have hloc (x : E2) : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ e₀ x := by
    let d : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ :=
      { toPartialEquiv := e₀.toPartialEquiv
        open_source := e₀.open_source
        open_target := e₀.open_target
        contMDiffOn_toFun := he₀
        contMDiffOn_invFun := hei₀ }
    exact d.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ (by change x ∈ e₀.source; rw [hs₀]; trivial)
  have hboundary₀ : e₀ '' sphere (0 : E2) 1 = range f := by
    change (s.symm ∘ A) '' sphere (0 : E2) 1 = _
    rw [image_comp, hboundary, ← range_comp]
    apply congrArg range
    funext q
    apply s.left_inv
    rw [stereographic'_source]
    exact fun heq => hp ⟨q, heq⟩
  obtain ⟨R, e, hR, hse, he, hei, hcomp⟩ :=
    exists_complementary_disk_neighborhood (by norm_num : (0 : Real) < 1) e₀
      (e₀.injOn.mono hclosed₀) (fun x _ => hloc x)
  obtain ⟨e₁, hclosed₁, he₁, hei₁, hnorm⟩ := normalize_disk_neighborhood hR e hse he hei
  have hcomp₁ : e₁ '' closedBall 0 1 = (e₀ '' ball 0 1)ᶜ := hnorm.trans hcomp
  have hcl₀ := closure_image_unit_disk e₀ hclosed₀
  have hinner₀ := e₀.image_ball_eq_interior hclosed₀ rfl
  have hinner₁ := e₁.image_ball_eq_interior hclosed₁ rfl
  have hfront₀ := e₀.image_sphere_eq_frontier hclosed₀ rfl
  have hfront₁ := e₁.image_sphere_eq_frontier hclosed₁ rfl
  have hopen₀ : IsOpen (e₀ '' ball 0 1) :=
    e₀.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hclosed₀)
  have hK₀ : IsClosed (e₀ '' closedBall 0 1) :=
    ((isCompact_closedBall 0 1).image_of_continuousOn (e₀.continuousOn.mono hclosed₀)).isClosed
  have hfrontOpen₀ : frontier (e₀ '' ball 0 1) = range f := by
    rw [hopen₀.frontier_eq, hcl₀, hinner₀, ← hK₀.frontier_eq, ← hfront₀, hboundary₀]
  have hboundary₁ : e₁ '' sphere (0 : E2) 1 = range f := by
    rw [hfront₁, hcomp₁, frontier_compl, hfrontOpen₀]
  have hopen₁ : e₁ '' ball 0 1 = (e₀ '' closedBall 0 1)ᶜ := by
    rw [hinner₁, hcomp₁, interior_compl, hcl₀]
  refine ⟨e₀, e₁, (fun _ => rfl), hclosed₀, hclosed₁, he₀, hei₀, he₁, hei₁,
    hboundary₀, hboundary₁, hcomp₁, ?_, ?_, ?_⟩
  · rw [hopen₁]
    exact disjoint_left.mpr fun x hx hx' => hx' ((image_mono ball_subset_closedBall) hx)
  · rw [hcomp₁]
    ext x
    constructor
    · exact fun _ => mem_univ _
    · intro _
      by_cases hx : x ∈ e₀ '' ball 0 1
      · exact Or.inl ((image_mono ball_subset_closedBall) hx)
      · exact Or.inr hx
  · rw [hcomp₁]
    change e₀ '' closedBall 0 1 \ e₀ '' ball 0 1 = range f
    rw [hinner₀, ← hK₀.frontier_eq, ← hfront₀, hboundary₀]

end Poincare.Manifold.Schoenflies
