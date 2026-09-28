import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.SupportedEquivalence
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Range
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Annulus.Clearance







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryStep

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)



theorem exists_protected_lower_replacement
    (B L D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : B '' sphere (0 : E3) 1 = range S.fMinus)
    (havoid : Disjoint (B '' closedBall (0 : E3) 1) (range S.fPlus))
    (hDB : D '' (B '' closedBall (0 : E3) 1) = L '' closedBall (0 : E3) 1)
    (hnest : L '' closedBall (0 : E3) 1 ⊆ B '' closedBall (0 : E3) 1)
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {r : Real} (hr : 1 < r)
    (hcore : g '' closedBall (0 : E2) 1 = S.gMinus '' closedBall 0 1)
    (hsub : g '' closedBall (0 : E2) r ⊆ range S.fMinus)
    (hfix : ∀ y ∈ g '' closedBall (0 : E2) r, D y = y) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' range S.fMinus = L '' sphere (0 : E3) 1 ∧
      (∀ y ∈ S.gMinus '' closedBall (0 : E2) 1, F y = y) ∧
      (∀ y ∈ (fun p => S.D (f p)) '' (S.T '' (univ ×ˢ Icc (-S.a) S.a)), F y = y) ∧
      ∀ y ∈ range S.fPlus, F y = y := by
  let C := ((fun p => S.D (f p)) '' (S.T '' (univ ×ˢ Icc (-S.a) S.a))) ∪ range S.fPlus
  have hC : IsClosed C := S.isCompact_prepared_annulus.isClosed.union
    (isCompact_range S.fPlus_embedding.contMDiff.continuous).isClosed
  have hBC : (B '' closedBall (0 : E3) 1) ∩ C ⊆ g '' closedBall (0 : E2) 1 := by
    rw [hcore]
    rintro y ⟨hyB, hyann | hyother⟩
    · exact S.filledMinus_inter_annulus_subset_cap B hB havoid ⟨hyB, hyann⟩
    · exact False.elim (disjoint_left.mp havoid hyB hyother)
  obtain ⟨F, hFC, hFcap, hFB⟩ := Reverse.exists_nested_ball_equivalence_fixing_obstacle
    B D (by rw [hDB]; exact hnest) g hg hgi hgd hr (hB.symm ▸ hsub) hfix hC hBC
      ⟨v, mem_sphere_zero_iff_norm.mpr S.unit_v⟩
  have hFball : F '' (B '' closedBall (0 : E3) 1) = L '' closedBall (0 : E3) 1 :=
    hFB.trans hDB
  refine ⟨F, ?_, hcore ▸ hFcap, fun y hy => hFC y (Or.inl hy),
    fun y hy => hFC y (Or.inr hy)⟩
  rw [← hB]
  exact Reverse.image_filled_sphere_of_image_filled_ball F B L hFball


theorem exists_protected_upper_replacement
    (B L D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : B '' sphere (0 : E3) 1 = range S.fPlus)
    (havoid : Disjoint (B '' closedBall (0 : E3) 1) (range S.fMinus))
    (hDB : D '' (B '' closedBall (0 : E3) 1) = L '' closedBall (0 : E3) 1)
    (hnest : L '' closedBall (0 : E3) 1 ⊆ B '' closedBall (0 : E3) 1)
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {r : Real} (hr : 1 < r)
    (hcore : g '' closedBall (0 : E2) 1 = S.gPlus '' closedBall 0 1)
    (hsub : g '' closedBall (0 : E2) r ⊆ range S.fPlus)
    (hfix : ∀ y ∈ g '' closedBall (0 : E2) r, D y = y) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' range S.fPlus = L '' sphere (0 : E3) 1 ∧
      (∀ y ∈ S.gPlus '' closedBall (0 : E2) 1, F y = y) ∧
      (∀ y ∈ (fun p => S.D (f p)) '' (S.T '' (univ ×ˢ Icc (-S.a) S.a)), F y = y) ∧
      ∀ y ∈ range S.fMinus, F y = y := by
  let C := ((fun p => S.D (f p)) '' (S.T '' (univ ×ˢ Icc (-S.a) S.a))) ∪ range S.fMinus
  have hC : IsClosed C := S.isCompact_prepared_annulus.isClosed.union
    (isCompact_range S.fMinus_embedding.contMDiff.continuous).isClosed
  have hBC : (B '' closedBall (0 : E3) 1) ∩ C ⊆ g '' closedBall (0 : E2) 1 := by
    rw [hcore]
    rintro y ⟨hyB, hyann | hyother⟩
    · exact S.filledPlus_inter_annulus_subset_cap B hB havoid ⟨hyB, hyann⟩
    · exact False.elim (disjoint_left.mp havoid hyB hyother)
  obtain ⟨F, hFC, hFcap, hFB⟩ := Reverse.exists_nested_ball_equivalence_fixing_obstacle
    B D (by rw [hDB]; exact hnest) g hg hgi hgd hr (hB.symm ▸ hsub) hfix hC hBC
      ⟨v, mem_sphere_zero_iff_norm.mpr S.unit_v⟩
  have hFball : F '' (B '' closedBall (0 : E3) 1) = L '' closedBall (0 : E3) 1 :=
    hFB.trans hDB
  refine ⟨F, ?_, hcore ▸ hFcap, fun y hy => hFC y (Or.inl hy),
    fun y hy => hFC y (Or.inr hy)⟩
  rw [← hB]
  exact Reverse.image_filled_sphere_of_image_filled_ball F B L hFball

end Poincare.Manifold.Schoenflies.SphereSurgeryStep

end

end M38Schoenflies
