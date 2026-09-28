import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Clearance
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Annulus.CapFiber
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Annulus.ConnectedExterior







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
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)

private theorem annulus_height_mem_tube {t : Real} (ht : t ∈ Icc (-S.a) S.a) :
    t ∈ Ioo (-S.ε) S.ε := by
  constructor <;> linarith [ht.1, ht.2, S.a_lt_quarter_ε, S.a_pos]

theorem prepared_tube_lower_cut_mem_child (q : S1) :
    S.D (f (S.T (q, -S.a))) ∈ range S.fMinus := by
  rw [S.fMinus_range]
  apply Or.inl
  exact (S.prepared_tube_mem_capMinus_iff q
    (S.annulus_height_mem_tube ⟨le_rfl, by linarith [S.a_pos]⟩)).mpr
    ⟨le_rfl, by linarith [S.s_pos]⟩

theorem prepared_tube_upper_cut_mem_child (q : S1) :
    S.D (f (S.T (q, S.a))) ∈ range S.fPlus := by
  rw [S.fPlus_range]
  apply Or.inl
  exact (S.prepared_tube_mem_capPlus_iff q
    (S.annulus_height_mem_tube ⟨by linarith [S.a_pos], le_rfl⟩)).mpr
    ⟨by linarith [S.s_pos], le_rfl⟩


theorem prepared_tube_not_mem_childMinus (q : S1) {t : Real}
    (hl : -S.a + S.s < t) (hu : t ≤ S.a) :
    S.D (f (S.T (q, t))) ∉ range S.fMinus := by
  have ht : t ∈ Icc (-S.a) S.a := ⟨by linarith [S.s_pos], hu⟩
  intro hy
  by_cases he : t = S.a
  · subst t
    exact disjoint_left.mp S.children_disjoint hy (S.prepared_tube_upper_cut_mem_child q)
  rw [S.fMinus_range] at hy
  rcases hy with hcap | ⟨p, hp, heq⟩
  · exact (not_le_of_gt hl)
      ((S.prepared_tube_mem_capMinus_iff q (S.annulus_height_mem_tube ht)).mp hcap).2
  · have heq' := S.prepared_embedding.isEmbedding.injective heq
    exact S.tube_not_mem_retainedMinus q
      ⟨by linarith [S.s_pos], lt_of_le_of_ne hu he⟩ (heq' ▸ hp)


theorem prepared_tube_not_mem_childPlus (q : S1) {t : Real}
    (hl : -S.a ≤ t) (hu : t < S.a - S.s) :
    S.D (f (S.T (q, t))) ∉ range S.fPlus := by
  have ht : t ∈ Icc (-S.a) S.a := ⟨hl, by linarith [S.s_pos]⟩
  intro hy
  by_cases he : t = -S.a
  · subst t
    exact disjoint_left.mp S.children_disjoint (S.prepared_tube_lower_cut_mem_child q) hy
  rw [S.fPlus_range] at hy
  rcases hy with hcap | ⟨p, hp, heq⟩
  · exact (not_le_of_gt hu)
      ((S.prepared_tube_mem_capPlus_iff q (S.annulus_height_mem_tube ht)).mp hcap).1
  · have heq' := S.prepared_embedding.isEmbedding.injective heq
    exact S.tube_not_mem_retainedPlus q
      ⟨lt_of_le_of_ne hl (Ne.symm he), by linarith [S.s_pos]⟩ (heq' ▸ hp)



theorem prepared_tube_not_mem_filledMinus
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : B '' sphere (0 : E3) 1 = range S.fMinus)
    (havoid : Disjoint (B '' closedBall (0 : E3) 1) (range S.fPlus))
    (q : S1) {t : Real} (hl : -S.a + S.s < t) (hu : t ≤ S.a) :
    S.D (f (S.T (q, t))) ∉ B '' closedBall (0 : E3) 1 := by
  let p : Real → E3 := fun r => (c + r) • v + (S.γ q : E3)
  have hp : Continuous p := by fun_prop
  have hpr (r : Real) (hr : r ∈ Icc t S.a) : p r = S.D (f (S.T (q, r))) := by
    exact (S.cylinder q r (S.annulus_height_mem_tube
      ⟨by linarith [hr.1, S.s_pos], hr.2⟩)).symm
  have hconn : IsPreconnected (p '' Icc t S.a) :=
    isPreconnected_Icc.image p hp.continuousOn
  have hboundary : Disjoint (p '' Icc t S.a) (B '' sphere (0 : E3) 1) := by
    apply disjoint_left.mpr
    rintro _ ⟨r, hr, rfl⟩ hy
    rw [hB, hpr r hr] at hy
    exact S.prepared_tube_not_mem_childMinus q (hl.trans_le hr.1) hr.2 hy
  have hpoint : ((p '' Icc t S.a) ∩ (B '' closedBall (0 : E3) 1)ᶜ).Nonempty := by
    refine ⟨p S.a, mem_image_of_mem p ⟨hu, le_rfl⟩, ?_⟩
    intro hy
    apply disjoint_left.mp havoid hy
    rw [hpr S.a ⟨hu, le_rfl⟩]
    exact S.prepared_tube_upper_cut_mem_child q
  have hout := Reverse.subset_exterior_of_isPreconnected B.toHomeomorph hconn hboundary hpoint
  have hpt := hout (mem_image_of_mem p (show t ∈ Icc t S.a from ⟨le_rfl, hu⟩))
  rwa [hpr t ⟨le_rfl, hu⟩] at hpt



theorem prepared_tube_not_mem_filledPlus
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : B '' sphere (0 : E3) 1 = range S.fPlus)
    (havoid : Disjoint (B '' closedBall (0 : E3) 1) (range S.fMinus))
    (q : S1) {t : Real} (hl : -S.a ≤ t) (hu : t < S.a - S.s) :
    S.D (f (S.T (q, t))) ∉ B '' closedBall (0 : E3) 1 := by
  let p : Real → E3 := fun r => (c + r) • v + (S.γ q : E3)
  have hp : Continuous p := by fun_prop
  have hpr (r : Real) (hr : r ∈ Icc (-S.a) t) : p r = S.D (f (S.T (q, r))) := by
    exact (S.cylinder q r (S.annulus_height_mem_tube
      ⟨hr.1, by linarith [hr.2, S.s_pos]⟩)).symm
  have hconn : IsPreconnected (p '' Icc (-S.a) t) :=
    isPreconnected_Icc.image p hp.continuousOn
  have hboundary : Disjoint (p '' Icc (-S.a) t) (B '' sphere (0 : E3) 1) := by
    apply disjoint_left.mpr
    rintro _ ⟨r, hr, rfl⟩ hy
    rw [hB, hpr r hr] at hy
    exact S.prepared_tube_not_mem_childPlus q hr.1 (hr.2.trans_lt hu) hy
  have hpoint : ((p '' Icc (-S.a) t) ∩ (B '' closedBall (0 : E3) 1)ᶜ).Nonempty := by
    refine ⟨p (-S.a), mem_image_of_mem p ⟨le_rfl, hl⟩, ?_⟩
    intro hy
    apply disjoint_left.mp havoid hy
    rw [hpr (-S.a) ⟨le_rfl, hl⟩]
    exact S.prepared_tube_lower_cut_mem_child q
  have hout := Reverse.subset_exterior_of_isPreconnected B.toHomeomorph hconn hboundary hpoint
  have hpt := hout (mem_image_of_mem p (show t ∈ Icc (-S.a) t from ⟨hl, le_rfl⟩))
  rwa [hpr t ⟨hl, le_rfl⟩] at hpt



theorem filledMinus_inter_annulus_subset_cap
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : B '' sphere (0 : E3) 1 = range S.fMinus)
    (havoid : Disjoint (B '' closedBall (0 : E3) 1) (range S.fPlus)) :
    (B '' closedBall (0 : E3) 1) ∩
        ((fun p => S.D (f p)) '' (S.T '' (univ ×ˢ Icc (-S.a) S.a))) ⊆
      S.gMinus '' closedBall (0 : E2) 1 := by
  rintro _ ⟨hball, _, ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩, rfl⟩
  by_cases htop : t ≤ -S.a + S.s
  · exact (S.prepared_tube_mem_capMinus_iff q (S.annulus_height_mem_tube ht)).mpr
      ⟨ht.1, htop⟩
  · exact False.elim (S.prepared_tube_not_mem_filledMinus B hB havoid q
      (lt_of_not_ge htop) ht.2 hball)



theorem filledPlus_inter_annulus_subset_cap
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : B '' sphere (0 : E3) 1 = range S.fPlus)
    (havoid : Disjoint (B '' closedBall (0 : E3) 1) (range S.fMinus)) :
    (B '' closedBall (0 : E3) 1) ∩
        ((fun p => S.D (f p)) '' (S.T '' (univ ×ˢ Icc (-S.a) S.a))) ⊆
      S.gPlus '' closedBall (0 : E2) 1 := by
  rintro _ ⟨hball, _, ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩, rfl⟩
  by_cases hbottom : S.a - S.s ≤ t
  · exact (S.prepared_tube_mem_capPlus_iff q (S.annulus_height_mem_tube ht)).mpr
      ⟨hbottom, ht.2⟩
  · exact False.elim (S.prepared_tube_not_mem_filledPlus B hB havoid q
      ht.1 (lt_of_not_ge hbottom) hball)

end Poincare.Manifold.Schoenflies.SphereSurgeryStep

end

end M38Schoenflies
