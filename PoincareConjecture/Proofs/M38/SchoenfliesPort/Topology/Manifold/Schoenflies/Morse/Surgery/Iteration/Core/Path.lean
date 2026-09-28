import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Tree
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.RetainedDerivatives

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

inductive SphereSurgeryPath (v : E3) : (S2 -> E3) -> (S2 -> E3) -> Type
  | refl (f : S2 -> E3) : SphereSurgeryPath v f f
  | minus {f g : S2 -> E3} {c R : Real}
      (S : SphereSurgeryStep f v c R) (next : SphereSurgeryPath v S.fMinus g) :
      SphereSurgeryPath v f g
  | plus {f g : S2 -> E3} {c R : Real}
      (S : SphereSurgeryStep f v c R) (next : SphereSurgeryPath v S.fPlus g) :
      SphereSurgeryPath v f g

namespace SphereSurgeryPath

variable {v : E3}

def core : {f g : S2 -> E3} -> SphereSurgeryPath v f g -> Set S2
  | _, _, .refl _ => univ
  | _, _, .minus S next => next.core ∩ (S.eMinus '' closedBall 0 1)
  | _, _, .plus S next => next.core ∩ (S.ePlus '' closedBall 0 1)

def boundaryHeights : {f g : S2 -> E3} -> SphereSurgeryPath v f g -> Set Real
  | _, _, .refl _ => ∅
  | _, _, .minus (c := c) S next => insert (c - S.a) next.boundaryHeights
  | _, _, .plus (c := c) S next => insert (c + S.a) next.boundaryHeights

def Protects (B : Set Real) : {f g : S2 -> E3} -> SphereSurgeryPath v f g -> Prop
  | _, _, .refl _ => True
  | _, _, .minus (c := c) (R := R) _ next =>
      (∀ k ∈ B, R < |k - c|) ∧ next.Protects B
  | _, _, .plus (c := c) (R := R) _ next =>
      (∀ k ∈ B, R < |k - c|) ∧ next.Protects B

variable {f g : S2 -> E3} (P : SphereSurgeryPath v f g)

theorem isClosed_core : IsClosed P.core := by
  induction P with
  | refl => exact isClosed_univ
  | minus S next ih =>
    exact ih.inter ((isCompact_closedBall 0 1).image_of_continuousOn
      (S.eMinus.continuousOn.mono S.eMinus_source)).isClosed
  | plus S next ih =>
    exact ih.inter ((isCompact_closedBall 0 1).image_of_continuousOn
      (S.ePlus.continuousOn.mono S.ePlus_source)).isClosed

theorem finite_boundaryHeights : P.boundaryHeights.Finite := by
  induction P with
  | refl => exact finite_empty
  | minus S next ih => exact ih.insert _
  | plus S next ih => exact ih.insert _

theorem height_eq_on_core : EqOn (fun p => inner Real v (g p))
    (fun p => inner Real v (f p)) P.core := by
  induction P with
  | refl => exact fun _ _ => rfl
  | minus S next ih =>
    intro p hp
    exact (ih hp.1).trans ((congrArg (inner Real v) (S.retainedMinus_eq p hp.2)).trans
      (S.height_preserving _))
  | plus S next ih =>
    intro p hp
    exact (ih hp.1).trans ((congrArg (inner Real v) (S.retainedPlus_eq p hp.2)).trans
      (S.height_preserving _))

theorem mfderiv_eq_on_core : ∀ p ∈ P.core,
    mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p =
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p := by
  induction P with
  | refl => exact fun _ _ => rfl
  | minus S next ih =>
    intro p hp
    rw [ih p hp.1]
    exact mfderiv_eq_on_smooth_closed_disk
      ((innerSL Real v).contMDiff.comp S.fMinus_embedding.contMDiff)
      ((innerSL Real v).contMDiff.comp S.original_embedding.contMDiff)
      S.eMinus S.eMinus_source S.eMinus_smooth S.eMinus_symm_smooth
      (fun x hx => (congrArg (inner Real v) (S.retainedMinus_eq x hx)).trans
        (S.height_preserving _)) p hp.2
  | plus S next ih =>
    intro p hp
    rw [ih p hp.1]
    exact mfderiv_eq_on_smooth_closed_disk
      ((innerSL Real v).contMDiff.comp S.fPlus_embedding.contMDiff)
      ((innerSL Real v).contMDiff.comp S.original_embedding.contMDiff)
      S.ePlus S.ePlus_source S.ePlus_smooth S.ePlus_symm_smooth
      (fun x hx => (congrArg (inner Real v) (S.retainedPlus_eq x hx)).trans
        (S.height_preserving _)) p hp.2

theorem frontier_height_mem : ∀ p ∈ frontier P.core,
    inner Real v (g p) ∈ P.boundaryHeights := by
  induction P with
  | refl => simp [core]
  | minus S next ih =>
    intro p hp
    have hpC : p ∈ next.core ∩ S.eMinus '' closedBall 0 1 :=
      (isClosed_core (.minus S next)).frontier_subset hp
    rcases frontier_inter_subset _ _ hp with hnext | hret
    · exact mem_insert_of_mem _ (ih p hnext.1)
    · have hboundary := hret.2
      rw [← S.eMinus.image_sphere_eq_frontier S.eMinus_source rfl,
        S.eMinus_boundary] at hboundary
      obtain ⟨q, hq⟩ := hboundary
      have ht : -S.a ∈ Ioo (-S.ε) S.ε := by
        constructor <;> linarith [S.a_pos, S.ε_pos, S.a_lt_quarter_ε]
      have hh := next.height_eq_on_core hpC.1
      dsimp only at hh
      rw [hh, S.retainedMinus_eq p hpC.2, S.height_preserving, ← hq,
        S.tube_height q (-S.a) ht]
      simp [boundaryHeights, sub_eq_add_neg]
  | plus S next ih =>
    intro p hp
    have hpC : p ∈ next.core ∩ S.ePlus '' closedBall 0 1 :=
      (isClosed_core (.plus S next)).frontier_subset hp
    rcases frontier_inter_subset _ _ hp with hnext | hret
    · exact mem_insert_of_mem _ (ih p hnext.1)
    · have hboundary := hret.2
      rw [← S.ePlus.image_sphere_eq_frontier S.ePlus_source rfl,
        S.ePlus_boundary] at hboundary
      obtain ⟨q, hq⟩ := hboundary
      have ht : S.a ∈ Ioo (-S.ε) S.ε := by
        constructor <;> linarith [S.a_pos, S.ε_pos, S.a_lt_quarter_ε]
      have hh := next.height_eq_on_core hpC.1
      dsimp only at hh
      rw [hh, S.retainedPlus_eq p hpC.2, S.height_preserving, ← hq,
        S.tube_height q S.a ht]
      exact mem_insert _ _

theorem disjoint_boundaryHeights {B : Set Real} (hP : P.Protects B) :
    Disjoint P.boundaryHeights B := by
  induction P with
  | refl => simp [boundaryHeights]
  | minus S next ih =>
    apply Set.disjoint_left.mpr
    intro k hk hkB
    rcases hk with heq | hk
    · have hfar := hP.1 k hkB
      rw [heq, sub_sub_cancel_left, abs_neg, abs_of_pos S.a_pos] at hfar
      linarith [S.a_lt_quarter_R, S.a_pos]
    · exact Set.disjoint_left.mp (ih hP.2) hk hkB
  | plus S next ih =>
    apply Set.disjoint_left.mpr
    intro k hk hkB
    rcases hk with heq | hk
    · have hfar := hP.1 k hkB
      rw [heq, add_sub_cancel_left, abs_of_pos S.a_pos] at hfar
      linarith [S.a_lt_quarter_R, S.a_pos]
    · exact Set.disjoint_left.mp (ih hP.2) hk hkB

end SphereSurgeryPath

namespace SphereSurgeryTree

variable {v : E3} {A : Finset Real} {f g : S2 -> E3} {B : Set Real}

theorem exists_path_to_leaf (tree : SphereSurgeryTree v A f) (hg : g ∈ tree.leaves)
    (hprotects : tree.Protects B) :
    ∃ P : SphereSurgeryPath v f g, P.Protects B := by
  induction tree with
  | leaf hf hav =>
    simp only [leaves, List.mem_singleton] at hg
    subst g
    exact ⟨.refl _, trivial⟩
  | branch hc hsep S minus plus ihM ihP =>
    rcases List.mem_append.mp hg with hM | hP
    · obtain ⟨P, hP⟩ := ihM hM hprotects.2.1
      exact ⟨.minus S P, hprotects.1, hP⟩
    · obtain ⟨P, hP⟩ := ihP hP hprotects.2.2
      exact ⟨.plus S P, hprotects.1, hP⟩

end SphereSurgeryTree

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
