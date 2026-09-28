import PoincareConjecture.Proofs.M51.CompletedStageChain
import PoincareConjecture.Proofs.M51.ComposedExtensionReadouts

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51.CompletedStageChain

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S}
  {C : RepairedCanonicalInductionData S N}
  {F0 : SurgeryFlowData.{u}} {k : Nat}
  (Q : CompletedStageChain S N C F0 k)

noncomputable def extensionBetween (n m : Nat) (hnm : n <= m) :
    SurgeryFlowExtension (Q.flow n) :=
  ComposedExtension.between Q.flow Q.step Q.step_eq n m hnm

theorem extensionBetween_eq (n m : Nat) (hnm : n <= m) :
    (Q.extensionBetween n m hnm).extended = Q.flow m :=
  ComposedExtension.between_extended Q.flow Q.step Q.step_eq n m hnm

theorem stageTime (n m : Nat) (hnm : n <= m) {t : Real}
    (ht : t ∈ (Q.flow n).time_domain) : t ∈ (Q.flow m).time_domain :=
  ComposedExtension.oldTimeBetween Q.flow Q.step Q.step_eq n m hnm ht

noncomputable def stageIdentify (n m : Nat) (hnm : n <= m) (t : Real)
    (ht : t ∈ (Q.flow n).time_domain) :
    Diffeomorph (𝓡 3) (𝓡 3) ((Q.flow n).slice t).carrier
      ((Q.flow m).slice t).carrier ∞ :=
  ComposedExtension.identifyBetween Q.flow Q.step Q.step_eq n m hnm t ht

theorem stageIdentify_self (n : Nat) (t : Real)
    (ht : t ∈ (Q.flow n).time_domain) :
    Q.stageIdentify n n le_rfl t ht =
      Diffeomorph.refl (𝓡 3) ((Q.flow n).slice t).carrier ∞ := by
  simp only [stageIdentify, ComposedExtension.identifyBetween,
    ComposedExtension.between_self]
  rfl

theorem stageIdentify_comp (n m q : Nat) (hnm : n <= m) (hmq : m <= q)
    (t : Real) (ht : t ∈ (Q.flow n).time_domain)
    (x : ((Q.flow n).slice t).carrier) :
    Q.stageIdentify n q (hnm.trans hmq) t ht x =
      Q.stageIdentify m q hmq t (Q.stageTime n m hnm ht)
        (Q.stageIdentify n m hnm t ht x) := by
  exact congrArg (fun e => e x)
    (ComposedExtension.identifyBetween_trans Q.flow Q.step Q.step_eq
      n m q hnm hmq t ht)

noncomputable def compare (n m : Nat) (t : Real)
    (hn : t ∈ (Q.flow n).time_domain) (hm : t ∈ (Q.flow m).time_domain) :
    Diffeomorph (𝓡 3) (𝓡 3) ((Q.flow n).slice t).carrier
      ((Q.flow m).slice t).carrier ∞ :=
  (Q.stageIdentify n (max n m) (le_max_left _ _) t hn).trans
    (Q.stageIdentify m (max n m) (le_max_right _ _) t hm).symm

theorem compare_common (n m q : Nat) (hnq : n <= q) (hmq : m <= q)
    (t : Real) (hn : t ∈ (Q.flow n).time_domain)
    (hm : t ∈ (Q.flow m).time_domain) (x : ((Q.flow n).slice t).carrier) :
    Q.stageIdentify m q hmq t hm (Q.compare n m t hn hm x) =
      Q.stageIdentify n q hnq t hn x := by
  have hpq : max n m <= q := max_le hnq hmq
  rw [Q.stageIdentify_comp m (max n m) q (le_max_right _ _) hpq t hm,
    Q.stageIdentify_comp n (max n m) q (le_max_left _ _) hpq t hn]
  simp only [compare, Diffeomorph.coe_trans, Function.comp_apply,
    Diffeomorph.apply_symm_apply]

theorem compare_self (n : Nat) (t : Real)
    (ht : t ∈ (Q.flow n).time_domain) (x : ((Q.flow n).slice t).carrier) :
    Q.compare n n t ht ht x = x := by
  exact (Q.stageIdentify n n le_rfl t ht).injective
    (Q.compare_common n n n le_rfl le_rfl t ht ht x)

theorem compare_comp (n m l : Nat) (t : Real)
    (hn : t ∈ (Q.flow n).time_domain) (hm : t ∈ (Q.flow m).time_domain)
    (hl : t ∈ (Q.flow l).time_domain) (x : ((Q.flow n).slice t).carrier) :
    Q.compare m l t hm hl (Q.compare n m t hn hm x) =
      Q.compare n l t hn hl x := by
  let q := max n (max m l)
  have hnq : n <= q := le_max_left _ _
  have hmq : m <= q := (le_max_left m l).trans (le_max_right _ _)
  have hlq : l <= q := (le_max_right m l).trans (le_max_right _ _)
  apply (Q.stageIdentify l q hlq t hl).injective
  change Q.stageIdentify l q hlq t hl (Q.compare m l t hm hl
    (Q.compare n m t hn hm x)) =
      Q.stageIdentify l q hlq t hl (Q.compare n l t hn hl x)
  rw [Q.compare_common m l q hmq hlq t hm hl,
    Q.compare_common n m q hnq hmq t hn hm,
    Q.compare_common n l q hnq hlq t hn hl]

theorem compare_of_le (n m : Nat) (hnm : n <= m) (t : Real)
    (hn : t ∈ (Q.flow n).time_domain) (hm : t ∈ (Q.flow m).time_domain)
    (x : ((Q.flow n).slice t).carrier) :
    Q.compare n m t hn hm x = Q.stageIdentify n m hnm t hn x := by
  simpa only [Q.stageIdentify_self, Diffeomorph.coe_refl, id_eq] using
    Q.compare_common n m m hnm le_rfl t hn hm x

theorem compare_symm (n m : Nat) (t : Real)
    (hn : t ∈ (Q.flow n).time_domain) (hm : t ∈ (Q.flow m).time_domain) :
    (Q.compare n m t hn hm).symm = Q.compare m n t hm hn := by
  ext x
  apply (Q.compare n m t hn hm).injective
  change Q.compare n m t hn hm ((Q.compare n m t hn hm).symm x) =
    Q.compare n m t hn hm (Q.compare m n t hm hn x)
  rw [Diffeomorph.apply_symm_apply, Q.compare_comp, Q.compare_self]

theorem compare_metric (n m : Nat) (t : Real)
    (hn : t ∈ (Q.flow n).time_domain) (hm : t ∈ (Q.flow m).time_domain)
    (x : ((Q.flow n).slice t).carrier) (v w : TangentSpace (𝓡 3) x) :
    ((Q.flow m).metric t).inner (Q.compare n m t hn hm x)
      (mfderiv (𝓡 3) (𝓡 3) (Q.compare n m t hn hm) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Q.compare n m t hn hm) x w) =
        ((Q.flow n).metric t).inner x v w := by
  let p := max n m
  let f := Q.stageIdentify n p (le_max_left _ _) t hn
  let g := (Q.stageIdentify m p (le_max_right _ _) t hm).symm
  have hf : forall x v w,
      ((Q.flow p).metric t).inner (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) =
          ((Q.flow n).metric t).inner x v w :=
    ComposedExtension.identifyTo_metric_pullback
      (Q.extensionBetween n p (le_max_left _ _))
      (Q.extensionBetween_eq n p (le_max_left _ _)) t hn
  have hg : MetricHomothety ((Q.flow p).metric t) ((Q.flow m).metric t) g 1 :=
    ComposedExtension.identifyTo_metric_homothety_symm
      (Q.extensionBetween m p (le_max_right _ _))
      (Q.extensionBetween_eq m p (le_max_right _ _)) t hm
  change ((Q.flow m).metric t).inner ((f.trans g) x)
    (mfderiv (𝓡 3) (𝓡 3) (f.trans g) x v)
    (mfderiv (𝓡 3) (𝓡 3) (f.trans g) x w) = _
  rw [Diffeomorph.coe_trans, mfderiv_comp x
    (g.contMDiff.mdifferentiable (by simp) (f x))
    (f.contMDiff.mdifferentiable (by simp) x)]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  rw [hg, one_mul]
  exact hf x v w

end PoincareConjecture.M51.CompletedStageChain
