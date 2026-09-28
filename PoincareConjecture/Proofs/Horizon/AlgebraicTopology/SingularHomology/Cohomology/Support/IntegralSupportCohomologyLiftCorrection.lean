import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.Support.IntegralSupportCohomologyMV
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.HomologicalAlgebra.ModuleComplexHomologyClass







set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace Poincare.Topology

attribute [local instance 2000] Submodule.Quotient.module Submodule.module

private theorem boundary_of_moduleHomologyClass_eq
    (S : ShortComplex (ModuleCat.{u} Int))
    (z w : LinearMap.ker S.g.hom)
    (h : moduleHomologyClass S z = moduleHomologyClass S w) :
    ∃ a : S.X₁, S.f a = z.val - w.val := by
  have he := congrArg S.moduleCatHomologyIso.hom h
  simp only [moduleHomologyClass, Iso.inv_hom_id_apply] at he
  change (Submodule.Quotient.mk z :
    LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) =
      Submodule.Quotient.mk w at he
  obtain ⟨a, ha⟩ := (Submodule.Quotient.eq (LinearMap.range S.moduleCatToCycles)).mp he
  exact ⟨a, congrArg Subtype.val ha⟩

private theorem exists_corrected_cochain_lift
    (S : ShortComplex (CochainComplex (ModuleCat.{u} Int) Nat))
    (hS : S.ShortExact) (C : CochainComplex (ModuleCat.{u} Int) Nat)
    (F : C ⟶ S.X₁) (q : Nat) (hF : IsIso (homologyMap F (q + 1)))
    (z : S.X₃.X q) (hz : S.X₃.d q (q + 1) z = 0) :
    ∃ (b : S.X₂.X q) (gamma : C.X (q + 1)),
      S.g.f q b = z ∧ C.d (q + 1) (q + 2) gamma = 0 ∧
        S.f.f (q + 1) (F.f (q + 1) gamma) = S.X₂.d q (q + 1) b := by
  let := hF
  have hseq (n : Nat) := (shortExact_iff_degreewise_shortExact S).mp hS n
  obtain ⟨b, hb⟩ := (hseq q).moduleCat_surjective_g z
  change S.X₂.X q at b
  change S.g.f q b = z at hb
  have hdb : S.g.f (q + 1) (S.X₂.d q (q + 1) b) = 0 := by
    have hc := congrArg (fun f => f b) (S.g.comm q (q + 1))
    change S.X₃.d q (q + 1) (S.g.f q b) =
      S.g.f (q + 1) (S.X₂.d q (q + 1) b) at hc
    exact hc.symm.trans (by rw [hb, hz])
  obtain ⟨v, hv⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (hseq (q + 1)).exact (S.X₂.d q (q + 1) b) hdb
  change S.X₁.X (q + 1) at v
  change S.f.f (q + 1) v = S.X₂.d q (q + 1) b at hv
  have hvcycle : S.X₁.d (q + 1) (q + 2) v = 0 := by
    apply (hseq (q + 2)).moduleCat_injective_f
    change S.f.f (q + 2) (S.X₁.d (q + 1) (q + 2) v) = S.f.f (q + 2) 0
    have hc := congrArg (fun f => f v) (S.f.comm (q + 1) (q + 2))
    change S.X₂.d (q + 1) (q + 2) (S.f.f (q + 1) v) =
      S.f.f (q + 2) (S.X₁.d (q + 1) (q + 2) v) at hc
    rw [← hc, hv, map_zero]
    exact congrArg (fun f => f b) (S.X₂.d_comp_d q (q + 1) (q + 2))
  have hi : (ComplexShape.up Nat).prev (q + 1) = q :=
    (ComplexShape.up Nat).prev_eq' (show (ComplexShape.up Nat).Rel q (q + 1) from rfl)
  have hk : (ComplexShape.up Nat).next (q + 1) = q + 2 :=
    (ComplexShape.up Nat).next_eq'
      (show (ComplexShape.up Nat).Rel (q + 1) (q + 2) from rfl)
  let vcycle : LinearMap.ker (S.X₁.sc' q (q + 1) (q + 2)).g.hom := ⟨v, hvcycle⟩
  let e := asIso (homologyMap F (q + 1))
  obtain ⟨gamma, hgamma⟩ := moduleComplexHomologyClass_surjective C q (q + 1)
    (q + 2) hi hk
    (e.inv (moduleComplexHomologyClass S.X₁ q (q + 1) (q + 2) hi hk vcycle))
  have hclass : moduleComplexHomologyClass S.X₁ q (q + 1) (q + 2) hi hk vcycle =
      moduleComplexHomologyClass S.X₁ q (q + 1) (q + 2) hi hk
        (moduleHomologyCycleMap
          ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.up Nat)
            q (q + 1) (q + 2)).map F) gamma) := by
    have he := congrArg e.hom hgamma
    rw [Iso.inv_hom_id_apply] at he
    exact he.symm.trans (moduleComplexHomologyClass_map F q (q + 1) (q + 2) hi hk gamma)
  have hclass' := congrArg (S.X₁.homologyIsoSc' q (q + 1) (q + 2) hi hk).hom hclass
  simp only [moduleComplexHomologyClass, Iso.inv_hom_id_apply] at hclass'
  obtain ⟨lambda, hlambda⟩ := boundary_of_moduleHomologyClass_eq _ _ _ hclass'
  change S.X₁.d q (q + 1) lambda = v - F.f (q + 1) gamma.val at hlambda
  refine ⟨b - S.f.f q lambda, gamma.val, ?_, gamma.property, ?_⟩
  · have hzero := congrArg (fun f => f.f q lambda) S.zero
    change S.g.f q (S.f.f q lambda) = 0 at hzero
    rw [map_sub, hzero, sub_zero, hb]
  · have hc := congrArg (fun f => f lambda) (S.f.comm q (q + 1))
    change S.X₂.d q (q + 1) (S.f.f q lambda) =
      S.f.f (q + 1) (S.X₁.d q (q + 1) lambda) at hc
    rw [map_sub, hc, hlambda, map_sub, hv, sub_sub_cancel]

theorem exists_integralSupportCohomology_corrected_lift
    {X : Type u} [TopologicalSpace X]
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat)
    (z : (integralSupportCochains (K ∪ L)).X q)
    (hz : (integralSupportCochains (K ∪ L)).d q (q + 1) z = 0) :
    ∃ (b : (integralSupportCochains K ⊞ integralSupportCochains L).X q)
      (gamma : (integralSupportCochains (K ∩ L)).X (q + 1)),
      (integralSupportCochainSum K L).f q b = z ∧
      (integralSupportCochains (K ∩ L)).d (q + 1) (q + 2) gamma = 0 ∧
      (integralSupportCochainDifference K L).f (q + 1) gamma =
        (integralSupportCochains K ⊞ integralSupportCochains L).d q (q + 1) b := by
  let F := integralDualMap (integralSupportComparison K L)
  let : QuasiIso F := integralSupportComparison_dual_quasiIso K L hK hL
  have hF : IsIso (homologyMap F (q + 1)) :=
    (quasiIsoAt_iff_isIso_homologyMap F (q + 1)).mp inferInstance
  obtain ⟨b, gamma, hb, hgamma, hboundary⟩ := exists_corrected_cochain_lift
    (integralSupportDualSequence K L) (integralSupportDualSequence_shortExact' K L)
    (integralSupportCochains (K ∩ L)) F q hF z hz
  refine ⟨b, gamma, ?_, hgamma, ?_⟩
  · rw [← integralSupportDualSequence_g]
    exact hb
  · have hf := congrArg (fun f => f.f (q + 1) gamma) (integralSupportDualComparison_f K L)
    exact hf.symm.trans hboundary

end Poincare.Topology
