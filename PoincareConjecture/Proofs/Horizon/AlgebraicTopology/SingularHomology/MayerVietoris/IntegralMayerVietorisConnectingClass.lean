import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralOpenMayerVietoris
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.Support.IntegralSupportCohomologyMV
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.HomologicalAlgebra.ModuleComplexConnecting

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralSupportCohomologyConnecting_class
    (K L : Set X) (hK : IsClosed K) (hL : IsClosed L) (q : Nat)
    (z : LinearMap.ker ((integralSupportCochains (K ∪ L)).sc' q (q + 1) (q + 2)).g.hom)
    (b : (integralSupportCochains K ⊞ integralSupportCochains L).X (q + 1))
    (hb : (integralSupportCochainSum K L).f (q + 1) b = z.val)
    (gamma : LinearMap.ker
      ((integralSupportCochains (K ∩ L)).sc' (q + 1) (q + 2) (q + 3)).g.hom)
    (hboundary : (integralSupportCochainDifference K L).f (q + 2) gamma.val =
      (integralSupportCochains K ⊞ integralSupportCochains L).d (q + 1) (q + 2) b) :
    integralSupportCohomologyConnecting K L hK hL (q + 1)
        (moduleComplexHomologyClass (integralSupportCochains (K ∪ L))
          q (q + 1) (q + 2) (by simp) (by simp) z) =
      moduleComplexHomologyClass (integralSupportCochains (K ∩ L))
        (q + 1) (q + 2) (q + 3) (by simp) (by simp) gamma := by
  let S := integralSupportDualSequence K L
  let hS := integralSupportDualSequence_shortExact' K L
  let F := integralDualMap (integralSupportComparison K L)
  let e := integralSupportCohomologyIntersectionIso K L hK hL (q + 2)
  let fgamma := moduleHomologyCycleMap
    ((shortComplexFunctor' (ModuleCat.{u} Int) (ComplexShape.up Nat)
      (q + 1) (q + 2) (q + 3)).map F) gamma
  have hb' : S.g.f (q + 1) b = z.val := by
    rw [integralSupportDualSequence_g]
    exact hb
  have hf : S.f.f (q + 2) fgamma.val = S.X₂.d (q + 1) (q + 2) b := by
    have h := congrArg (fun f => f.f (q + 2) gamma.val)
      (integralSupportDualComparison_f K L)
    exact h.trans hboundary
  have he := moduleComplexHomologyClass_connecting S hS
    q (q + 1) (q + 2) (q + 3) (by simp) rfl (by simp)
    z.val z.property b hb' fgamma.val fgamma.property hf
  have hn := moduleComplexHomologyClass_map F
    (q + 1) (q + 2) (q + 3) (by simp) (by simp) gamma
  have he' : hS.δ (q + 1) (q + 2) rfl
      (moduleComplexHomologyClass (integralSupportCochains (K ∪ L))
        q (q + 1) (q + 2) (by simp) (by simp) z) =
    e.hom (moduleComplexHomologyClass (integralSupportCochains (K ∩ L))
      (q + 1) (q + 2) (q + 3) (by simp) (by simp) gamma) := he.trans hn.symm
  change e.inv (hS.δ (q + 1) (q + 2) rfl _) = _
  rw [he', Iso.hom_inv_id_apply]

theorem integralOpenHomologyConnecting_class
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : Nat)
    (z : LinearMap.ker
      ((integralSmallChainComplex (integralBinaryCover U V)).sc' (n + 2) (n + 1) n).g.hom)
    (b : (integralChains U ⊞ integralChains V).X (n + 1))
    (hb : (integralOpenSum U V).f (n + 1) b = z.val)
    (a : LinearMap.ker ((integralChains ↥(U ∩ V)).sc' (n + 1) n (n - 1)).g.hom)
    (hboundary : (integralOpenDifference U V).f n a.val =
      (integralChains U ⊞ integralChains V).d (n + 1) n b) :
    integralOpenHomologyConnecting U V hU hV hcover n
        (homologyMap (integralSmallChainInclusion (integralBinaryCover U V)) (n + 1)
          (moduleComplexHomologyClass (integralSmallChainComplex (integralBinaryCover U V))
            (n + 2) (n + 1) n (by simp) (by simp) z)) =
      moduleComplexHomologyClass (integralChains ↥(U ∩ V))
        (n + 1) n (n - 1) (by simp) (by cases n <;> simp) a := by
  let S := integralOpenChainSequence U V
  let hS := integralOpenChainSequence_shortExact U V
  let e := integralOpenHomologyIso U V hU hV hcover (n + 1)
  change hS.δ (n + 1) n rfl (e.inv (e.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact moduleComplexHomologyClass_connecting S hS
    (n + 2) (n + 1) n (n - 1) (by simp) rfl (by cases n <;> simp)
    z.val z.property b hb a.val a.property hboundary

end Poincare.Topology
