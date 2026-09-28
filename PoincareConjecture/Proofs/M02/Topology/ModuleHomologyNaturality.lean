import PoincareConjecture.Proofs.M02.Topology.ModuleBilinearHomology
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

set_option autoImplicit false

open CategoryTheory

universe u

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

def moduleHomologyCycleMap {S T : ShortComplex (ModuleCat.{u} Int)} (f : S ⟶ T)
    (z : LinearMap.ker S.g.hom) : LinearMap.ker T.g.hom :=
  ⟨f.τ₂ z.val, by
    have h := congrArg (fun k => k z.val) f.comm₂₃
    change T.g (f.τ₂ z.val) = f.τ₃ (S.g z.val) at h
    rw [show S.g z.val = 0 from z.property, map_zero] at h
    exact h⟩

theorem moduleHomologyClass_eq (S : ShortComplex (ModuleCat.{u} Int))
    (z : LinearMap.ker S.g.hom) :
    moduleHomologyClass S z = S.homologyπ (S.moduleCatCyclesIso.inv z) :=
  (congrArg (fun f => f z) S.moduleCatCyclesIso_inv_π).symm

theorem moduleHomologyClass_map {S T : ShortComplex (ModuleCat.{u} Int)}
    (f : S ⟶ T) (z : LinearMap.ker S.g.hom) :
    ShortComplex.homologyMap f (moduleHomologyClass S z) =
      moduleHomologyClass T (moduleHomologyCycleMap f z) := by
  have hz : T.moduleCatCyclesIso.hom
      (ShortComplex.cyclesMap f (S.moduleCatCyclesIso.inv z)) =
      moduleHomologyCycleMap f z := by
    apply Subtype.ext
    have hi := congrArg (fun k => k (S.moduleCatCyclesIso.inv z))
      (ShortComplex.cyclesMap_i f)
    change T.iCycles (ShortComplex.cyclesMap f (S.moduleCatCyclesIso.inv z)) =
      f.τ₂ (S.iCycles (S.moduleCatCyclesIso.inv z)) at hi
    have hs := congrArg (fun k => k z) S.moduleCatCyclesIso_inv_iCycles
    have ht := congrArg (fun k => k (ShortComplex.cyclesMap f (S.moduleCatCyclesIso.inv z)))
      T.moduleCatCyclesIso_hom_i
    exact ht.trans (hi.trans (congrArg f.τ₂ hs))
  rw [moduleHomologyClass_eq, moduleHomologyClass_eq]
  have h := congrArg (fun k => k (S.moduleCatCyclesIso.inv z))
    (ShortComplex.homologyπ_naturality f)
  change ShortComplex.homologyMap f (S.homologyπ (S.moduleCatCyclesIso.inv z)) =
    T.homologyπ (ShortComplex.cyclesMap f (S.moduleCatCyclesIso.inv z)) at h
  rw [← hz]
  simpa only [Iso.hom_inv_id_apply] using h

theorem complexHomologyClass_map {ι : Type*} {c : ComplexShape ι}
    {C D : HomologicalComplex (ModuleCat.{u} Int) c} (f : C ⟶ D) (n : ι)
    (z : LinearMap.ker (C.sc n).g.hom) :
    HomologicalComplex.homologyMap f n (moduleHomologyClass (C.sc n) z) =
      moduleHomologyClass (D.sc n)
        (moduleHomologyCycleMap ((HomologicalComplex.shortComplexFunctor
          (ModuleCat.{u} Int) c n).map f) z) :=
  moduleHomologyClass_map _ z

end

end PoincareConjecture.Proofs.M02.Topology
