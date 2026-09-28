import PoincareConjecture.Proofs.M02.Topology.ModuleHomologyNaturality



set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

variable {ι : Type v} {c : ComplexShape ι}

def moduleComplexHomologyClass
    (C : HomologicalComplex (ModuleCat.{u} Int) c)
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    (z : LinearMap.ker (C.sc' i j k).g.hom) : C.homology j :=
  (C.homologyIsoSc' i j k hi hk).inv (moduleHomologyClass (C.sc' i j k) z)

theorem moduleComplexHomologyClass_surjective
    (C : HomologicalComplex (ModuleCat.{u} Int) c)
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    Function.Surjective (moduleComplexHomologyClass C i j k hi hk) := by
  intro a
  obtain ⟨z, hz⟩ := moduleHomologyClass_surjective (C.sc' i j k)
    ((C.homologyIsoSc' i j k hi hk).hom a)
  refine ⟨z, ?_⟩
  exact (congrArg (C.homologyIsoSc' i j k hi hk).inv.hom hz).trans
    ((C.homologyIsoSc' i j k hi hk).hom_inv_id_apply a)

theorem moduleComplexHomologyClass_map
    {C D : HomologicalComplex (ModuleCat.{u} Int) c} (f : C ⟶ D)
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    (z : LinearMap.ker (C.sc' i j k).g.hom) :
    homologyMap f j (moduleComplexHomologyClass C i j k hi hk z) =
      moduleComplexHomologyClass D i j k hi hk
        (moduleHomologyCycleMap ((shortComplexFunctor' (ModuleCat.{u} Int) c i j k).map f) z) := by
  have hn := (homologyFunctorIso' (ModuleCat.{u} Int) c i j k hi hk).inv.naturality f
  change ShortComplex.homologyMap
      ((shortComplexFunctor' (ModuleCat.{u} Int) c i j k).map f) ≫
      (D.homologyIsoSc' i j k hi hk).inv =
    (C.homologyIsoSc' i j k hi hk).inv ≫ homologyMap f j at hn
  have he := congrArg (fun g => g.hom (moduleHomologyClass (C.sc' i j k) z)) hn
  have hm := moduleHomologyClass_map
    ((shortComplexFunctor' (ModuleCat.{u} Int) c i j k).map f) z
  exact he.symm.trans (congrArg (D.homologyIsoSc' i j k hi hk).inv.hom hm)

end PoincareConjecture.Proofs.M02.Topology
