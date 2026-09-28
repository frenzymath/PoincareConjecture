import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.HomologicalAlgebra.ModuleComplexHomologyClass
import Mathlib.Algebra.Homology.ConcreteCategory

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u v

namespace Poincare.Topology

variable {ι : Type v} {c : ComplexShape ι}

theorem moduleComplexHomologyClass_eq_cyclesMk
    (C : HomologicalComplex (ModuleCat.{u} Int) c)
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    (z : LinearMap.ker (C.sc' i j k).g.hom) :
    moduleComplexHomologyClass C i j k hi hk z =
      C.homologyπ j (C.cyclesMk z.val k hk z.property) := by
  subst i k
  simp only [moduleComplexHomologyClass, homologyIsoSc'_eq_refl, Iso.refl_inv]
  rw [moduleHomologyClass_eq]
  apply congrArg (C.homologyπ j)
  apply (ModuleCat.mono_iff_injective (C.iCycles j)).mp inferInstance
  have h := congrArg (fun f => f z) (C.sc j).moduleCatCyclesIso_inv_iCycles
  exact h.trans (C.i_cyclesMk z.val _ rfl z.property).symm

theorem moduleComplexHomologyClass_connecting
    (S : ShortComplex (HomologicalComplex (ModuleCat.{u} Int) c))
    (hS : S.ShortExact) (a i j k : ι) (hi : c.prev i = a)
    (hij : c.Rel i j) (hk : c.next j = k)
    (z : S.X₃.X i) (hz : S.X₃.d i j z = 0)
    (b : S.X₂.X i) (hb : S.g.f i b = z)
    (v : S.X₁.X j) (hv : S.X₁.d j k v = 0)
    (hboundary : S.f.f j v = S.X₂.d i j b) :
    hS.δ i j hij
        (moduleComplexHomologyClass S.X₃ a i j hi (c.next_eq' hij) ⟨z, hz⟩) =
      moduleComplexHomologyClass S.X₁ i j k (c.prev_eq' hij) hk ⟨v, hv⟩ := by
  rw [moduleComplexHomologyClass_eq_cyclesMk, moduleComplexHomologyClass_eq_cyclesMk]
  exact hS.δ_apply i j hij z hz b hb v hboundary k hk

end Poincare.Topology
