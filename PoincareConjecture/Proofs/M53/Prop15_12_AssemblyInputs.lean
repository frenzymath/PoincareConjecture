import PoincareConjecture.Proofs.M53.Prop15_12_LocalParity
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Set
open PoincareConjecture.Proofs.M02.Topology

universe u

namespace PoincareConjecture.Proofs.M53

theorem nonempty_integralThreePointHomology_equiv_int
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 3) (x : V) :
    Nonempty (integralSupportHomology ({x} : Set V) 3 ≃+ ℤ) := by
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim)
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) V := e.symm.toHomeomorph.chartedSpace
  obtain ⟨A⟩ := exists_integralThreeLocalHomologyAtlas (X := V)
  exact ⟨(A.localFrame x x (A.mem_baseSet x)).symm.toAddEquiv⟩

theorem even_threeManifoldRelativeRestriction_iff_of_isPreconnected
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (S : Set X) (hS : IsPreconnected Sᶜ) (a : integralRelativeHomology S 3)
    {x y : X} (hx : S ⊆ ({x}ᶜ : Set X)) (hy : S ⊆ ({y}ᶜ : Set X)) :
    Even (homologyMap (integralRelativeRestriction hx) 3 a) ↔
      Even (homologyMap (integralRelativeRestriction hy) 3 a) := by
  classical
  generalize hK : Sᶜ = K at hS
  have hSK : S = Kᶜ := by rw [← hK, compl_compl]
  subst S
  have hxK : x ∈ K := by
    by_contra hn
    exact hx hn rfl
  have hyK : y ∈ K := by
    by_contra hn
    exact hy hn rfl
  exact even_threeManifoldSupportRestriction_iff_of_isPreconnected K hS a hxK hyK

end PoincareConjecture.Proofs.M53
