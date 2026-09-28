import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

theorem exists_continuous_section_of_contractible [ContractibleSpace X]
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    ∃ s : C(X, E), ∀ x, p (s x) = x := by
  obtain ⟨x₀, ⟨H⟩⟩ := id_nullhomotopic X
  obtain ⟨y₀, hy₀⟩ := hsurj x₀
  let f : C(X, E) := ContinuousMap.const X y₀
  have hzero : ∀ x, H.symm (0, x) = p (f x) :=
    fun x => (H.symm.apply_zero x).trans hy₀.symm
  let G := hp.liftHomotopy H.symm.toContinuousMap f hzero
  let s : C(X, E) := ⟨fun x => G (1, x),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨s, fun x => ?_⟩
  exact (congrFun (hp.liftHomotopy_lifts H.symm.toContinuousMap f hzero) (1, x)).trans
    (H.symm.apply_one x)

theorem exists_continuous_section_of_simplyConnected
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    ∃ s : C(X, E), ∀ x, p (s x) = x := by
  classical
  let x₀ : X := Classical.arbitrary X
  obtain ⟨y₀, hy₀⟩ := hsurj x₀
  obtain ⟨s, ⟨_, hs⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts (ContinuousMap.id X) x₀ y₀ hy₀
  exact ⟨s, fun x => congrFun hs x⟩

theorem injective_of_continuous_section [PreconnectedSpace E]
    (hp : IsCoveringMap p) (s : C(X, E)) (hs : ∀ x, p (s x) = x) (x₀ : X) :
    Function.Injective p := by
  have heq : (fun y => s (p y)) = id := by
    apply hp.eq_of_comp_eq (s.continuous.comp hp.continuous) continuous_id
      (a := s x₀)
    · exact funext fun y => hs (p y)
    · exact congrArg s (hs x₀)
  have hinverse : Function.LeftInverse s p := fun y => congrFun heq y
  exact hinverse.injective

end IsCoveringMap
