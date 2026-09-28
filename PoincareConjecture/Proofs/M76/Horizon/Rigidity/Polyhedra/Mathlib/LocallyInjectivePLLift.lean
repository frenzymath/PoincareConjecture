import Mathlib.Topology.SeparatedMap
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse

set_option autoImplicit false

open Set

namespace Geometry

variable {E F G X ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace X]

theorem PolyhedralPLInCharts.finitePiecewiseAffineOn_lift_of_locallyInjective
    {e : ι → OpenPartialHomeomorph X F}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {f : E → X} (P : SimplicialComplex ℝ E) (hP : P.faces.Finite)
    (hf : PolyhedralPLInCharts e f P.space)
    (hinj : IsLocallyInjective (fun x : P.space => f x))
    (K : SimplicialComplex ℝ G) (hK : K.faces.Finite)
    {q : G → E} (hq : ContinuousOn q K.space)
    (hqP : MapsTo q K.space P.space)
    (hfq : PolyhedralPLInCharts e (f ∘ q) K.space) :
    FinitePiecewiseAffineOn q K.space := by
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  let qP : K.space → P.space := fun y => ⟨q y, hqP y.property⟩
  have hqPc : Continuous qP := hq.domRestrict.subtype_mk _
  obtain ⟨U, hU, hqxU, hfU⟩ := hinj (qP x)
  obtain ⟨P₀, W, hP₀, hP₀P, hW, hqxW, hWP₀, hP₀U⟩ :=
    P.exists_relative_polyhedral_neighborhood hP (qP x) hU hqxU
  have hfP₀ : InjOn f P₀.space := by
    intro y hy z hz heq
    exact congrArg Subtype.val (hfU
      (hP₀U (show (⟨y, hP₀P hy⟩ : P.space) ∈ Subtype.val ⁻¹' P₀.space from hy))
      (hP₀U (show (⟨z, hP₀P hz⟩ : P.space) ∈ Subtype.val ⁻¹' P₀.space from hz))
      heq)
  obtain ⟨N, V, hN, hNK, hV, hxV, hVN, hNW⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x (hW.preimage hqPc) hqxW
  have hqN : MapsTo q N.space P₀.space := by
    intro y hy
    exact hWP₀ ⟨qP ⟨y, hNK hy⟩,
      hNW (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy), rfl⟩
  have hlift := (hf.restrict_finite P₀ hP₀ hP₀P).finitePiecewiseAffineOn_lift
    hcompat hfP₀ N hN (hq.mono hNK) hqN (hfq.restrict_finite N hN hNK)
  obtain ⟨L, hL, hLN, hqL⟩ := hlift
  exact ⟨L, V, hL, hV, hxV, fun y hy => hLN.symm.subset (hVN hy), hqL⟩

end Geometry
