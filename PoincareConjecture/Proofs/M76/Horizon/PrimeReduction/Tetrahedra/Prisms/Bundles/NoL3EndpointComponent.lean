import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalSphericalComponentModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismTrimComponentTransport

set_option autoImplicit false
open Set Metric Geometry CategoryTheory Limits
universe u v

namespace PoincareConjecture.M76.PrismBelt

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem endpoint_component_invariant_of_noL3
    {X E ι ν η : Type*} [TopologicalSpace X] [T2Space X] [Finite ν] [Finite η]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R Qcut : Set X}
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFg : ∀ x ∈ K.space, F (g x) = x)
    (hQ : IsCompact Qcut) (hPL : PLDomain e Qcut)
    (hno : HasNoPuncturedSphereComponents e F Qcut)
    (S : ν → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier Qcut = frontier R ∪ ⋃ i, S i)
    {A B : η → Set E} {V : Set E}
    (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i) (hH : ∀ i, (H i).IsFinitePL)
    (L : C((⋃ i, B i) × I, (⋃ i, B i)))
    (hL : ∀ i (x : B i) (t : I), (L (⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩, t) : E) =
      prismFiberInterpolation (H i) x t)
    (hpair : ∀ i j (x : E) (hi : x ∈ B i) (hj : x ∈ B j),
      prismFiberEndPair (H i) ⟨x, hi⟩ = prismFiberEndPair (H j) ⟨x, hj⟩)
    (τ : (⋃ i, prismEnds (H i)) ≃ₜ (⋃ i, prismEnds (H i)))
    (hτ : Function.Involutive τ)
    (hτends : ∀ i (x : A i) (b : Bool),
      (τ (prismEndpointLift H i x b) : E) = prismEndMap (H i) x (!b))
    (T : (⋃ i, B i) ≃ₜ V) (hT : T.IsFinitePL)
    (p : (⋃ i, prismEnds (H i) : Set E))
    (P : sphere (0 : V3) 1 ≃ₜ connectedComponentIn (⋃ i, prismEnds (H i)) (p : E))
    (hP : P.IsFinitePL)
    (hNK : connectedComponentIn V (T (prismEndpointInclusion H p) : E) ⊆ K.space)
    (hNint : MapsTo g (connectedComponentIn V (T (prismEndpointInclusion H p) : E))
      (interior R))
    {x : X} (hx : x ∈ Qcut)
    (hcontain : connectedComponentIn Qcut x ⊆
      g '' connectedComponentIn V (T (prismEndpointInclusion H p) : E)) :
    τ p ∈ connectedComponent p := by
  by_contra hp
  obtain ⟨U, hU, _⟩ := exists_transported_finitePL_exchanged_prism_component
    H hH L hL hpair τ hτ hτends T hT p hp
  exact not_finitePL_spherical_product_containing_noL3_component K g hg hgi F hF hFg
    hQ hPL hno S sS hSdis hfront hNK hNint P hP U hU hx hcontain

theorem endpoint_component_homology_retract_of_noL3
    {X : Type v} {E : Type u} {ι ν η : Type*} [TopologicalSpace X] [T2Space X] [Finite ν] [Finite η]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R Qcut : Set X}
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFg : ∀ x ∈ K.space, F (g x) = x)
    (hQ : IsCompact Qcut) (hPL : PLDomain e Qcut)
    (hno : HasNoPuncturedSphereComponents e F Qcut)
    (S : ν → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier Qcut = frontier R ∪ ⋃ i, S i)
    {A B : η → Set E} {V : Set E}
    (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i) (hH : ∀ i, (H i).IsFinitePL)
    (L : C((⋃ i, B i) × I, (⋃ i, B i)))
    (hL : ∀ i (x : B i) (t : I), (L (⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩, t) : E) =
      prismFiberInterpolation (H i) x t)
    (hpair : ∀ i j (x : E) (hi : x ∈ B i) (hj : x ∈ B j),
      prismFiberEndPair (H i) ⟨x, hi⟩ = prismFiberEndPair (H j) ⟨x, hj⟩)
    (τ : (⋃ i, prismEnds (H i)) ≃ₜ (⋃ i, prismEnds (H i)))
    (hτ : Function.Involutive τ)
    (hτends : ∀ i (x : A i) (b : Bool),
      (τ (prismEndpointLift H i x b) : E) = prismEndMap (H i) x (!b))
    (W : TwistedInvolutionInterval.Model τ hτ ≃ₜ (⋃ i, B i))
    (hW : ∀ p, W (TwistedInvolutionInterval.boundaryMap τ hτ p) =
      prismEndpointInclusion H p)
    (T : (⋃ i, B i) ≃ₜ V) (hT : T.IsFinitePL)
    (p : (⋃ i, prismEnds (H i) : Set E))
    (P : sphere (0 : V3) 1 ≃ₜ connectedComponentIn (⋃ i, prismEnds (H i)) (p : E))
    (hP : P.IsFinitePL)
    (hNK : connectedComponentIn V (T (prismEndpointInclusion H p) : E) ⊆ K.space)
    (hNint : MapsTo g (connectedComponentIn V (T (prismEndpointInclusion H p) : E))
      (interior R))
    {x : X} (hx : x ∈ Qcut)
    (hcontain : connectedComponentIn Qcut x ⊆
      g '' connectedComponentIn V (T (prismEndpointInclusion H p) : E))
    (Rmod : ModuleCat.{u} (ZMod 2)) [Nontrivial Rmod] :
    ∃ (i : Rmod ⟶ (TopCat.toSSet.obj
        (TopCat.of (connectedComponentIn (⋃ i, B i) (p : E)))).homology Rmod 1)
      (r : (TopCat.toSSet.obj
        (TopCat.of (connectedComponentIn (⋃ i, B i) (p : E)))).homology Rmod 1 ⟶ Rmod),
      i ≫ r = 𝟙 Rmod ∧ ¬ IsZero ((TopCat.toSSet.obj
        (TopCat.of (connectedComponentIn (⋃ i, B i) (p : E)))).homology Rmod 1) := by
  have hp := endpoint_component_invariant_of_noL3 K g hg hgi F hF hFg hQ hPL hno
    S sS hSdis hfront H hH L hL hpair τ hτ hτends T hT p P hP hNK hNint hx hcontain
  have hfree : ∀ q, τ q ≠ q := by
    intro q
    obtain ⟨i, ⟨⟨a, b⟩, hq⟩⟩ := mem_iUnion.mp q.property
    have hq' : q = prismEndpointLift H i a b := Subtype.ext hq.symm
    intro heq
    have hv := congrArg Subtype.val heq
    rw [hq', hτends] at hv
    exact prismEndMap_flip_ne (H i) a b (Subtype.ext hv)
  obtain ⟨i,r,hir⟩ := endpoint_invariant_component_homology_retract
    H hH τ hτ W hW hfree p hp Rmod
  refine ⟨i,r,hir,?_⟩
  intro hzero
  have hi : i = 0 := hzero.eq_of_tgt i 0
  have hid : 𝟙 Rmod = 0 := hir.symm.trans (by rw [hi, zero_comp])
  have : Subsingleton Rmod := ModuleCat.isZero_iff_subsingleton.mp
    ((IsZero.iff_id_eq_zero Rmod).mpr hid)
  exact false_of_nontrivial_of_subsingleton Rmod

end PoincareConjecture.M76.PrismBelt
