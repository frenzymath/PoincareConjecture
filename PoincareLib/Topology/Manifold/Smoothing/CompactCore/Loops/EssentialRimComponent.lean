import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.SquareRimLoop
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Spheres.OriginalComponentSphere
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Spheres.OriginalSphereSimplyConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The whole component containing an actual essential rim

The connected image of the given rim selects a whole frontier component.
The same rim remains essential there, so that component is not an original
chartwise PL sphere. Its retained genus equation then has positive genus,
by the original zero-count sphere construction. See Wall019, lines 133--143.
-/

set_option autoImplicit false

open Set Metric Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1

/-- An actual essential square rim rules out an original PL sphere. -/
theorem not_chartwisePLSphere_of_essential_rim
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) {S : Set X}
    (gamma : C(Q, S))
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1) :
    ¬ Nonempty (ChartwisePLSphere e S) := by
  rintro ⟨sph⟩
  let : SimplyConnectedSpace S := sph.simplyConnectedSpace
  exact hessential (Subsingleton.elim _ _)

/-- Localize the given essential rim into one whole component, retaining
its exact ambient values. This applies in particular to a finite component
family; the localization itself does not require finiteness. -/
theorem exists_whole_component_essential_rim
    {X ι σ : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) {F : Set X}
    (S : σ → Set X) (hunion : (⋃ i, S i) = F)
    (hcomponent : ∀ i, ∀ x ∈ S i, connectedComponentIn F x = S i)
    (gamma : C(Q, F))
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1) :
    ∃ (i : σ) (gammaS : C(Q, S i)),
      (∀ u, (gamma u : X) ∈ S i) ∧
      (∀ u, (gammaS u : X) = (gamma u : X)) ∧
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gammaS.continuous)) ≠ 1 ∧
      ¬ Nonempty (ChartwisePLSphere e (S i)) := by
  let : ConnectedSpace Q :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere (by simp) 0 zero_le_one)
  have hbase : (gamma Dehn.squareRimBase : X) ∈ ⋃ i, S i :=
    hunion.symm ▸ (gamma Dehn.squareRimBase).property
  obtain ⟨i, hi⟩ := mem_iUnion.mp hbase
  let f : Q → X := fun u => gamma u
  have hf : Continuous f := continuous_subtype_val.comp gamma.continuous
  have hsub : range f ⊆ F := by
    rintro _ ⟨u, rfl⟩
    exact (gamma u).property
  have hSi : range f ⊆ S i := by
    rw [← hcomponent i _ hi]
    exact (isPreconnected_range hf).subset_connectedComponentIn
      (mem_range_self Dehn.squareRimBase) hsub
  have hvalues (u : Q) : (gamma u : X) ∈ S i := hSi (mem_range_self u)
  let gammaS : C(Q, S i) := ⟨fun u => ⟨gamma u, hvalues u⟩, hf.subtype_mk _⟩
  have hSF : S i ⊆ F := fun _ hx => hunion ▸ mem_iUnion.mpr ⟨i, hx⟩
  have hessentialS : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gammaS.continuous)) ≠ 1 := by
    intro hzero
    have hnull : (Dehn.squareRimLoop.map gammaS.continuous).Homotopic
        (Path.refl (gammaS Dehn.squareRimBase)) := Path.Homotopic.Quotient.exact hzero
    have hnullF : (Dehn.squareRimLoop.map gamma.continuous).Homotopic
        (Path.refl (gamma Dehn.squareRimBase)) :=
      hnull.map (ContinuousMap.inclusion hSF)
    exact hessential (Path.Homotopic.Quotient.eq.mpr hnullF)
  exact ⟨i, gammaS, hvalues, fun _ => rfl, hessentialS,
    not_chartwisePLSphere_of_essential_rim e gammaS hessentialS⟩

/-- The actual essential rim forces positivity of the retained genus count
of its original component model. -/
theorem original_component_genus_pos_of_essential_rim
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space)
    (c : A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {S : Set X} (himage : S = g '' (A.edgeComponentComplex c).space)
    (gamma : C(Q, S))
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1)
    (genus : ℕ)
    (hcount : Nat.card (A.edgeComponentComplex c).vertices +
      Nat.card (Triangle
        (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex) +
      2 * genus = Nat.card (Edge
        (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) :
    0 < genus := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hcount0 : Nat.card (A.edgeComponentComplex c).vertices +
      Nat.card (Triangle
        (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex) =
      Nat.card (Edge
        (A.edgeComponentComplex c).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2 := by
    simpa only [hzero, Nat.mul_zero, Nat.add_zero] using hcount
  have hsphere := exists_original_component_sphere_of_count K A hK hAK hg hgi
    hpure hcofaces hlinks c hcount0
  rw [← himage] at hsphere
  exact not_chartwisePLSphere_of_essential_rim e gamma hessential hsphere

end PoincareMT.M76
