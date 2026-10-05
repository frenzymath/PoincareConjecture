import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.FiniteComplexHomologyCoefficients
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.OrderComplexLiftComparison
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.FiniteLiftChains
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.HomologyTrace
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.OrderComplexMapImage

/-!
# Finite mod-two singular homology of finite geometric complexes

The positive face-center homeomorphism gives a finite order model of the
literal carrier. The constructed singular comparison, followed by change
of coefficients, gives finite singular homology in every degree.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open scoped Simplicial BigOperators

universe u

namespace PoincareMT.M76.FiniteComplexHomology

open PoincareMT.Proofs.M02.Topology PoincareMT.Proofs.M59

set_option backward.isDefEq.respectTransparency false in
/-- A compact cover of a finite order complex has finite actual mod-two
singular homology, using the constructed lifted characteristic comparison. -/
theorem finite_modTwo_homology_of_order_complex_cover
    {J : Type u} [PartialOrder J] [Fintype J]
    {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (p : C(X, (finiteOrderComplex J).space)) (hp : IsCoveringMap p) (n : ℕ) :
    Module.Finite (ZMod 2)
      (SSet.homology (C := ModuleCat.{u} (ZMod 2)) (TopCat.toSSet.obj (TopCat.of X))
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) n) := by
  let A := singularLiftSSet p (nerve J) (orderComplexSingular J)
  let coeff := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
  let hdegree (k : ℕ) : Finite (A _⦋k⦌) := by
    let := finite_nerve_degree J k
    exact singularLift_finite p (nerve J) (orderComplexSingular J) hp k
  let hchains (k : ℕ) : Module.Finite (ZMod 2) ((A.chainComplex coeff).X k) :=
    chainModuleFinite A coeff k
  let := ChainComplex.moduleFinite_homology (C := A.chainComplex coeff) n
  obtain ⟨e⟩ := modTwo_homotopyEquiv_of_integral_quasiIso
    (singularLiftProjection p (nerve J) (orderComplexSingular J))
    (orderComplexSingularLift_quasiIso p hp)
  exact Module.Finite.equiv (asIso (homologyMap e.hom n)).toLinearEquiv

/-- Every finite geometric complex has finite mod-two singular homology
on its actual carrier, in every degree. -/
theorem finite_modTwo_homology
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) (n : ℕ) :
    Module.Finite (ZMod 2)
      (SSet.homology (C := ModuleCat.{u} (ZMod 2)) (TopCat.toSSet.obj (TopCat.of K.space))
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) n) := by
  classical
  let := hK.fintype
  let c (s : K.faces) := ∑ v ∈ s.val, (s.val.card : ℝ)⁻¹ • v
  have hc (s : K.faces) : ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
      (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s := by
    have hs : 0 < (s.val.card : ℝ) := by
      exact_mod_cast (K.nonempty_of_mem_faces s.property).card_pos
    refine ⟨fun _ => (s.val.card : ℝ)⁻¹, fun _ _ => inv_pos.mpr hs, ?_, rfl⟩
    simp [ne_of_gt hs]
  let e : (finiteOrderComplex K.faces).space ≃ₜ K.space :=
    (geometricFlagHomeomorphRange K Subtype.val (fun s => s.property)
      (fun _ _ => Iff.rfl) c hc).trans
        (Homeomorph.setCongr (K.range_faceOrderComplexMap c hc))
  let : CompactSpace (finiteOrderComplex K.faces).space :=
    isCompact_iff_compactSpace.mp finiteOrderComplex_space_isCompact
  let : CompactSpace K.space := e.compactSpace
  exact finite_modTwo_homology_of_order_complex_cover
    ⟨e.symm, e.symm.continuous⟩
    (isLocalHomeomorph_iff_isCoveringMap.mp e.symm.isLocalHomeomorph) n

end PoincareMT.M76.FiniteComplexHomology
