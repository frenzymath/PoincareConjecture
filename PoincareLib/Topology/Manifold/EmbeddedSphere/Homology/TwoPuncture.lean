import PoincareLib.Topology.Manifold.EmbeddedSphere.Cylinder.TwoPuncture
import PoincareLib.AlgebraicTopology.SingularHomology.Relative.IntegralConvexSupport

/-!
# Relative homology comparison with two point supports

The actual relative restriction from the plane-plus-exterior pair to the
two-puncture pair is a quasi-isomorphism. Compare the pair sequences using
the explicit homotopy equivalence on subspaces and the ambient identity.
This is Hatcher, Theorem 2.16 and Proposition 2.19, pp. 117-118, applied to
M53 derivation 07 for the repair of Morgan--Tian, Proposition 15.12 and
Remark 15.13, p. 365.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open Poincare.Topology

universe u

namespace PoincareMT.Topology.EmbeddedSphere

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The canonical relative restriction to the two point supports is a
quasi-isomorphism. Source: Hatcher, pp. 117-118, and M53 derivation 07. -/
theorem planeExterior_twoPuncture_quasiIso
    (K : Set (E × ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (c : ℝ) (hc : 0 < c) (hp : ((0 : E), c) ∈ K) (hm : ((0 : E), -c) ∈ K) :
    QuasiIso (integralRelativeRestriction
      (planeExterior_subset_twoPuncture K c hc hp hm)) := by
  let A : Set (E × ℝ) := {y | y.2 = 0} ∪ Kᶜ
  let Q : Set (E × ℝ) := ({((0 : E), c)} ∪ {(0, -c)})ᶜ
  let incl := integralChainsFunctor.map
    (TopCat.ofHom (planeExteriorPunctureInclusion K c hc hp hm))
  have hincl : QuasiIso incl := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    change IsIso (integralHomologyIsoOfHomotopyEquiv
      (planeExteriorPunctureHomotopyEquiv K hK hconv c hc hp hm) n).hom
    infer_instance
  let T : integralPairSequence A ⟶ integralPairSequence Q :=
    { τ₁ := incl
      τ₂ := 𝟙 _
      τ₃ := integralRelativeRestriction (planeExterior_subset_twoPuncture K c hc hp hm)
      comm₁₂ := by
        change incl ≫ integralSubspaceChains Q = integralSubspaceChains A ≫ 𝟙 _
        rw [Category.comp_id]
        dsimp only [incl, integralSubspaceChains]
        rw [← CategoryTheory.Functor.map_comp]
        rfl
      comm₂₃ := by
        change 𝟙 _ ≫ integralRelativeProjection Q = integralRelativeProjection A ≫
          integralRelativeRestriction (planeExterior_subset_twoPuncture K c hc hp hm)
        rw [Category.id_comp, integralRelativeRestriction_projection] }
  exact HomologySequence.quasiIso_τ₃ T (integralPairSequence_shortExact A)
    (integralPairSequence_shortExact Q) hincl
    (by change QuasiIso (𝟙 (integralChains (E × ℝ))); infer_instance)

/-- In each degree the actual restriction to two punctures is an integral
homology isomorphism. Source: M53 derivation 07 and Hatcher, pp. 117-118. -/
theorem planeExterior_twoPuncture_homology_isIso
    (K : Set (E × ℝ)) (hK : IsCompact K) (hconv : Convex ℝ K)
    (c : ℝ) (hc : 0 < c) (hp : ((0 : E), c) ∈ K) (hm : ((0 : E), -c) ∈ K) (n : Nat) :
    IsIso (homologyMap (integralRelativeRestriction
      (planeExterior_subset_twoPuncture K c hc hp hm)) n) := by
  let := planeExterior_twoPuncture_quasiIso K hK hconv c hc hp hm
  infer_instance

end PoincareMT.Topology.EmbeddedSphere
