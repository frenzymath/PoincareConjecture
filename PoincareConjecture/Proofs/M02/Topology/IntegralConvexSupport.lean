import PoincareConjecture.Proofs.M02.Topology.CompactConvexComplement
import PoincareConjecture.Proofs.M02.Topology.IntegralSupportMayerVietoris
import PoincareConjecture.Proofs.M02.Topology.IntegralSphereVanishing
import PoincareConjecture.Proofs.M02.Topology.IntegralSphereBase










set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]

theorem integralCompactConvexSupportRestriction_quasiIso
    (K : Set E) (hK : IsCompact K) (hconv : Convex Real K)
    (x : E) (hx : x ∈ K) :
    QuasiIso (integralSupportRestriction (Set.singleton_subset_iff.mpr hx)) := by
  let O : Set E := Kᶜ
  let P : Set E := {x}ᶜ
  let incl : integralChains O ⟶ integralChains P := integralChainsFunctor.map
    (TopCat.ofHom (compactConvexComplementInclusion K x hx))
  have hI : QuasiIso incl := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    change IsIso (integralHomologyIsoOfHomotopyEquiv
      (compactConvexComplementPunctureHomotopyEquiv K hK hconv x hx) n).hom
    infer_instance
  let F : integralPairSequence O ⟶ integralPairSequence P :=
    { τ₁ := incl
      τ₂ := 𝟙 (integralChains E)
      τ₃ := integralSupportRestriction (Set.singleton_subset_iff.mpr hx)
      comm₁₂ := by
        change incl ≫ integralSubspaceChains P = integralSubspaceChains O ≫ 𝟙 _
        rw [Category.comp_id]
        dsimp only [incl, integralSubspaceChains]
        rw [← Functor.map_comp]
        rfl
      comm₂₃ := by
        change 𝟙 _ ≫ integralRelativeProjection P =
          integralRelativeProjection O ≫ integralSupportRestriction _
        rw [Category.id_comp, integralSupportRestriction_projection] }
  exact HomologySequence.quasiIso_τ₃ F
    (integralPairSequence_shortExact O) (integralPairSequence_shortExact P) hI
      (by change QuasiIso (𝟙 (integralChains E)); infer_instance)

theorem integralCompactConvexSupportRestriction_homology_isIso
    (K : Set E) (hK : IsCompact K) (hconv : Convex Real K)
    (x : E) (hx : x ∈ K) (n : Nat) :
    IsIso (integralSupportHomologyRestriction (Set.singleton_subset_iff.mpr hx) n) := by
  let := integralCompactConvexSupportRestriction_quasiIso K hK hconv x hx
  change IsIso (homologyMap (integralSupportRestriction _) n)
  infer_instance

def integralEuclideanCompactConvexSupportThreeIso
    (K : Set (EuclideanSpace Real (Fin 3))) (hK : IsCompact K)
    (hconv : Convex Real K) (x : EuclideanSpace Real (Fin 3)) (hx : x ∈ K) :
    integralSupportHomology K 3 ≅ integralCoefficient :=
  integralContractibleAmbientRelativeBoundaryIso Kᶜ 1 ≪≫
    integralHomologyIsoOfHomotopyEquiv
      ((compactConvexComplementPunctureHomotopyEquiv K hK hconv x hx).trans
        ((punctureTranslationHomeomorph x).toHomotopyEquiv.trans
          (puncturedSpaceSphereHomotopyEquiv (EuclideanSpace Real (Fin 3))))) 2 ≪≫
    integralSphereH2Iso

theorem integralEuclideanCompactConvexSupportAbove_isZero
    (K : Set (EuclideanSpace Real (Fin 3))) (hK : IsCompact K)
    (hconv : Convex Real K) (x : EuclideanSpace Real (Fin 3)) (hx : x ∈ K) (n : Nat) :
    IsZero (integralSupportHomology K (n + 4)) :=
  (integralSphereS2HomologyAbove_isZero n).of_iso
    (integralContractibleAmbientRelativeBoundaryIso Kᶜ (n + 2) ≪≫
      integralHomologyIsoOfHomotopyEquiv
        ((compactConvexComplementPunctureHomotopyEquiv K hK hconv x hx).trans
          ((punctureTranslationHomeomorph x).toHomotopyEquiv.trans
            (puncturedSpaceSphereHomotopyEquiv (EuclideanSpace Real (Fin 3))))) (n + 3))

end PoincareConjecture.Proofs.M02.Topology
