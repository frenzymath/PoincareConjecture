import PoincareConjecture.Proofs.M02.Topology.IntegralBallSupport

set_option autoImplicit false

open CategoryTheory Limits Metric HomologicalComplex
open scoped Topology ContinuousMap unitInterval

universe u

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]

def closedBallComplementPointInclusion (c : E) (r : Real)
    (x : E) (hx : x ∈ closedBall c r) :
    C(((closedBall c r)ᶜ : Set E), ({x}ᶜ : Set E)) :=
  ⟨fun z => ⟨z.val, fun h => z.property (h ▸ hx)⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem closedBallComplementPointInclusion_homology_isIso
    (c : E) (r : Real) (hr : 0 ≤ r)
    (x : E) (hx : x ∈ closedBall c r) (n : Nat) :
    IsIso (homologyMap (integralChainsFunctor.map
      (TopCat.ofHom (closedBallComplementPointInclusion c r x hx))) n) := by
  let O : Set E := (closedBall c r)ᶜ
  let P : Set E := {0}ᶜ
  let ic := closedBallComplementInclusion c r hr
  let ix := closedBallComplementPointInclusion c r x hx
  let tc : C(({c}ᶜ : Set E), P) := punctureTranslationHomeomorph c
  let tx : C(({x}ᶜ : Set E), P) := punctureTranslationHomeomorph x
  have hmem (t : unitInterval) : AffineMap.lineMap c x (t : Real) ∈ closedBall c r :=
    (convex_closedBall c r).lineMap_mem (mem_closedBall_self hr) hx t.property
  have hnonzero (z : unitInterval × O) :
      z.2.val - AffineMap.lineMap c x (z.1 : Real) ∈ P := by
    intro h
    have he : z.2.val = AffineMap.lineMap c x (z.1 : Real) := sub_eq_zero.mp h
    exact z.2.property (he ▸ hmem z.1)
  let H : (tc.comp ic).Homotopy (tx.comp ix) :=
    { toFun := fun z => ⟨z.2.val - AffineMap.lineMap c x (z.1 : Real), hnonzero z⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        simp only [AffineMap.lineMap_apply_module]
        fun_prop
      map_zero_left z := Subtype.ext (by
        change z.val - AffineMap.lineMap c x 0 = z.val - c
        rw [AffineMap.lineMap_apply_zero])
      map_one_left z := Subtype.ext (by
        change z.val - AffineMap.lineMap c x 1 = z.val - x
        rw [AffineMap.lineMap_apply_one]) }
  let Ic := integralChainsFunctor.map (TopCat.ofHom ic)
  let Ix := integralChainsFunctor.map (TopCat.ofHom ix)
  let Tc := integralChainsFunctor.map (TopCat.ofHom tc)
  let Tx := integralChainsFunctor.map (TopCat.ofHom tx)
  have hIc : IsIso (homologyMap Ic n) := by
    change IsIso (integralHomologyIsoOfHomotopyEquiv
      (closedBallComplementPunctureHomotopyEquiv c r hr) n).hom
    infer_instance
  have hTc : IsIso (homologyMap Tc n) := by
    change IsIso (integralHomeomorphHomologyIso (punctureTranslationHomeomorph c) n).hom
    infer_instance
  have hTx : IsIso (homologyMap Tx n) := by
    change IsIso (integralHomeomorphHomologyIso (punctureTranslationHomeomorph x) n).hom
    infer_instance
  let HT : TopCat.Homotopy
      (TopCat.ofHom ic ≫ TopCat.ofHom tc) (TopCat.ofHom ix ≫ TopCat.ofHom tx) := H
  have heq := HT.congr_homologyMap_singularChainComplexFunctor integralCoefficient n
  change homologyMap (integralChainsFunctor.map (TopCat.ofHom ic ≫ TopCat.ofHom tc)) n =
    homologyMap (integralChainsFunctor.map (TopCat.ofHom ix ≫ TopCat.ofHom tx)) n at heq
  rw [Functor.map_comp, Functor.map_comp, homologyMap_comp, homologyMap_comp] at heq
  have hcomp : IsIso (homologyMap Ix n ≫ homologyMap Tx n) := by
    rw [← heq]
    exact IsIso.comp_isIso' hIc hTc
  let := hTx
  let := hcomp
  exact IsIso.of_isIso_comp_right (homologyMap Ix n) (homologyMap Tx n)

def integralBallLocalRestriction (c : E) (r : Real)
    (x : E) (hx : x ∈ closedBall c r) :
    integralRelativeChains ((closedBall c r)ᶜ : Set E) ⟶
      integralRelativeChains ({x}ᶜ : Set E) :=
  integralRelativeMap (ContinuousMap.id E)
    (show Set.MapsTo (ContinuousMap.id E) ((closedBall c r)ᶜ) ({x}ᶜ : Set E) from
      fun ⦃z⦄ hz h => by
        have he : z = x := h
        exact hz (he ▸ hx))

theorem integralBallLocalRestriction_quasiIso (c : E) (r : Real) (hr : 0 ≤ r)
    (x : E) (hx : x ∈ closedBall c r) :
    QuasiIso (integralBallLocalRestriction c r x hx) := by
  let O : Set E := (closedBall c r)ᶜ
  let P : Set E := {x}ᶜ
  let incl : integralChains O ⟶ integralChains P := integralChainsFunctor.map
    (TopCat.ofHom (closedBallComplementPointInclusion c r x hx))
  have hI : QuasiIso incl := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact closedBallComplementPointInclusion_homology_isIso c r hr x hx n
  let F : integralPairSequence O ⟶ integralPairSequence P :=
    { τ₁ := incl
      τ₂ := 𝟙 (integralChains E)
      τ₃ := integralBallLocalRestriction c r x hx
      comm₁₂ := by
        change incl ≫ integralSubspaceChains P = integralSubspaceChains O ≫ 𝟙 _
        rw [Category.comp_id]
        dsimp only [incl, integralSubspaceChains]
        rw [← Functor.map_comp]
        rfl
      comm₂₃ := by
        change 𝟙 _ ≫ integralRelativeProjection P =
          integralRelativeProjection O ≫ integralRelativeMap (ContinuousMap.id E) _
        rw [Category.id_comp, integralRelativeMap_projection]
        change integralRelativeProjection P =
          integralChainsFunctor.map (𝟙 (TopCat.of E)) ≫ integralRelativeProjection P
        simp }
  exact HomologySequence.quasiIso_τ₃ F
    (integralPairSequence_shortExact O) (integralPairSequence_shortExact P) hI
      (by change QuasiIso (𝟙 (integralChains E)); infer_instance)

theorem integralBallLocalRestriction_homology_isIso
    (c : E) (r : Real) (hr : 0 ≤ r) (x : E) (hx : x ∈ closedBall c r) (n : Nat) :
    IsIso (homologyMap (integralBallLocalRestriction c r x hx) n) := by
  let := integralBallLocalRestriction_quasiIso c r hr x hx
  infer_instance

end

end PoincareConjecture.Proofs.M02.Topology
