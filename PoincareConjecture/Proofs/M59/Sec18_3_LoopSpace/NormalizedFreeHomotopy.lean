import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.Claim18_16_PiTwoPiThree
import PoincareConjecture.Proofs.M59.Mathlib.CubeTransport











set_option autoImplicit false

open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareConjecture

open Proofs.M02

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



theorem m59NormalizedFamily_pole (q : M59SphereQuotient) (x : M)
    (Gamma : FreeTwoSphereFamily (M := M)) (hGamma : M59NormalizedAt q x Gamma) :
    m59FamilyMap Gamma q.pole = constantC1Loop x := by
  have hz : (fun _ : Fin 2 => (0 : I)) ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  rw [← q.boundary_collapsed _ hz, ← m59NormalizedCube_agreement q x Gamma hGamma]
  exact GenLoop.boundary (m59NormalizedCube q x Gamma hGamma) _ hz



theorem m59NormalizedCube_homotopyAlong (q : M59SphereQuotient) (x : M)
    (Gamma Delta : FreeTwoSphereFamily (M := M))
    (hGamma : M59NormalizedAt q x Gamma) (hDelta : M59NormalizedAt q x Delta)
    (H : (m59FamilyMap Gamma).Homotopy (m59FamilyMap Delta)) :
    ∃ l : Path (constantC1Loop x) (constantC1Loop x),
      Nonempty (GenLoop.HomotopyAlong l
        (m59NormalizedCube q x Gamma hGamma) (m59NormalizedCube q x Delta hDelta)) := by
  let l : Path (constantC1Loop x) (constantC1Loop x) :=
    { toFun := fun t => H (t, q.pole)
      continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
      source' := (H.apply_zero q.pole).trans (m59NormalizedFamily_pole q x Gamma hGamma)
      target' := (H.apply_one q.pole).trans (m59NormalizedFamily_pole q x Delta hDelta) }
  refine ⟨l, ⟨{
    toFun := fun v => H (v.1, q.map v.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk (q.map.continuous.comp continuous_snd))
    map_zero_left := fun v => (H.apply_zero (q.map v)).trans
      (m59NormalizedCube_agreement q x Gamma hGamma v).symm
    map_one_left := fun v => (H.apply_one (q.map v)).trans
      (m59NormalizedCube_agreement q x Delta hDelta v).symm
    boundary_path := fun t v => congrArg (fun s => H (t, s))
      (q.boundary_collapsed v v.2) }⟩⟩




theorem m59_normalized_classes_eq_of_continuous_free_class [T2Space M]
    (hcompact : IsCompact (Set.univ : Set M)) (q : M59SphereQuotient) (x : M)
    (hfree : ∀ (a b : GenLoop (Fin 2) C(LoopCircle, M) (ContinuousMap.const LoopCircle x))
      (l : Path (ContinuousMap.const LoopCircle x) (ContinuousMap.const LoopCircle x)),
      GenLoop.HomotopyAlong l a b → GenLoop.Homotopic a b)
    (Gamma Delta : FreeTwoSphereFamily (M := M))
    (hGamma : M59NormalizedAt q x Gamma) (hDelta : M59NormalizedAt q x Delta)
    (hH : (m59FamilyMap Gamma).Homotopic (m59FamilyMap Delta)) :
    familySigmaClass Gamma = familySigmaClass Delta := by
  obtain ⟨H⟩ := hH
  obtain ⟨l, ⟨K⟩⟩ := m59NormalizedCube_homotopyAlong q x Gamma Delta hGamma hDelta H
  have hab := hfree _ _ _ (K.map Proofs.M58.loopValues)
  have heq : (⟦m59NormalizedCube q x Gamma hGamma⟧ :
      HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)) =
      ⟦m59NormalizedCube q x Delta hDelta⟧ :=
    (m59C1ValueEquivTop hcompact 2 x).injective (Quotient.sound hab)
  rw [← m59NormalizedCube_sigma q x Gamma hGamma, ← m59NormalizedCube_sigma q x Delta hDelta]
  exact congrArg (Sigma.mk x) heq

end PoincareConjecture
