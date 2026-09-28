import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneActualMeridian
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneComplementDomain
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedGeometricInputs










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "V" => (ℝ × V2)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "Q" => sphere (0 : V2) 1
local notation "Param" => Set.prod (Icc (-1 : ℝ) 1) Q







theorem exists_actual_marked_proper_dehn_disk
    (hDehn : HasHamiltonStandardProperDehnDisks)
    (A : W ≃ₜ W) (hAL : A '' squareBlock = squareBlock)
    (hAf : EqOn A id (frontier squareBlock)) {B T : Set W}
    (hB : IsFinitePLBallPair W B (T ∪ squareAttachingDisks))
    (hBL : B ⊆ squareBlock) (hT : IsClosed T)
    (hcontact : B ∩ frontier squareBlock = squareAttachingDisks)
    (hrims : T ∩ frontier squareBlock = squareRims)
    (tau : squareInnerAnnulus ≃ₜ T) (htau : tau.IsFinitePL)
    (hfix : ∀ x : squareInnerAnnulus, (x : W) ∈ squareRims → (tau x : W) = x)
    (unit : Param ≃ₜ T) (hunitPL : unit.IsFinitePL)
    (hunit : ∀ x : Param, ∀ hx : unitAnnulusCoordinates x ∈ squareInnerAnnulus,
      (tau ⟨unitAnnulusCoordinates x, hx⟩ : W) = unit x)
    (hKB : A '' squareUnitBlock ⊆ B) (hKT : Disjoint (A '' squareUnitBlock) T) :
    ∃ (marked : squareInnerAnnulus ≃ₜ T)
      (e : frontier squareShell ≃ₜ frontier (complementaryRegion B))
      (D : Set W) (b : closedBall (0 : V2) 1 ≃ₜ D),
      marked.IsFinitePL ∧
      (∀ x : squareInnerAnnulus, (x : W) ∈ squareRims → (marked x : W) = x) ∧
      e.IsFinitePL ∧
      (∀ (x : squareInnerAnnulus) (hx : (x : W) ∈ frontier squareShell),
        (e ⟨x, hx⟩ : W) = marked x) ∧
      (∀ (x : squareOuterAnnulus) (hx : (x : W) ∈ frontier squareShell),
        (e ⟨x, hx⟩ : W) = x) ∧
      IsCompact D ∧ D ⊆ complementaryRegion B ∧ b.IsFinitePL ∧
      (∀ x : Q, standardSquareMeridian x ∈ frontier squareShell) ∧
      (∀ (x : Q) (hx : standardSquareMeridian x ∈ frontier squareShell),
        (b ⟨x, sphere_subset_closedBall x.property⟩ : W) =
          e ⟨standardSquareMeridian x, hx⟩) ∧
      ∀ x : closedBall (0 : V2) 1,
        (b x : W) ∈ frontier (complementaryRegion B) ↔ (x : V2) ∈ Q := by
  obtain ⟨marked, e, S, gamma, F, hm, hmfix, he, heinner, heouter,
    hgamma, hS, hstandard, hmarked, hF⟩ :=
    exists_actual_marked_meridian_filling A hAL hAf hB hBL hT hcontact hrims
      tau htau hfix unit hunitPL hunit hKB hKT
  let l : W ≃L[ℝ] V3 := ContinuousLinearEquiv.ofFinrankEq
    (by simp [Module.finrank_prod])
  let a := l.toContinuousAffineEquiv
  let E : Set W := complementaryRegion B
  obtain ⟨hRcompact, hRdomain⟩ := plDomain_affineImage_complementaryRegion a
    hB.isCompact.isClosed (hB.closure_interior_of_finrank_eq rfl) hBL hT
    (hB.frontier_eq_of_finrank_eq rfl) hcontact hrims tau htau hfix
  have haFront : a '' frontier E = frontier (a '' E) :=
    a.toHomeomorph.image_frontier E
  have hSa : a '' S ⊆ frontier (a '' E) := by
    have h := image_mono (f := a) hS
    rwa [haFront] at h
  let gammaA : Q ≃ₜ (a '' S) := gamma.trans (a.toHomeomorph.image S)
  have hgammaA : gammaA.IsFinitePL := by
    obtain ⟨g, hg, hgeq⟩ := hgamma
    exact ⟨fun x => a (g x), hg.postcomp a.toContinuousAffineMap,
      fun x => congrArg a (hgeq x)⟩
  let FA : C(closedBall (0 : V2) 1, a '' E) :=
    ⟨fun x => ⟨a (F x), ⟨F x, (F x).property, rfl⟩⟩,
      (a.continuous.comp (continuous_subtype_val.comp F.continuous)).subtype_mk _⟩
  have hFA (x : Q) : (FA ⟨x, sphere_subset_closedBall x.property⟩ : V3) = gammaA x :=
    congrArg a (hF x)
  obtain ⟨DA, bA, hDA, hDAE, hbA, hbAbound, hbAproper⟩ :=
    hDehn (a '' E) hRcompact hRdomain (a '' S) hSa gammaA hgammaA FA hFA
  let D : Set W := a.symm '' DA
  let b : closedBall (0 : V2) 1 ≃ₜ D := bA.trans (a.symm.toHomeomorph.image DA)
  have hD : IsCompact D := hDA.image a.symm.continuous
  have hDE : D ⊆ E := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, hyz⟩ := hDAE hz
    rw [← hyz, a.symm_apply_apply]
    exact hy
  have hb : b.IsFinitePL := by
    obtain ⟨g, hg, hgeq⟩ := hbA
    exact ⟨fun x => a.symm (g x), hg.postcomp a.symm.toContinuousAffineMap,
      fun x => congrArg a.symm (hgeq x)⟩
  have hboundary (x : Q) : (b ⟨x, sphere_subset_closedBall x.property⟩ : W) = gamma x := by
    have h := hbAbound x
    change (bA ⟨x, sphere_subset_closedBall x.property⟩ : V3) = a (gamma x : W) at h
    change a.symm (bA ⟨x, sphere_subset_closedBall x.property⟩ : V3) = _
    rw [h, a.symm_apply_apply]
  have hproper (x : closedBall (0 : V2) 1) :
      (b x : W) ∈ frontier E ↔ (x : V2) ∈ Q := by
    have hmem : (b x : W) ∈ frontier E ↔ (bA x : V3) ∈ frontier (a '' E) := by
      rw [← haFront]
      constructor
      · intro hx
        exact ⟨a.symm (bA x : V3), hx, a.apply_symm_apply _⟩
      · rintro ⟨y, hy, hyx⟩
        change a.symm (bA x : V3) ∈ frontier E
        rw [← hyx, a.symm_apply_apply]
        exact hy
    exact hmem.trans (hbAproper x)
  exact ⟨marked, e, D, b, hm, hmfix, he, heinner, heouter, hD, hDE, hb, hstandard,
    fun x hx => (hboundary x).trans (hmarked x hx), hproper⟩

end PoincareConjecture.M76.HamiltonIndexOne
