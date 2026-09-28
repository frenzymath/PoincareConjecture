import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcJointRestrictions
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondStrictPoints









set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem exists_original_joint_strict_point
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R C A : Set X}
    (hAC : A ⊆ interior C) (hAR : A ⊆ R) (hAF : (A ∩ frontier R).Finite)
    (S : Fin 2 → Set X) (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (F : X → E) (hF : Continuous F) (H : C ≃ₜ K.space)
    (hH : ∀ x : C, (H x : E) = F x) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K)
    (hfull : ∀ i t, t ∈ K.faces → (∀ v ∈ t, v ∈ (M i).vertices) → t ∈ (M i).faces)
    (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (hsheet : ∀ i z, z ∈ K.space → (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (B : (M arc).vertices → OpenPartialHomeomorph X V3)
    (hB : ∀ p : (M arc).vertices,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space (B p).source ∧
      (K.closedStar p).AffineOnFaces (fun z => B p (g z)) ∧
      (∀ y ∈ (B p).source, y ∈ A ↔ y ∈ R ∧ B p y 0 = 0 ∧ B p y 1 = 0) ∧
      ∀ i y, y ∈ (B p).source → (y ∈ S i ↔ y ∈ R ∧ B p y i.castSucc = 0))
    (s : Finset E) (hs : s ∈ (M arc).faces) (hcard : s.card = 2)
    (v : (M arc).vertices) (hvs : (v : E) ∈ s) (signs : Fin 2 → Bool) :
    ∃ z ∈ (K.barycentricDualBlock s).space,
      z ∈ ((K.barycentricDualBlock {(v : E)}).link v).space ∧
      ∀ i : Fin 2, if signs i then 0 < B v (g z) i.castSucc
        else B v (g z) i.castSucc < 0 := by
  obtain ⟨p, T, G, hG, hps, hquarter, hradius, hsheetMap, hcenter, hcorners,
    hquarterMap, hradiusMap, hregJ, hmiss, harcJ, hlinks, hne, hgeometry, hchange⟩ :=
    exists_original_signed_tube_joint_restrictions hAC hAR hAF S K F hF H hH g hg hgPL
      M hMK hfull reg fr arc sheet hreg hfr harc hsheet B hB s hs hcard
  obtain ⟨eta, heta, htransport⟩ := hchange v hvs
  have hlocal (eps delta : Bool) (x : signedTubeDiamond) :
      (x : P2) ∈ signedTubeQuarter eps delta ↔
        (G x : E) ∈ signedCoordinateSector (K.barycentricDualBlock s).space
          (fun i z => B v (g z) i.castSucc) eta eps delta := by
    rw [hquarter]
    change ((G x : E) ∈ (K.barycentricDualBlock s).space ∧
      (if eps then 0 ≤ B p (g (G x)) 0 else B p (g (G x)) 0 ≤ 0) ∧
      (if delta then 0 ≤ B p (g (G x)) 1 else B p (g (G x)) 1 ≤ 0)) ↔ _
    exact and_congr Iff.rfl (and_congr
      (htransport 0 eps (G x) (G x).property)
      (htransport 1 delta (G x) (G x).property))
  obtain ⟨z, hz, hstrict⟩ := exists_strict_point_of_signed_diamond_quarters
    (K.barycentricDualBlock s).space (fun i z => B v (g z) i.castSucc) eta G hlocal signs
  exact ⟨z, hz, hlinks v hvs hz, hstrict⟩

end PoincareConjecture.M76.Dehn
