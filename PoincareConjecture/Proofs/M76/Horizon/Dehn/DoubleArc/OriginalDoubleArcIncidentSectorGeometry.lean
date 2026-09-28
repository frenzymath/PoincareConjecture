import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalDoubleArcJointRestrictions
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondReflection










set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem exists_original_incident_joint_sector_geometry
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
    let J := K.barycentricDualBlock s
    let Q := {z | z ∈ J.space ∧ ∀ i : Fin 2,
      if signs i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0}
    let U := (Q ∩ (M (sheet 0)).space) ∪ (Q ∩ (M (sheet 1)).space)
    let O := Q ∩ (J.link (s.centroid ℝ id)).space
    ∃ a b : E, a ≠ b ∧ IsFinitePLBallPair P2 Q (O ∪ U) ∧
      IsFinitePLBallPair ℝ U {a, b} ∧
      Q ⊆ ((M reg).barycentricDualBlock {(v : E)}).space ∧
      Q ⊆ ((K.barycentricDualBlock {(v : E)}).link v).space := by
  classical
  obtain ⟨p, T, G, hG, hps, hquarter, hradius, hsheetMap, hcenter, hcorners,
    hquarterMap, hradiusMap, hregJ, hmiss, harcJ, hlinks, hne, hgeometry, hchange⟩ :=
    exists_original_signed_tube_joint_restrictions hAC hAR hAF S K F hF H hH g hg hgPL
      M hMK hfull reg fr arc sheet hreg hfr harc hsheet B hB s hs hcard
  obtain ⟨eta, heta, htransport⟩ := hchange v hvs
  let sourceSigns : Fin 2 → Bool := fun i => signedTubeReindex (eta i) (signs i)
  let sourceQ := {z | z ∈ (K.barycentricDualBlock s).space ∧
    (if sourceSigns 0 then 0 ≤ B p (g z) 0 else B p (g z) 0 ≤ 0) ∧
    if sourceSigns 1 then 0 ≤ B p (g z) 1 else B p (g z) 1 ≤ 0}
  let Q := {z | z ∈ (K.barycentricDualBlock s).space ∧ ∀ i : Fin 2,
    if signs i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0}
  have hsign (i : Fin 2) (z : E) (hz : z ∈ (K.barycentricDualBlock s).space) :
      (if sourceSigns i then 0 ≤ B p (g z) i.castSucc else B p (g z) i.castSucc ≤ 0) ↔
      if signs i then 0 ≤ B v (g z) i.castSucc else B v (g z) i.castSucc ≤ 0 := by
    have ht := htransport i (sourceSigns i) z hz
    cases he : eta i <;> cases hs : signs i <;>
      simpa only [sourceSigns, signedTubeReindex, he, hs, Bool.false_eq_true,
        ↓reduceIte, Bool.not_false, Bool.not_true] using ht
  have hQ : Q = sourceQ := by
    ext z
    constructor
    · rintro ⟨hz, h⟩
      exact ⟨hz, (hsign 0 z hz).mpr (h 0), (hsign 1 z hz).mpr (h 1)⟩
    · rintro ⟨hz, h₀, h₁⟩
      refine ⟨hz, ?_⟩
      intro i
      fin_cases i
      · exact (hsign 0 z hz).mp h₀
      · exact (hsign 1 z hz).mp h₁
  let a : Fin 2 → Bool → E := fun i sign => (T i sign).centroid ℝ id
  let rad : Fin 2 → Bool → Set E := fun i sign => segment ℝ (s.centroid ℝ id) (a i sign)
  have hgeom := hgeometry (sourceSigns 0) (sourceSigns 1)
  have hrad₀ : Q ∩ (M (sheet 0)).space = rad 0 (sourceSigns 1) := by
    rw [hQ]
    exact hgeom.2.2.2.2.1
  have hrad₁ : Q ∩ (M (sheet 1)).space = rad 1 (sourceSigns 0) := by
    rw [hQ]
    exact hgeom.2.2.2.2.2.1
  have hends : a 0 (sourceSigns 1) ≠ a 1 (sourceSigns 0) := by
    intro heq
    have h₀ : a 0 (sourceSigns 1) ∈ rad 0 (sourceSigns 1) := right_mem_segment ℝ _ _
    have h₁ : a 0 (sourceSigns 1) ∈ rad 1 (sourceSigns 0) := heq ▸ right_mem_segment ℝ _ _
    exact hne 0 (sourceSigns 1) (hgeom.2.2.2.2.2.2.subset ⟨h₀, h₁⟩)
  refine ⟨a 0 (sourceSigns 1), a 1 (sourceSigns 0), hends, ?_, ?_, ?_, ?_⟩
  · change IsFinitePLBallPair P2 Q ((Q ∩ _) ∪ ((Q ∩ _) ∪ (Q ∩ _)))
    rw [hrad₀, hrad₁, hQ]
    exact hgeom.1
  · change IsFinitePLBallPair ℝ ((Q ∩ _) ∪ (Q ∩ _)) _
    rw [hrad₀, hrad₁]
    exact hgeom.2.1
  · intro z hz
    apply space_subset_of_le ((M reg).barycentricDualBlock_antitone
      (Finset.singleton_subset_iff.mpr hvs))
    exact hregJ.subset hz.1
  · exact fun z hz => hlinks v hvs hz.1

end PoincareConjecture.M76.Dehn
