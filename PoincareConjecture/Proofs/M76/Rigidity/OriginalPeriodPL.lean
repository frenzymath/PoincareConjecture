import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodMap
import PoincareConjecture.Proofs.M76.Rigidity.MeridianParameter
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLGluing










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}



theorem polyhedral_periodCutMap (P : OriginalDiskProduct e R j)
    (he : PLDomain e R) {a p : ℝ} (ha : 0 < a) (hgap : a / 2 < p - a / 2)
    (u : E → X) (hu : PolyhedralPLInCharts e u (D ×ˢ Icc (a / 2) (p - a / 2)))
    (hlower : ∀ z ∈ D, u (z, a / 2) = P.map (z, 1 / 2))
    (hupper : ∀ z ∈ D, u (z, p - a / 2) = P.map (z, -(1 / 2))) :
    PolyhedralPLInCharts e (P.periodCutMap a p u) (D ×ˢ Icc 0 p) := by
  let v := P.periodCutMap a p u
  let C0 : Set E := D ×ˢ Icc 0 (a / 2)
  let C1 : Set E := D ×ˢ Icc (a / 2) (p - a / 2)
  let C2 : Set E := D ×ˢ Icc (p - a / 2) p
  obtain ⟨K, hK, hKW⟩ := exists_finite_hamiltonMeridianBox (by linarith : 0 < p)
  obtain ⟨J0, hJ0, hJ0S⟩ := exists_finite_hamiltonMeridianBox (half_pos ha)
  obtain ⟨J1, hJ1, hJ1S⟩ := exists_finite_hamiltonMeridianBox hgap
  obtain ⟨J2, hJ2, hJ2S⟩ :=
    exists_finite_hamiltonMeridianBox (by linarith : p - a / 2 < p)
  have h0 : PolyhedralPLInCharts e v C0 := by
    have hA : FinitePiecewiseAffineOn (periodLowerCoordinates a) J0.space :=
      ⟨J0, hJ0, rfl, J0.affineOnFaces_affine (periodLowerCoordinates a)⟩
    have hmap : MapsTo (periodLowerCoordinates a) J0.space (D ×ˢ I) := by
      intro z hz
      have hc := periodLowerCoordinates_mapsTo ha (hJ0S.subset hz)
      exact ⟨hc.1, by linarith [hc.2.1], by linarith [hc.2.2]⟩
    have hp := (P.polyhedral.comp_finitePiecewiseAffineOn J0 hJ0 hA hmap).congr
      (fun z hz => (P.periodCutMap_lower a p u (hJ0S.subset hz).2.2).symm)
    change PolyhedralPLInCharts e v (D ×ˢ Icc 0 (a / 2))
    exact hJ0S ▸ hp
  have h1 : PolyhedralPLInCharts e v C1 :=
    hu.congr (fun z hz => (P.periodCutMap_middle ha hgap u hlower hupper hz).symm)
  have h2 : PolyhedralPLInCharts e v C2 := by
    have hA : FinitePiecewiseAffineOn (periodUpperCoordinates a p) J2.space :=
      ⟨J2, hJ2, rfl, J2.affineOnFaces_affine (periodUpperCoordinates a p)⟩
    have hmap : MapsTo (periodUpperCoordinates a p) J2.space (D ×ˢ I) := by
      intro z hz
      have hc := periodUpperCoordinates_mapsTo ha (hJ2S.subset hz)
      exact ⟨hc.1, by linarith [hc.2.1], by linarith [hc.2.2]⟩
    have hp := (P.polyhedral.comp_finitePiecewiseAffineOn J2 hJ2 hA hmap).congr
      (fun z hz => (P.periodCutMap_upper hgap u (hJ2S.subset hz).2.1).symm)
    change PolyhedralPLInCharts e v (D ×ˢ Icc (p - a / 2) p)
    exact hJ2S ▸ hp
  have hpieces : D ×ˢ Icc (0 : ℝ) p = C0 ∪ (C1 ∪ C2) := by
    ext z
    constructor
    · intro hz
      by_cases hlo : z.2 ≤ a / 2
      · exact Or.inl ⟨hz.1, hz.2.1, hlo⟩
      · by_cases hup : p - a / 2 ≤ z.2
        · exact Or.inr (Or.inr ⟨hz.1, hup, hz.2.2⟩)
        · exact Or.inr (Or.inl ⟨hz.1, (not_le.mp hlo).le, (not_le.mp hup).le⟩)
    · rintro (hz | hz | hz)
      · exact ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
      · exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
      · exact ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩
  have hc : ContinuousOn v (D ×ˢ Icc (0 : ℝ) p) := by
    rw [hpieces]
    exact h0.continuousOn.union_of_isClosed
      (h1.continuousOn.union_of_isClosed h2.continuousOn
        (isClosed_closedBall.prod isClosed_Icc) (isClosed_closedBall.prod isClosed_Icc))
      (isClosed_closedBall.prod isClosed_Icc)
      ((isClosed_closedBall.prod isClosed_Icc).union (isClosed_closedBall.prod isClosed_Icc))
  let J : Option Bool → SimplicialComplex ℝ E
    | none => J0
    | some false => J1
    | some true => J2
  have hJ (i : Option Bool) : (J i).faces.Finite := by
    rcases i with _ | b
    · exact hJ0
    · cases b
      · exact hJ1
      · exact hJ2
  have hPL (i : Option Bool) : PolyhedralPLInCharts e v (J i).space := by
    rcases i with _ | b
    · exact hJ0S.symm ▸ h0
    · cases b
      · exact hJ1S.symm ▸ h1
      · exact hJ2S.symm ▸ h2
  have hcover : K.space ⊆ ⋃ i, (J i).space := by
    intro z hz
    rcases hpieces.subset (hKW.subset hz) with hlo | hmid | hup
    · exact mem_iUnion.mpr ⟨none, hJ0S.symm.subset hlo⟩
    · exact mem_iUnion.mpr ⟨some false, hJ1S.symm.subset hmid⟩
    · exact mem_iUnion.mpr ⟨some true, hJ2S.symm.subset hup⟩
  have h := polyhedralPLInCharts_of_finite_cover he.cover he.compatible K hK J hJ
    (hKW.symm ▸ hc) hPL hcover
  exact hKW ▸ h

end PoincareConjecture.M76.OriginalDiskProduct
