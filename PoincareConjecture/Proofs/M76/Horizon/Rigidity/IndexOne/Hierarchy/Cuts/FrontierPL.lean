import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Cuts.FrontierMap
import PoincareConjecture.Proofs.M76.Rigidity.MeridianBandCarrier
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLGluing



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "W" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {N : Set X} {j : V2 → X}


theorem polyhedral_marked_parameter_cap (P : OriginalDiskProduct e N j)
    (s : ℝ) {t : ℝ} (ht : t ∈ I) :
    PolyhedralPLInCharts e (fun z : W => P.map (z.1, t)) (D ×ˢ ({s} : Set ℝ)) := by
  obtain ⟨K, hK, hKS⟩ := exists_finite_cubePrismCap s
  let A : W →ᴬ[ℝ] W :=
    (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
      (ContinuousAffineMap.const ℝ W t)
  have hA : FinitePiecewiseAffineOn A K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine A⟩
  have hmap : MapsTo A K.space (D ×ˢ I) := fun _ hz => ⟨(hKS.subset hz).1, ht⟩
  have h := P.polyhedral.comp_finitePiecewiseAffineOn K hK hA hmap
  change PolyhedralPLInCharts e (fun z : W => P.map (z.1, t)) K.space at h
  exact hKS ▸ h


theorem polyhedral_markedCutFrontierMap (P : OriginalDiskProduct e N j)
    (he : PLDomain e N) (q : W → X) {l u : ℝ} (hlu : l < u)
    (hlower : ∀ z ∈ Q, q (z, l) = P.map (z, (1 / 2 : ℝ)))
    (hupper : ∀ z ∈ Q, q (z, u) = P.map (z, -(1 / 2 : ℝ)))
    (hq : PolyhedralPLInCharts e q (Q ×ˢ Icc l u)) :
    PolyhedralPLInCharts e (P.markedCutFrontierMap q l u) (cubePrismBoundary l u) := by
  let f := P.markedCutFrontierMap q l u
  have hl : PolyhedralPLInCharts e f (D ×ˢ ({l} : Set ℝ)) :=
    (P.polyhedral_marked_parameter_cap l (t := 1 / 2) (by norm_num)).congr (by
      intro z hz
      have hz' : z = (z.1, l) := Prod.ext rfl hz.2
      change P.map (z.1, (1 / 2 : ℝ)) = P.markedCutFrontierMap q l u z
      rw [hz', P.markedCutFrontierMap_lower])
  have hu : PolyhedralPLInCharts e f (D ×ˢ ({u} : Set ℝ)) :=
    (P.polyhedral_marked_parameter_cap u (t := -(1 / 2)) (by norm_num)).congr (by
      intro z hz
      have hz' : z = (z.1, u) := Prod.ext rfl hz.2
      change P.map (z.1, -(1 / 2 : ℝ)) = P.markedCutFrontierMap q l u z
      rw [hz', P.markedCutFrontierMap_upper q hlu])
  have hlat : PolyhedralPLInCharts e f (Q ×ˢ Icc l u) :=
    hq.congr (fun z hz => (P.markedCutFrontierMap_lateral q hlu hlower hupper z hz.1).symm)
  have hS : cubePrismBoundary l u =
      (Q ×ˢ Icc l u) ∪ ((D ×ˢ ({l} : Set ℝ)) ∪ (D ×ˢ ({u} : Set ℝ))) := by
    ext z
    simp only [cubePrismBoundary, mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  have hcl : IsClosed (D ×ˢ ({l} : Set ℝ)) := isClosed_closedBall.prod isClosed_singleton
  have hcu : IsClosed (D ×ˢ ({u} : Set ℝ)) := isClosed_closedBall.prod isClosed_singleton
  have hc : ContinuousOn f (cubePrismBoundary l u) := by
    rw [hS]
    exact hlat.continuousOn.union_of_isClosed
      (hl.continuousOn.union_of_isClosed hu.continuousOn hcl hcu)
      (isClosed_sphere.prod isClosed_Icc) (hcl.union hcu)
  obtain ⟨K, hK, hKS⟩ := exists_finite_cubePrismBoundary hlu
  obtain ⟨J0, hJ0, hJ0S⟩ := exists_finite_hamiltonMeridianBand hlu
  obtain ⟨J1, hJ1, hJ1S⟩ := exists_finite_cubePrismCap l
  obtain ⟨J2, hJ2, hJ2S⟩ := exists_finite_cubePrismCap u
  let J : Option Bool → SimplicialComplex ℝ W
    | none => J0
    | some false => J1
    | some true => J2
  have hJ (i : Option Bool) : (J i).faces.Finite := by
    rcases i with _ | b
    · exact hJ0
    · cases b
      · exact hJ1
      · exact hJ2
  have hPL (i : Option Bool) : PolyhedralPLInCharts e f (J i).space := by
    rcases i with _ | b
    · exact hJ0S.symm ▸ hlat
    · cases b
      · exact hJ1S.symm ▸ hl
      · exact hJ2S.symm ▸ hu
  have hcover : K.space ⊆ ⋃ i, (J i).space := by
    intro z hz
    rcases hS.subset (hKS.subset hz) with hlat | hl | hu
    · exact mem_iUnion.mpr ⟨none, hJ0S.symm.subset hlat⟩
    · exact mem_iUnion.mpr ⟨some false, hJ1S.symm.subset hl⟩
    · exact mem_iUnion.mpr ⟨some true, hJ2S.symm.subset hu⟩
  exact hKS ▸ polyhedralPLInCharts_of_finite_cover he.cover he.compatible K hK J hJ
    (hKS.symm ▸ hc) hPL hcover

end PoincareConjecture.M76.OriginalDiskProduct
