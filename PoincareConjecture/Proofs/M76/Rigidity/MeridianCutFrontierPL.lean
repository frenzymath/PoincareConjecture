import PoincareConjecture.Proofs.M76.Rigidity.MeridianCutFrontierMap
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLGluing

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

variable {ι : Type*} {e : ι → OpenPartialHomeomorph X V3} {j : V2 → X}

theorem polyhedral_on_parameter_cap (P : OriginalDiskProduct e R j)
    (s : ℝ) {t : ℝ} (ht : t ∈ I) :
    PolyhedralPLInCharts e (fun z : E => P.map (z.1, t)) (D ×ˢ ({s} : Set ℝ)) := by
  obtain ⟨K, hK, hKS⟩ := exists_finite_cubePrismCap s
  let A : E →ᴬ[ℝ] E :=
    (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
      (ContinuousAffineMap.const ℝ E t)
  have hA : FinitePiecewiseAffineOn A K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine A⟩
  have hmap : MapsTo A K.space (D ×ˢ I) :=
    fun _ hz => ⟨(hKS.subset hz).1, ht⟩
  have h := P.polyhedral.comp_finitePiecewiseAffineOn K hK hA hmap
  change PolyhedralPLInCharts e (fun z : E => P.map (z.1, t)) K.space at h
  exact hKS ▸ h

theorem polyhedral_meridianCutFrontierMap (P : OriginalDiskProduct e R j)
    (he : PLDomain e R) {a : ℝ} (hgap : a / 2 < p - a / 2)
    (hmark : ∀ z ∈ Q, ∀ t ∈ I,
      P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t))
    (hC : PolyhedralPLInCharts e hamiltonMeridianCutAmbientMap
      (Q ×ˢ Icc (a / 2) (p - a / 2))) :
    PolyhedralPLInCharts e (P.meridianCutFrontierMap a)
      (cubePrismBoundary (a / 2) (p - a / 2)) := by
  let f := P.meridianCutFrontierMap a
  have hlower : PolyhedralPLInCharts e f (D ×ˢ ({a / 2} : Set ℝ)) :=
    (P.polyhedral_on_parameter_cap (a / 2) (t := 1 / 2) (by norm_num)).congr (by
      intro z hz
      have heq : z = (z.1, a / 2) := Prod.ext rfl hz.2
      change P.map (z.1, (1 / 2 : ℝ)) = P.meridianCutFrontierMap a z
      rw [heq, P.meridianCutFrontierMap_lower])
  have hupper : PolyhedralPLInCharts e f (D ×ˢ ({p - a / 2} : Set ℝ)) :=
    (P.polyhedral_on_parameter_cap (p - a / 2) (t := -(1 / 2)) (by norm_num)).congr (by
      intro z hz
      have heq : z = (z.1, p - a / 2) := Prod.ext rfl hz.2
      change P.map (z.1, -(1 / 2 : ℝ)) = P.meridianCutFrontierMap a z
      rw [heq, P.meridianCutFrontierMap_upper hgap])
  have hlateral : PolyhedralPLInCharts e f (Q ×ˢ Icc (a / 2) (p - a / 2)) :=
    hC.congr (fun z hz => (P.meridianCutFrontierMap_lateral hgap hmark z hz.1).symm)
  have hS : cubePrismBoundary (a / 2) (p - a / 2) =
      (Q ×ˢ Icc (a / 2) (p - a / 2)) ∪
        ((D ×ˢ ({a / 2} : Set ℝ)) ∪ (D ×ˢ ({p - a / 2} : Set ℝ))) := by
    ext z
    simp only [cubePrismBoundary, mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  have hclosed_lower : IsClosed (D ×ˢ ({a / 2} : Set ℝ)) :=
    isClosed_closedBall.prod isClosed_singleton
  have hclosed_upper : IsClosed (D ×ˢ ({p - a / 2} : Set ℝ)) :=
    isClosed_closedBall.prod isClosed_singleton
  have hc : ContinuousOn f (cubePrismBoundary (a / 2) (p - a / 2)) := by
    rw [hS]
    exact hlateral.continuousOn.union_of_isClosed
      (hlower.continuousOn.union_of_isClosed hupper.continuousOn hclosed_lower hclosed_upper)
      (isClosed_sphere.prod isClosed_Icc) (hclosed_lower.union hclosed_upper)
  obtain ⟨K, hK, hKS⟩ := exists_finite_cubePrismBoundary hgap
  obtain ⟨J0, hJ0, hJ0S⟩ := exists_finite_hamiltonMeridianBand hgap
  obtain ⟨J1, hJ1, hJ1S⟩ := exists_finite_cubePrismCap (a / 2)
  obtain ⟨J2, hJ2, hJ2S⟩ := exists_finite_cubePrismCap (p - a / 2)
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
  have hPL (i : Option Bool) : PolyhedralPLInCharts e f (J i).space := by
    rcases i with _ | b
    · exact hJ0S.symm ▸ hlateral
    · cases b
      · exact hJ1S.symm ▸ hlower
      · exact hJ2S.symm ▸ hupper
  have hcover : K.space ⊆ ⋃ i, (J i).space := by
    intro z hz
    rcases hS.subset (hKS.subset hz) with hlat | hlo | hup
    · exact mem_iUnion.mpr ⟨none, hJ0S.symm.subset hlat⟩
    · exact mem_iUnion.mpr ⟨some false, hJ1S.symm.subset hlo⟩
    · exact mem_iUnion.mpr ⟨some true, hJ2S.symm.subset hup⟩
  have h := polyhedralPLInCharts_of_finite_cover he.cover he.compatible K hK J hJ
    (hKS.symm ▸ hc) hPL hcover
  exact hKS ▸ h

end PoincareConjecture.M76.OriginalDiskProduct
