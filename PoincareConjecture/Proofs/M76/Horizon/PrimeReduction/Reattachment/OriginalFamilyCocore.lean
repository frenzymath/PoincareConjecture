import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.OriginalProtectedCocore
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.FamilyCocoreSection

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Square" => Set.prod (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1)
local notation "Cube" => Set.prod Square (Icc (-1 : ℝ) 1)
local notation "OpenCube" => Set.prod (Set.prod (Ioo (-1 : ℝ) 1) (Ioo (-1 : ℝ) 1)) (Ioo (-1 : ℝ) 1)

theorem physical_cocore_contact_eq_chart_section
    {X : Type*} [TopologicalSpace X] (S : Set X) (p : P3 → X)
    (Q : OpenPartialHomeomorph X V3) (H : V3 ≃ᴬ[ℝ] P3)
    (J : Set V3) (hJQ : J ⊆ Q.target)
    (hQT : Q.target = H ⁻¹' OpenCube)
    (hvalues : ∀ y, Q.symm y = p (H y)) (t : ℝ)
    (hcapture : ∀ z ∈ Square ×ˢ {t}, p z ∈ S → H.symm z ∈ J) :
    S ∩ p '' (Square ×ˢ {t}) =
      Q.symm '' ((Q '' (S ∩ Q.source) ∩ J) ∩ {x | (H x).2 = t}) := by
  apply Subset.antisymm
  · rintro _ ⟨hzS,z,hz,rfl⟩
    have hzJ := hcapture z hz hzS
    have hzQ := hJQ hzJ
    have hv : Q.symm (H.symm z) = p z := by
      rw [hvalues,H.apply_symm_apply]
    refine ⟨H.symm z,⟨⟨⟨Q.symm (H.symm z),
      ⟨hv.symm ▸ hzS,Q.map_target hzQ⟩,Q.right_inv hzQ⟩,hzJ⟩,?_⟩,hv⟩
    change (H (H.symm z)).2 = t
    simpa only [H.apply_symm_apply,mem_singleton_iff] using hz.2
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hyx⟩ := hx.1.1
    have hxS : Q.symm x ∈ S := by
      rw [← hyx,Q.left_inv hy.2]
      exact hy.1
    have hxO := hQT.subset (hJQ hx.1.2)
    refine ⟨hxS,⟨H x,⟨?_,hx.2⟩,(hvalues x).symm⟩⟩
    exact ⟨⟨hxO.1.1.1.le,hxO.1.1.2.le⟩,⟨hxO.1.2.1.le,hxO.1.2.2.le⟩⟩

theorem disjoint_physical_cocore_of_empty_chart_section
    {X : Type*} [TopologicalSpace X] (S : Set X) (p : P3 → X)
    (Q : OpenPartialHomeomorph X V3) (H : V3 ≃ᴬ[ℝ] P3)
    (J : Set V3) (hJQ : J ⊆ Q.target)
    (hQT : Q.target = H ⁻¹' OpenCube)
    (hvalues : ∀ y, Q.symm y = p (H y)) (t : ℝ)
    (hcapture : ∀ z ∈ Square ×ˢ {t}, p z ∈ S → H.symm z ∈ J)
    (hempty : (Q '' (S ∩ Q.source) ∩ J) ∩ {x | (H x).2 = t} = ∅) :
    Disjoint S (p '' (Square ×ˢ {t})) := by
  rw [disjoint_iff_inter_eq_empty,
    physical_cocore_contact_eq_chart_section S p Q H J hJQ hQT hvalues t hcapture,
    hempty,image_empty]

theorem cocore_contact_capture_of_supported_subset
    {X : Type*} [TopologicalSpace X] {S T : Set X} (p : P3 → X)
    (hp : InjOn p Cube) (Q : OpenPartialHomeomorph X V3)
    (H : V3 ≃ᴬ[ℝ] P3) {J : Set V3} (hJQ : J ⊆ Q.target)
    (hQT : Q.target = H ⁻¹' OpenCube)
    (hvalues : ∀ y, Q.symm y = p (H y))
    (K : Set P3) (hK : K ⊆ Cube)
    (hcapture : ∀ z ∈ K, p z ∈ S → H.symm z ∈ J)
    (hTS : T ⊆ S ∪ Q.symm '' J) :
    ∀ z ∈ K, p z ∈ T → H.symm z ∈ J := by
  intro z hz hzT
  rcases hTS hzT with hzS | hzJ
  · exact hcapture z hz hzS
  · obtain ⟨y,hy,hyz⟩ := hzJ
    have hyO := hQT.subset (hJQ hy)
    have hyCube : H y ∈ Cube :=
      ⟨⟨⟨hyO.1.1.1.le,hyO.1.1.2.le⟩,⟨hyO.1.2.1.le,hyO.1.2.2.le⟩⟩,
        ⟨hyO.2.1.le,hyO.2.2.le⟩⟩
    have heq : H y = z := hp hyCube (hK hz) ((hvalues y).symm.trans hyz)
    rw [← heq,H.symm_apply_apply]
    exact hy

theorem HamiltonMarkedProtectedBall.exists_original_family_cocore
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Finite β]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 2)
    (S : β → Set (LatticeHandleAmbient ι κ L)) (s : ∀ j, ChartwisePLSphere e (S j))
    (hdis : Pairwise fun j k => Disjoint (S j) (S k))
    (hSR : ∀ j, S j ⊆ interior (latticeHandleDomain ι κ L)) :
    ∃ (p : P3 → LatticeHandleAmbient ι κ L)
      (Q : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
      (J : SimplicialComplex ℝ V3) (t : ℝ),
      t ∈ Ioo (-(1/2 : ℝ)) (1/2) ∧
      PolyhedralPLInCharts e p Cube ∧ InjOn p Cube ∧ p '' Cube = D ∧
      Q.source = interior D ∧ Q.target = markedProductCoordinates ⁻¹' OpenCube ∧
      (∀ y, Q.symm y = p (markedProductCoordinates y)) ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      J.faces.Finite ∧ J.space ⊆ Q.target ∧ Convex ℝ J.space ∧
      MapsTo Q.symm J.space (interior (latticeHandleDomain ι κ L)) ∧
      (∀ z ∈ Cube, z.2 ∈ Ioo (-(1/2 : ℝ)) (1/2) → p z ∈ ⋃ j, S j →
        markedProductCoordinates.symm z ∈ interior J.space) ∧
      (∀ z ∈ Cube, (|z.1.1| = 1 ∨ |z.1.2| = 1) →
        p z ∈ frontier (latticeHandleDomain ι κ L)) ∧
      MapsTo p OpenCube (interior (latticeHandleDomain ι κ L)) ∧
      HasDisjointPolygonPresentation
        ((Q '' ((⋃ j, S j) ∩ Q.source) ∩ J.space) ∩ {x | (markedProductCoordinates x).2 = t}) ∧
      ((Q '' ((⋃ j, S j) ∩ Q.source) ∩ J.space) ∩
        {x | (markedProductCoordinates x).2 = t}) ⊆ interior J.space ∧
      (∀ w ∈ (Q '' ((⋃ j, S j) ∩ Q.source) ∩ J.space) ∩
        {x | (markedProductCoordinates x).2 = t},
        ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ B : OpenPartialHomeomorph V3 P3,
            w ∈ B.source ∧ B.source ⊆ O ∩ interior J.space ∧ B w = 0 ∧
            LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀ x ∈ B.source, Q.symm x ∈ ⋃ j, S j ↔ (B x).2 = 0) ∧
            ∀ x ∈ B.source, (markedProductCoordinates x).2 - t = (B x).1.1) ∧
      ((⋃ j, S j) ∩ p '' (Square ×ˢ {t}) = Q.symm ''
        ((Q '' ((⋃ j, S j) ∩ Q.source) ∩ J.space) ∩ {x | (markedProductCoordinates x).2 = t})) ∧
      (∀ z ∈ Cube, p z ∈ frontier (latticeHandleDomain ι κ L) ↔
        |z.1.1| = 1 ∨ |z.1.2| = 1) := by
  have hSclosed : IsClosed (⋃ j, S j) :=
    isClosed_iUnion_of_finite fun j => (s j).isCompact.isClosed
  have hSU : (⋃ j, S j) ⊆ interior (latticeHandleDomain ι κ L) := iUnion_subset hSR
  obtain ⟨p,Q,J,hp,hpi,hpD,hQs,hQt,hQinv,hQ,hJ,hJQ,hJcv,hJR,hband,hall,hlat,hinner,hproper⟩ :=
    b.exists_original_cocore_window_of_isClosed he hdim hi hSclosed hSU
  let A : V3 →ᵃ[ℝ] ℝ :=
    ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap.comp
      markedProductCoordinates.toContinuousAffineMap).toAffineMap
  obtain ⟨t,ht,_,hpres,hcross⟩ :=
    exists_sphere_family_regular_cocore_section S s hdis Q hQ J hJ hJQ A
      (show -(1/2 : ℝ) < 1/2 by norm_num) hband
  refine ⟨p,Q,J,t,ht,hp,hpi,hpD,hQs,hQt,hQinv,hQ,hJ,hJQ,hJcv,hJR,hall,hlat,hinner,
    hpres,fun x hx => hband x hx.1 (hx.2 ▸ ht),hcross,?_,hproper⟩
  apply physical_cocore_contact_eq_chart_section _ p Q markedProductCoordinates J.space hJQ hQt hQinv t
  intro z hz hzS
  have hzt : z.2 = t := hz.2
  apply interior_subset (hall z ⟨hz.1,?_⟩ (hzt ▸ ht) hzS)
  constructor <;> linarith [ht.1,ht.2]

end PoincareConjecture.M76
