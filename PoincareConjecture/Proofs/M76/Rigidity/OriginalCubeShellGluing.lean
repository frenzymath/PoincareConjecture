import PoincareConjecture.Proofs.M76.Rigidity.CubeCollarPartition
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ScaledCubeBall
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLGluing
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "B" => closedBall (0 : V3) 1
local notation "B0" => closedBall (0 : V3) (7 / 8)
local notation "Q" => sphere (0 : V3) 1
local notation "Q0" => sphere (0 : V3) (7 / 8)
local notation "T" => (norm : V3 → ℝ) ⁻¹' Icc (7 / 8) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {C N S K Bdy : Set X}

theorem exists_chartwisePLBall_of_marked_cube_shell
    (hcover_e : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJT : J.space = T)
    (hcover : C ∪ N = K) (hoverlap : C ∩ N = S)
    (hBdy : Bdy ⊆ K) (hCfront : Disjoint C Bdy)
    (f0 f1 : V3 → X)
    (h0 : PolyhedralPLInCharts e f0 B0) (h1 : PolyhedralPLInCharts e f1 T)
    (hi0 : InjOn f0 B0) (hi1 : InjOn f1 T)
    (him0 : f0 '' B0 = C) (him1 : f1 '' T = N)
    (h1inner : ∀ x ∈ T, f1 x ∈ S ↔ x ∈ Q0)
    (h1outer : ∀ x ∈ T, f1 x ∈ Bdy ↔ x ∈ Q)
    (hagree : EqOn f0 f1 Q0) : Nonempty (ChartwisePLBall e K Bdy) := by
  classical
  obtain ⟨hsource, hinter, hQT⟩ := cube_collar_partition
  have hB0B : B0 ⊆ B := fun _ hx => hsource.subset (Or.inl hx)
  have hTB : T ⊆ B := fun _ hx => hsource.subset (Or.inr hx)
  have hnotT {x : V3} (hx : x ∈ B) (hxt : x ∉ T) : x ∈ B0 :=
    (hsource.symm.subset hx).resolve_right hxt
  let f : V3 → X := fun x => if x ∈ T then f1 x else f0 x
  have hfT {x : V3} (hx : x ∈ T) : f x = f1 x := if_pos hx
  have hf0 {x : V3} (hx : x ∈ B0) : f x = f0 x := by
    by_cases hxt : x ∈ T
    · exact (hfT hxt).trans (hagree (hinter.subset ⟨hx, hxt⟩)).symm
    · exact if_neg hxt
  have h0f : PolyhedralPLInCharts e f B0 := h0.congr (fun _ hx => (hf0 hx).symm)
  have h1f : PolyhedralPLInCharts e f T := h1.congr (fun _ hx => (hfT hx).symm)
  have hc : ContinuousOn f B := by
    rw [← hsource]
    exact h0f.continuousOn.union_of_isClosed h1f.continuousOn isClosed_closedBall
      (isClosed_Icc.preimage continuous_norm)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K0, hK0, hK0B, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_coordinate_cube (ι := Fin 3) (by norm_num : (0 : ℝ) < 7 / 8)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨KB, hKB, hKBB, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 3)
  let pieces : Bool → SimplicialComplex ℝ V3
    | false => K0
    | true => J
  have hpieces (i : Bool) : (pieces i).faces.Finite := by
    cases i
    · exact hK0
    · exact hJ
  have hPL (i : Bool) : PolyhedralPLInCharts e f (pieces i).space := by
    cases i
    · exact hK0B.symm ▸ h0f
    · exact hJT.symm ▸ h1f
  have hcov : KB.space ⊆ ⋃ i, (pieces i).space := by
    intro x hx
    rcases hsource.symm.subset (hKBB.subset hx) with hx0 | hx1
    · exact mem_iUnion.mpr ⟨false, hK0B.symm.subset hx0⟩
    · exact mem_iUnion.mpr ⟨true, hJT.symm.subset hx1⟩
  have hf : PolyhedralPLInCharts e f B := by
    have h := polyhedralPLInCharts_of_finite_cover hcover_e hcompat KB hKB pieces
      hpieces (hKBB.symm ▸ hc) hPL hcov
    exact hKBB ▸ h
  have hmap0 {x : V3} (hx : x ∈ B0) : f0 x ∈ C := him0.subset ⟨x, hx, rfl⟩
  have hmap1 {x : V3} (hx : x ∈ T) : f1 x ∈ N := him1.subset ⟨x, hx, rfl⟩
  have hfi : InjOn f B := by
    intro x hx y hy hxy
    by_cases hxt : x ∈ T <;> by_cases hyt : y ∈ T
    · rw [hfT hxt, hfT hyt] at hxy
      exact hi1 hxt hyt hxy
    · have hy0 := hnotT hy hyt
      have hxS : f1 x ∈ S := hoverlap.subset
        ⟨by rw [← hfT hxt, hxy, hf0 hy0]; exact hmap0 hy0, hmap1 hxt⟩
      have hx0 : x ∈ B0 := sphere_subset_closedBall ((h1inner x hxt).mp hxS)
      rw [hf0 hx0, hf0 hy0] at hxy
      exact hi0 hx0 hy0 hxy
    · have hx0 := hnotT hx hxt
      have hyS : f1 y ∈ S := hoverlap.subset
        ⟨by rw [← hfT hyt, ← hxy, hf0 hx0]; exact hmap0 hx0, hmap1 hyt⟩
      have hy0 : y ∈ B0 := sphere_subset_closedBall ((h1inner y hyt).mp hyS)
      rw [hf0 hx0, hf0 hy0] at hxy
      exact hi0 hx0 hy0 hxy
    · have hx0 := hnotT hx hxt
      have hy0 := hnotT hy hyt
      rw [hf0 hx0, hf0 hy0] at hxy
      exact hi0 hx0 hy0 hxy
  have himage : f '' B = K := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      apply hcover.subset
      by_cases hzt : z ∈ T
      · exact Or.inr (by rw [hfT hzt]; exact hmap1 hzt)
      · have hz0 := hnotT hz hzt
        exact Or.inl (by rw [hf0 hz0]; exact hmap0 hz0)
    · intro x hx
      rcases hcover.symm.subset hx with hx0 | hx1
      · obtain ⟨z, hz, rfl⟩ := him0.symm.subset hx0
        exact ⟨z, hB0B hz, hf0 hz⟩
      · obtain ⟨z, hz, rfl⟩ := him1.symm.subset hx1
        exact ⟨z, hTB hz, hfT hz⟩
  have hboundary (x : B) : f x ∈ Bdy ↔ (x : V3) ∈ Q := by
    by_cases hxt : (x : V3) ∈ T
    · rw [hfT hxt]
      exact h1outer x hxt
    · have hx0 := hnotT x.property hxt
      have hnf : f x ∉ Bdy := by
        rw [hf0 hx0]
        exact Set.disjoint_left.mp hCfront (hmap0 hx0)
      have hnq : (x : V3) ∉ Q := fun h => hxt (hQT h)
      simp only [hnf, hnq]
  let : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : V3) 1)
  let H : B ≃ₜ f '' B := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn f B hfi) (hc.domRestrict.subtype_mk _)
  exact ⟨{
    boundary_subset := hBdy
    parametrization := H.trans (Homeomorph.setCongr himage)
    map := f
    map_eq := fun _ => rfl
    piecewiseAffine := hf
    boundary_eq := hboundary
  }⟩

theorem exists_chartwisePLBall_of_cube_shell
    (hcover_e : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJT : J.space = T)
    (hcover : C ∪ N = K) (hoverlap : C ∩ N = S)
    (hCfront : Disjoint C (frontier K))
    (f0 f1 : V3 → X)
    (h0 : PolyhedralPLInCharts e f0 B0) (h1 : PolyhedralPLInCharts e f1 T)
    (hi0 : InjOn f0 B0) (hi1 : InjOn f1 T)
    (him0 : f0 '' B0 = C) (him1 : f1 '' T = N)
    (h1inner : ∀ x ∈ T, f1 x ∈ S ↔ x ∈ Q0)
    (h1outer : ∀ x ∈ T, f1 x ∈ frontier K ↔ x ∈ Q)
    (hagree : EqOn f0 f1 Q0) : Nonempty (ChartwisePLBall e K (frontier K)) := by
  have hC : IsCompact C := him0 ▸
    (isCompact_closedBall (0 : V3) (7 / 8)).image_of_continuousOn h0.continuousOn
  have hT : IsCompact T := hJT ▸ J.isCompact_space_of_finite hJ
  have hN : IsCompact N := him1 ▸ hT.image_of_continuousOn h1.continuousOn
  have hK : IsCompact K := hcover ▸ hC.union hN
  exact exists_chartwisePLBall_of_marked_cube_shell hcover_e hcompat J hJ hJT
    hcover hoverlap hK.isClosed.frontier_subset hCfront f0 f1 h0 h1 hi0 hi1
    him0 him1 h1inner h1outer hagree

end PoincareConjecture.M76
