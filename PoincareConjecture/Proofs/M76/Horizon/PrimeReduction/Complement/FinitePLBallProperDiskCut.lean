import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ProperDiskSelectedHole
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.OriginalDiskCutCollars
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteConvexDomain

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Cube" => closedBall (0 : V3) 1
local notation "atlas" => (fun _ : Unit => OpenPartialHomeomorph.refl V3)

theorem OriginalDiskProduct.finitePiecewiseAffineOn_standard
    {R : Set V3} {j : V2 → V3} (P : OriginalDiskProduct atlas R j) :
    FinitePiecewiseAffineOn P.map (Disk ×ˢ Icc (-1 : ℝ) 1) := by
  have hD : IsFinitePLBallPair V2 Disk (sphere (0 : V2) 1) :=
    isFinitePLBallPair_unit_cube
  obtain ⟨K, _, hK, hKs, _, _⟩ := hD.exists_finite_carrier_and_rim_complexes
  obtain ⟨L, _, hL, hLs, _, _⟩ :=
    (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).exists_finite_carrier_and_rim_complexes
  obtain ⟨J, hJ, hJs, _⟩ := K.exists_finite_triangulation_prod L hK hL
  rw [hKs, hLs] at hJs
  have hP : PolyhedralPLInCharts atlas P.map J.space := hJs.symm ▸ P.polyhedral
  have hcoord : ∀ i : Unit, LocallyPiecewiseAffineOn
      (id ∘ (atlas i).symm) (atlas i).target :=
    fun _ => locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ V3) isOpen_univ
  exact hJs ▸ hP.finitePiecewiseAffineOn_comp J hJ hcoord

private theorem finitePL_standard_chartwise
    {f : V2 → V3} (hf : FinitePiecewiseAffineOn f Disk) :
    PolyhedralPLInCharts atlas f Disk := by
  refine ⟨hf.continuousOn, ?_⟩
  obtain ⟨K, hK, hKs, hKf⟩ := hf
  intro x
  refine ⟨(), K, univ, hK, hKs.subset, isOpen_univ, mem_univ _, ?_, ?_, ?_⟩
  · rintro _ ⟨z, _, rfl⟩
    exact hKs.symm ▸ z.property
  · exact fun _ _ => mem_univ _
  · exact ⟨K, hK, rfl, hKf⟩

private theorem cube_plDomain : PLDomain atlas Cube := by
  have hb : IsFinitePLBallPair V3 Cube (frontier Cube) := by
    rw [frontier_closedBall _ one_ne_zero]
    exact isFinitePLBallPair_unit_cube
  obtain ⟨K, _, hK, hKs, _, _⟩ := hb.exists_finite_carrier_and_rim_complexes
  have hp : (1 : V3) ∈ frontier Cube := by
    rw [frontier_closedBall _ one_ne_zero, mem_sphere_zero_iff_norm]
    simp
  have hm : (-1 : V3) ∈ frontier Cube := by
    rw [frontier_closedBall _ one_ne_zero, mem_sphere_zero_iff_norm]
    simp
  exact K.plDomain_convex_of_frontier_points hK (isCompact_closedBall _ _)
    (convex_closedBall _ _) ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
    hKs hp hm (by intro h; have hh := congrFun h 0; norm_num at hh)

theorem exists_finitePL_ball_proper_disk_cut
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    {B r d b : Set E} (hB : IsFinitePLBallPair V3 B r)
    (hd : IsFinitePLBallPair V2 d b) (hdB : d ⊆ B) (hdr : d ∩ r = b)
    (a : ι → Set E) (ha : ∀ i, IsCompact (a i)) (haB : ∀ i, a i ⊆ B)
    (hda : ∀ i, Disjoint d (a i)) :
    ∃ (C : B ≃ₜ Cube) (f : E → V3) (j : V2 → V3),
      C.IsFinitePL ∧ FinitePiecewiseAffineOn f B ∧
      (∀ x : B, (C x : V3) = f x) ∧
      (∀ x : B, (x : E) ∈ r ↔ (C x : V3) ∈ frontier Cube) ∧
      j '' Disk = f '' d ∧ j '' sphere (0 : V2) 1 = f '' b ∧
      ∃ P : OriginalDiskProduct atlas Cube j,
        (∀ i, Disjoint (P.map '' (Disk ×ˢ Icc (-1 : ℝ) 1)) (f '' a i)) ∧
        IsOpen ((Subtype.val : Cube → V3) ⁻¹' P.openStrip) ∧
        PLDomain atlas P.cutCarrier ∧ IsCompact P.cutCarrier ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          IsOpen ((Subtype.val : Cube → V3) ⁻¹'
            (P.map '' (Disk ×ˢ Ioo (-ε) ε))) ∧
          IsOpen ((Subtype.val : frontier Cube → V3) ⁻¹'
            (P.map '' (sphere (0 : V2) 1 ×ˢ Ioo (-ε) ε))) := by
  classical
  obtain ⟨C, hC, hCr⟩ := hB.exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
  obtain ⟨f, hf, hCf⟩ := hC
  have hC : C.IsFinitePL := ⟨f, hf, hCf⟩
  have hfi : InjOn f B := by
    intro x hx y hy hxy
    have hh : C ⟨x, hx⟩ = C ⟨y, hy⟩ :=
      Subtype.ext (by simpa only [hCf] using hxy)
    exact congrArg Subtype.val (C.injective hh)
  obtain ⟨D, hD, hDb⟩ := hd.exists_cube_chart (ContinuousLinearEquiv.refl ℝ V2)
  obtain ⟨g, hg, hDg⟩ := hD.symm
  have hgd : MapsTo g Disk d := fun x hx => (hDg ⟨x, hx⟩) ▸ (D.symm ⟨x, hx⟩).property
  let j := f ∘ g
  have hj : FinitePiecewiseAffineOn j Disk := hf.comp hg (hgd.mono_right hdB)
  have hjC : MapsTo j Disk Cube := by
    intro x hx
    rw [show j x = f (g x) from rfl, ← hCf ⟨g x, hdB (hgd hx)⟩]
    exact (C ⟨g x, hdB (hgd hx)⟩).property
  have hgi : InjOn g Disk := by
    intro x hx y hy hxy
    have hh : D.symm ⟨x, hx⟩ = D.symm ⟨y, hy⟩ :=
      Subtype.ext (by simpa only [hDg] using hxy)
    exact congrArg Subtype.val (D.symm.injective hh)
  have hji : InjOn j Disk := hfi.comp hgi (hgd.mono_right hdB)
  have hjemb : Topology.IsEmbedding (fun z : Disk => j z) :=
    ((hj.continuousOn.comp_continuous continuous_subtype_val
      (fun z => z.property)).isClosedEmbedding
      (fun x y h => Subtype.ext (hji x.property y.property h))).isEmbedding
  have hproper : ∀ z : Disk, j z ∈ frontier Cube ↔ (z : V2) ∈ sphere 0 1 := by
    intro z
    change f (g z) ∈ frontier Cube ↔ _
    rw [← hCf ⟨g z, hdB (hgd z.property)⟩, ← hCr]
    have hb : g z ∈ r ↔ g z ∈ b := by
      rw [← hdr]
      exact (and_iff_right (hgd z.property)).symm
    rw [hb, ← hDg z, hDb, D.apply_symm_apply, frontier_closedBall _ one_ne_zero]
  have hgdimage : g '' Disk = d := by
    apply Subset.antisymm (image_subset_iff.mpr hgd)
    intro x hx
    refine ⟨D ⟨x, hx⟩, (D ⟨x, hx⟩).property, ?_⟩
    rw [← hDg, D.symm_apply_apply]
  have hjimage : j '' Disk = f '' d := by rw [image_comp, hgdimage]
  have hgbimage : g '' sphere (0 : V2) 1 = b := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [← hDg ⟨z, sphere_subset_closedBall hz⟩, hDb, D.apply_symm_apply,
        frontier_closedBall _ one_ne_zero]
      exact hz
    · intro x hx
      refine ⟨D ⟨x, hd.1 hx⟩, ?_, ?_⟩
      · rw [← frontier_closedBall _ one_ne_zero]
        exact (hDb ⟨x, hd.1 hx⟩).mp hx
      · rw [← hDg, D.symm_apply_apply]
  have hjbimage : j '' sphere (0 : V2) 1 = f '' b := by rw [image_comp, hgbimage]
  let U := (⋃ i, f '' a i)ᶜ
  have hU : IsOpen U := (isClosed_iUnion_of_finite fun i =>
    ((ha i).image_of_continuousOn (hf.continuousOn.mono (haB i))).isClosed).isOpen_compl
  have hjU : j '' Disk ⊆ U := by
    rw [hjimage]
    rintro _ ⟨x, hx, rfl⟩ hy
    obtain ⟨i, y, hy, heq⟩ := mem_iUnion.mp hy
    exact disjoint_left.mp (hda i) hx (hfi (haB i hy) (hdB hx) heq ▸ hy)
  obtain ⟨P, hPU, hopen, hPL, hc, _, _, _, _, _, hcollars⟩ :=
    exists_original_disk_cut_domain_with_collars (isCompact_closedBall _ _) cube_plDomain
      (finitePL_standard_chartwise hj) hjemb hjC hproper hU hjU
  refine ⟨C, f, j, hC, hf, hCf, hCr, hjimage, hjbimage, P, ?_, hopen, hPL, hc, hcollars⟩
  intro i
  apply disjoint_left.mpr
  rintro x ⟨z, hz, rfl⟩ hx
  exact hPU hz (mem_iUnion.mpr ⟨i, hx⟩)

local notation "V4" => (Fin 4 → ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere

theorem exists_selected_hole_original_disk_cut
    {ι : Type*} [Finite ι] (a r : ι → Set V4)
    (ha : ∀ i, IsFinitePLBallPair V3 (a i) (r i))
    (haS : ∀ i, a i ⊆ Sphere)
    (hopen : ∀ i, IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (a i \ r i)))
    (hdis : Pairwise fun i j => Disjoint (a i) (a j))
    {d b : Set V4} (hd : IsFinitePLBallPair V2 d b)
    (hdQ : d ⊆ Sphere \ ⋃ i, a i \ r i)
    (hproper : d ∩ ⋃ i, r i = b) :
    ∃ i, (∀ k, b ⊆ r k ↔ k = i) ∧
      IsFinitePLBallPair V3 (Sphere \ (a i \ r i)) (r i) ∧
      ((Sphere \ (a i \ r i)) \ ⋃ k : {k : ι // k ≠ i}, a k \ r k) =
        Sphere \ ⋃ k, a k \ r k ∧
      ∃ (C : ↥(Sphere \ (a i \ r i)) ≃ₜ Cube) (f : V4 → V3) (j : V2 → V3),
        C.IsFinitePL ∧ FinitePiecewiseAffineOn f (Sphere \ (a i \ r i)) ∧
        (∀ x : ↥(Sphere \ (a i \ r i)), (C x : V3) = f x) ∧
        (∀ x : ↥(Sphere \ (a i \ r i)), (x : V4) ∈ r i ↔
          (C x : V3) ∈ frontier Cube) ∧
        j '' Disk = f '' d ∧ j '' sphere (0 : V2) 1 = f '' b ∧
        ∃ P : OriginalDiskProduct atlas Cube j,
          (∀ k, k ≠ i →
            Disjoint (P.map '' (Disk ×ˢ Icc (-1 : ℝ) 1)) (f '' a k)) ∧
          IsOpen ((Subtype.val : Cube → V3) ⁻¹' P.openStrip) ∧
          PLDomain atlas P.cutCarrier ∧ IsCompact P.cutCarrier ∧
          ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            IsOpen ((Subtype.val : Cube → V3) ⁻¹'
              (P.map '' (Disk ×ˢ Ioo (-ε) ε))) ∧
            IsOpen ((Subtype.val : frontier Cube → V3) ⁻¹'
              (P.map '' (sphere (0 : V2) 1 ×ˢ Ioo (-ε) ε))) := by
  classical
  obtain ⟨i, hi, hB, hdB, hdb, _, hda, haB, heq⟩ :=
    hd.exists_selected_hole_for_proper_disk a r ha haS hopen hdis hdQ hproper
  obtain ⟨C, f, j, hC, hf, hCf, hCr, hjd, hjb, P, hPa, hPo, hPL, hc, hcollars⟩ :=
    exists_finitePL_ball_proper_disk_cut hB hd hdB hdb
      (fun k : {k : ι // k ≠ i} => a k)
      (fun k => (ha k).isCompact) (fun k => (haB k).trans sdiff_subset)
      (fun k => hda k k.property)
  exact ⟨i, hi, hB, heq, C, f, j, hC, hf, hCf, hCr, hjd, hjb, P,
    fun k hk => hPa ⟨k, hk⟩, hPo, hPL, hc, hcollars⟩

end PoincareConjecture.M76
