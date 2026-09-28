import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.RegularCocoreSection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "ClosedCube" => Set.prod (Set.prod (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1)) (Icc (-1 : ℝ) 1)
local notation "OpenCube" => Set.prod (Set.prod (Ioo (-1 : ℝ) 1) (Ioo (-1 : ℝ) 1)) (Ioo (-1 : ℝ) 1)

theorem exists_cocore_window_from_lateral_incidence
    {X : Type*} [TopologicalSpace X] [T2Space X] {S R : Set X}
    (hS : IsClosed S) (hSR : S ⊆ interior R)
    (p : P3 → X) (hp : ContinuousOn p ClosedCube)
    (hlateral : ∀ z ∈ ClosedCube,
      (|z.1.1| = 1 ∨ |z.1.2| = 1) → p z ∈ frontier R)
    (hinner : MapsTo p OpenCube (interior R))
    (Q : OpenPartialHomeomorph X V3) (H : V3 ≃ᴬ[ℝ] P3)
    (hQT : Q.target = H ⁻¹' OpenCube)
    (hvalues : ∀ z ∈ OpenCube, Q.symm (H.symm z) = p z) :
    ∃ J : SimplicialComplex ℝ V3,
      J.faces.Finite ∧ J.space ⊆ Q.target ∧ Convex ℝ J.space ∧
      MapsTo Q.symm J.space (interior R) ∧
      (∀ x ∈ Q '' (S ∩ Q.source) ∩ J.space,
        (H x).2 ∈ Ioo (-(1/2 : ℝ)) (1/2) → x ∈ interior J.space) ∧
      ∀ z ∈ ClosedCube, z.2 ∈ Ioo (-(1/2 : ℝ)) (1/2) → p z ∈ S →
        H.symm z ∈ interior J.space := by
  let C : Set P3 := (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ Icc (-(3/4 : ℝ)) (3/4)
  have hC : IsCompact C := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hCcube : C ⊆ ClosedCube := by
    intro z hz
    exact ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
  let T : Set P3 := C ∩ p ⁻¹' S
  have hT : IsCompact T := hC.of_isClosed_subset
    ((hp.mono hCcube).preimage_isClosed_of_isClosed hC.isClosed hS) inter_subset_left
  let f : P3 → ℝ := fun z => max |z.1.1| |z.1.2|
  have hf : Continuous f := (continuous_abs.comp (continuous_fst.comp continuous_fst)).max
    (continuous_abs.comp (continuous_snd.comp continuous_fst))
  have hflt : ∀ z ∈ T, f z < 1 := by
    intro z hz
    have hz0 : |z.1.1| ≤ 1 := abs_le.mpr hz.1.1.1
    have hz1 : |z.1.2| ≤ 1 := abs_le.mpr hz.1.1.2
    have hne0 : |z.1.1| ≠ 1 := fun heq =>
      (hlateral z (hCcube hz.1) (Or.inl heq)).2 (hSR hz.2)
    have hne1 : |z.1.2| ≠ 1 := fun heq =>
      (hlateral z (hCcube hz.1) (Or.inr heq)).2 (hSR hz.2)
    exact max_lt (lt_of_le_of_ne hz0 hne0) (lt_of_le_of_ne hz1 hne1)
  obtain ⟨r,hr0,hr1,hfr⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ z ∈ T, f z < r := by
    rcases T.eq_empty_or_nonempty with hTe | hTne
    · exact ⟨1/2,by norm_num,by norm_num,fun z hz => (hTe ▸ hz).elim⟩
    · obtain ⟨z,hz,hmax⟩ := hT.exists_isMaxOn hTne hf.continuousOn
      have hpos : 0 ≤ f z := le_trans (abs_nonneg _) (le_max_left _ _)
      refine ⟨(f z+1)/2,by linarith,by linarith [hflt z hz],?_⟩
      intro w hw
      have hle : f w ≤ f z := hmax hw
      linarith [hflt z hz]
  let B : Set P3 := (Icc (-r) r ×ˢ Icc (-r) r) ×ˢ Icc (-(3/4 : ℝ)) (3/4)
  have hBcube : B ⊆ OpenCube := by
    intro z hz
    exact ⟨⟨⟨by linarith [hz.1.1.1],by linarith [hz.1.1.2]⟩,
      ⟨by linarith [hz.1.2.1],by linarith [hz.1.2.2]⟩⟩,
      ⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩⟩
  have hBcv : Convex ℝ B := (convex_Icc (-r) r).prod (convex_Icc (-r) r) |>.prod
    (convex_Icc (-(3/4 : ℝ)) (3/4))
  have hBpair := ((isFinitePLBallPair_Icc (show -r < r by linarith)).prod
    (isFinitePLBallPair_Icc (show -r < r by linarith))).prod
    (isFinitePLBallPair_Icc (show -(3/4 : ℝ) < 3/4 by norm_num))
  have himage := hBpair.affine_image H.symm.toContinuousAffineMap H.symm.injective.injOn
  obtain ⟨J,_,hJ,hJs,_⟩ := himage.exists_finite_carrier_and_rim_complexes
  have hJspace : J.space = H ⁻¹' B := by
    rw [hJs]
    exact congrFun H.toHomeomorph.image_symm B
  have hBint : interior B = (Ioo (-r) r ×ˢ Ioo (-r) r) ×ˢ Ioo (-(3/4 : ℝ)) (3/4) := by
    simp only [B, interior_prod_eq, interior_Icc]
  have hcontact : ∀ z ∈ ClosedCube, z.2 ∈ Ioo (-(1/2 : ℝ)) (1/2) → p z ∈ S →
      z ∈ interior B := by
    intro z hz hzt hzS
    have hzT : z ∈ T := ⟨⟨hz.1,by constructor <;> linarith [hzt.1,hzt.2]⟩,hzS⟩
    have hfz := hfr z hzT
    have hz0 : |z.1.1| < r := (le_max_left _ _).trans_lt hfz
    have hz1 : |z.1.2| < r := (le_max_right _ _).trans_lt hfz
    rw [hBint]
    exact ⟨⟨abs_lt.mp hz0,abs_lt.mp hz1⟩,by constructor <;> linarith [hzt.1,hzt.2]⟩
  have hJint : interior J.space = H ⁻¹' interior B := by
    rw [hJspace]
    exact (H.toHomeomorph.preimage_interior B).symm
  refine ⟨J,hJ,?_,?_,?_,?_,?_⟩
  · rw [hJspace,hQT]
    exact preimage_mono hBcube
  · rw [hJspace]
    exact hBcv.affine_preimage H.toAffineEquiv.toAffineMap
  · intro x hx
    have hxB := hJspace.subset hx
    have hv := hvalues (H x) (hBcube hxB)
    rw [H.symm_apply_apply] at hv
    rw [hv]
    exact hinner (hBcube hxB)
  · intro x hx hxt
    rw [hJint]
    obtain ⟨y,⟨hyS,hyQ⟩,hyx⟩ := hx.1
    have hxB := hJspace.subset hx.2
    have hxo := hBcube hxB
    have hxc : H x ∈ ClosedCube :=
      ⟨⟨⟨hxo.1.1.1.le,hxo.1.1.2.le⟩,⟨hxo.1.2.1.le,hxo.1.2.2.le⟩⟩,
        ⟨hxo.2.1.le,hxo.2.2.le⟩⟩
    apply hcontact (H x) hxc hxt
    rw [← hvalues (H x) hxo,H.symm_apply_apply,← hyx,Q.left_inv hyQ]
    exact hyS
  · intro z hz hzt hzS
    rw [hJint]
    change H (H.symm z) ∈ interior B
    rw [H.apply_symm_apply]
    exact hcontact z hz hzt hzS

theorem ChartwisePLSphere.exists_one_handle_cocore_innermost_disk
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S R : Set X}
    (s : ChartwisePLSphere e S) (hSR : S ⊆ interior R)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (p : P3 → X) (hp : ContinuousOn p ClosedCube)
    (hlateral : ∀ z ∈ ClosedCube,
      (|z.1.1| = 1 ∨ |z.1.2| = 1) → p z ∈ frontier R)
    (hinner : MapsTo p OpenCube (interior R))
    (Q : OpenPartialHomeomorph X V3) (H : V3 ≃ᴬ[ℝ] P3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hQT : Q.target = H ⁻¹' OpenCube)
    (hvalues : ∀ z ∈ OpenCube, Q.symm (H.symm z) = p z) :
    ∃ t ∈ Ioo (-(1/2 : ℝ)) (1/2),
      Disjoint S (p '' ((Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ {t})) ∨
      ∃ B q : Set V3, IsFinitePLBallPair (ℝ × ℝ) B q ∧
        B ⊆ Q.target ∧
        PolyhedralPLInCharts e Q.symm B ∧ InjOn Q.symm B ∧
        MapsTo Q.symm B (interior R) ∧
        Q.symm '' B ⊆ p '' ((Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) ×ˢ {t}) ∧
        (∀ x ∈ B, Q.symm x ∈ S ↔ x ∈ q) := by
  obtain ⟨J,hJ,hJQ,hJcv,hJR,hband,hall⟩ := exists_cocore_window_from_lateral_incidence
    s.isCompact.isClosed hSR p hp hlateral hinner Q H hQT hvalues
  obtain ⟨t,ht,hempty | ⟨B,q,hB,hBsub,hPL,hi,hBR,hproper⟩⟩ :=
    s.exists_original_cocore_innermost_disk Q hcover hQ J hJ hJQ hJcv hJR H
      (by norm_num) hband
  · refine ⟨t,ht,Or.inl ?_⟩
    apply disjoint_left.mpr
    rintro y hyS ⟨z,hz,rfl⟩
    have hzt : z.2 = t := hz.2
    have hzcube : z ∈ ClosedCube := ⟨hz.1,by constructor <;> linarith [ht.1,ht.2]⟩
    have hxJ := hall z hzcube (hzt ▸ ht) hyS
    have hxT := hJQ (interior_subset hxJ)
    have hzo : z ∈ OpenCube := by
      have h := hQT.subset hxT
      change H (H.symm z) ∈ OpenCube at h
      simpa only [H.apply_symm_apply] using h
    have hxs : Q.symm (H.symm z) ∈ S := (hvalues z hzo).symm ▸ hyS
    have hx : H.symm z ∈ (Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t} := by
      refine ⟨⟨⟨Q.symm (H.symm z),⟨hxs,Q.map_target hxT⟩,Q.right_inv hxT⟩,
        interior_subset hxJ⟩,?_⟩
      change (H (H.symm z)).2 = t
      simpa only [H.apply_symm_apply] using hzt
    exact (hempty ▸ hx).elim
  · refine ⟨t,ht,Or.inr ⟨B,q,hB,fun _ hx => hJQ (interior_subset (hBsub hx).1),
      hPL,hi,hBR,?_,hproper⟩⟩
    rintro _ ⟨x,hx,rfl⟩
    have hxo := hQT.subset (hJQ (interior_subset (hBsub hx).1))
    have hxc : (H x).1 ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨⟨hxo.1.1.1.le,hxo.1.1.2.le⟩,⟨hxo.1.2.1.le,hxo.1.2.2.le⟩⟩
    refine ⟨H x,⟨hxc,(hBsub hx).2⟩,?_⟩
    have h := hvalues (H x) hxo
    simpa only [H.symm_apply_apply] using h.symm

end PoincareConjecture.M76
