import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.Capping.RelativeClosedCover
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.BoundaryConeCaps
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
open Set Metric Geometry BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

open Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in

theorem exists_boundaryCircleCap_local_collar (S : Set E) (x : S) :
    ∃ c : OpenPartialHomeomorph (S × Ico (0 : ℝ) 1) (boundaryCircleCap true S),
      collarBase x ∈ c.source ∧
        ∀ y, collarBase y ∈ c.source → (c (collarBase y) : E × ℝ) = ((y : E), 0) := by
  let D := boundaryCircleCap true S
  let W : TopologicalSpace.Opens D :=
    ⟨{z | (z : E × ℝ).2 < 1}, isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const⟩
  have hnormal (z : W) : (1 - (z.val : E × ℝ).2)⁻¹ • (z.val : E × ℝ).1 ∈ S := by
    obtain ⟨y, hy, r, hr, heq⟩ := (mem_boundaryCircleCap_iff true S z.val).mp z.val.property
    have ht : (z.val : E × ℝ).2 < 1 := z.property
    rw [heq] at ht
    have hr0 : r ≠ 0 := by simp only [capSign, if_true, one_mul] at ht; linarith
    rw [heq]
    simpa only [capSign, if_true, one_mul, Prod.fst, Prod.snd, sub_sub_cancel,
      smul_smul, inv_mul_cancel₀ hr0, one_smul] using hy
  have hheight (z : D) : 0 ≤ (z : E × ℝ).2 := by
    obtain ⟨y, hy, r, hr, heq⟩ := (mem_boundaryCircleCap_iff true S z).mp z.property
    rw [heq]
    simp only [capSign, if_true, one_mul]
    linarith [hr.2]
  have hden (z : W) : 1 - (z.val : E × ℝ).2 ≠ 0 := by
    have ht : (z.val : E × ℝ).2 < 1 := z.property
    linarith
  let F : (S × Ico (0 : ℝ) 1) ≃ₜ W := {
    toFun := fun z => ⟨⟨((1 - (z.2 : ℝ)) • (z.1 : E), (z.2 : ℝ)),
      (mem_boundaryCircleCap_iff true S _).mpr
        ⟨z.1, z.1.property, 1 - (z.2 : ℝ), ⟨by linarith [z.2.property.2], by linarith [z.2.property.1]⟩,
          by simp [capSign]⟩⟩, z.2.property.2⟩
    invFun := fun z => (⟨_, hnormal z⟩, ⟨(z.val : E × ℝ).2, hheight z.val, z.property⟩)
    left_inv := by
      intro z
      apply Prod.ext
      · apply Subtype.ext
        change (1 - (z.2 : ℝ))⁻¹ • ((1 - (z.2 : ℝ)) • (z.1 : E)) = z.1
        rw [smul_smul, inv_mul_cancel₀ (by linarith [z.2.property.2]), one_smul]
      · rfl
    right_inv := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · change (1 - (z.val : E × ℝ).2) •
          ((1 - (z.val : E × ℝ).2)⁻¹ • (z.val : E × ℝ).1) = (z.val : E × ℝ).1
        rw [smul_smul, mul_inv_cancel₀ (hden z), one_smul]
      · rfl
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
        (continuous_subtype_val.comp continuous_fst)).prodMk
          (continuous_subtype_val.comp continuous_snd)
    continuous_invFun := by
      have hz : Continuous (fun z : W => (z.val : E × ℝ)) :=
        continuous_subtype_val.comp continuous_subtype_val
      exact (((continuous_const.sub (continuous_snd.comp hz)).inv₀ hden).smul
        (continuous_fst.comp hz)).subtype_mk _ |>.prodMk
          ((continuous_snd.comp hz).subtype_mk _) }
  let iW := W.openPartialHomeomorphSubtypeCoe ⟨F (collarBase x)⟩
  let c := F.toOpenPartialHomeomorph.trans iW
  have hc : c.source = univ := by
    simp only [c, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      show iW.source = univ from rfl, preimage_univ, inter_univ]
  refine ⟨c, hc.symm ▸ mem_univ _, ?_⟩
  intro y _
  change ((1 - (0 : ℝ)) • (y : E), (0 : ℝ)) = ((y : E), 0)
  simp only [sub_zero, one_smul]

theorem boundaryCircleCap_isSimplyConnected
    {S : Set E} (gamma : sphere (0 : Fin 2 → ℝ) 1 ≃ₜ S) (hgamma : gamma.IsFinitePL) :
    IsSimplyConnected (boundaryCircleCap true S) := by
  obtain ⟨_, A, _, hAcv, hAne, H, _, _⟩ := isFinitePLBallPair_boundaryCircleCap true gamma hgamma
  let : ContractibleSpace A := hAcv.contractibleSpace (hAne.mono interior_subset)
  exact H.toHomotopyEquiv.simplyConnectedSpace

theorem isSimplyConnected_finite_boundaryCircleCap
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L ≤ K)
    (hKp : IsPathConnected K.space)
    (gamma : sphere (0 : Fin 2 → ℝ) 1 ≃ₜ L.space) (hgamma : gamma.IsFinitePL)
    (b : L.space)
    (hgenerate : Function.Surjective (FundamentalGroup.map
      (ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le hLK)) b))
    (hlocal : ∀ x : L.space,
      ∃ c : OpenPartialHomeomorph (L.space × Ico (0 : ℝ) 1) K.space,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source →
            c (collarBase a) = Set.inclusion (SimplicialComplex.space_subset_of_le hLK) a) :
    IsSimplyConnected ((fun x : E => (x, (0 : ℝ))) '' K.space ∪ boundaryCircleCap true L.space) := by
  let N : Set (E × ℝ) := K.space ×ˢ ({0} : Set ℝ)
  let D := boundaryCircleCap true L.space
  have hKc := K.isCompact_space_of_finite hK
  have hLc := L.isCompact_space_of_finite (hK.subset hLK)
  have hND : N ∩ D = L.space ×ˢ ({0} : Set ℝ) := by
    apply Subset.antisymm
    · intro z hz
      exact (boundaryCircleCap_plane true L.space).subset ⟨hz.2, mem_univ _, hz.1.2⟩
    · intro z hz
      exact ⟨⟨SimplicialComplex.space_subset_of_le hLK hz.1, hz.2⟩,
        ((boundaryCircleCap_plane true L.space).symm.subset hz).1⟩
  let HK : N ≃ₜ K.space := {
    toFun := fun x => ⟨x.val.1, x.property.1⟩
    invFun := fun x => ⟨(x, 0), x.property, rfl⟩
    left_inv := fun x => Subtype.ext (Prod.ext rfl x.property.2.symm)
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.prodMk continuous_const).subtype_mk _ }
  let HB : ↥(N ∩ D) ≃ₜ L.space := {
    toFun := fun x => ⟨x.val.1, (hND.subset x.property).1⟩
    invFun := fun x => ⟨(x, 0), hND.symm.subset ⟨x.property, rfl⟩⟩
    left_inv := fun x => Subtype.ext (Prod.ext rfl (hND.subset x.property).2.symm)
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.prodMk continuous_const).subtype_mk _ }
  have hNp : IsPathConnected N := by
    let : PathConnectedSpace K.space := isPathConnected_iff_pathConnectedSpace.mp hKp
    exact isPathConnected_iff_pathConnectedSpace.mpr
      (pathConnectedSpace_of_homotopyEquiv HK.symm.toHomotopyEquiv)
  have hLp : IsPathConnected L.space := by
    have hs : IsPathConnected (sphere (0 : Fin 2 → ℝ) 1) :=
      isPathConnected_sphere (by simp) _ (by norm_num)
    let : PathConnectedSpace (sphere (0 : Fin 2 → ℝ) 1) :=
      isPathConnected_iff_pathConnectedSpace.mp hs
    exact isPathConnected_iff_pathConnectedSpace.mpr
      (pathConnectedSpace_of_homotopyEquiv gamma.toHomotopyEquiv)
  have hWp : IsPathConnected (N ∩ D) := by
    let : PathConnectedSpace L.space := isPathConnected_iff_pathConnectedSpace.mp hLp
    exact isPathConnected_iff_pathConnectedSpace.mpr
      (pathConnectedSpace_of_homotopyEquiv HB.symm.toHomotopyEquiv)
  have hlocalN : ∀ x : ↥(N ∩ D),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ D) × Ico (0 : ℝ) 1) N,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_left a := by
    intro x
    obtain ⟨c, hx, hc⟩ := hlocal (HB x)
    let H := HB.prodCongr (Homeomorph.refl (Ico (0 : ℝ) 1))
    refine ⟨(H.transOpenPartialHomeomorph c).transHomeomorph HK.symm, hx, ?_⟩
    intro a ha
    change HK.symm (c (collarBase (HB a))) = Set.inclusion inter_subset_left a
    rw [hc (HB a) ha]
    apply HK.injective
    rw [HK.apply_symm_apply]
    rfl
  have hlocalD : ∀ x : ↥(N ∩ D),
      ∃ c : OpenPartialHomeomorph (↥(N ∩ D) × Ico (0 : ℝ) 1) D,
        collarBase x ∈ c.source ∧
          ∀ a, collarBase a ∈ c.source → c (collarBase a) = Set.inclusion inter_subset_right a := by
    intro x
    obtain ⟨c, hx, hc⟩ := exists_boundaryCircleCap_local_collar L.space (HB x)
    let H := HB.prodCongr (Homeomorph.refl (Ico (0 : ℝ) 1))
    refine ⟨H.transOpenPartialHomeomorph c, hx, ?_⟩
    intro a ha
    apply Subtype.ext
    change (c (collarBase (HB a)) : E × ℝ) = (a : E × ℝ)
    rw [hc (HB a) ha]
    exact Prod.ext rfl (hND.subset a.property).2.symm
  let b' : ↥(N ∩ D) := HB.symm b
  have hgen : Function.Surjective (FundamentalGroup.map
      (ContinuousMap.inclusion (inter_subset_left : N ∩ D ⊆ N)) b') := by
    let bN : N := ContinuousMap.inclusion (inter_subset_left : N ∩ D ⊆ N) b'
    intro a
    obtain ⟨z, hz⟩ := hgenerate (FundamentalGroup.map (⟨HK, HK.continuous⟩ : C(N, K.space)) bN a)
    obtain ⟨d, hd⟩ := (FundamentalGroup.map_bijective_of_homotopyEquiv HB.toHomotopyEquiv b').2 z
    refine ⟨d, ?_⟩
    apply (FundamentalGroup.map_bijective_of_homotopyEquiv HK.toHomotopyEquiv bN).1
    change FundamentalGroup.map (⟨HK, HK.continuous⟩ : C(N, K.space))
      (ContinuousMap.inclusion (inter_subset_left : N ∩ D ⊆ N) b')
      (FundamentalGroup.map (ContinuousMap.inclusion (inter_subset_left : N ∩ D ⊆ N)) b' d) = _
    rw [← FundamentalGroup.map_comp_apply]
    change FundamentalGroup.map
      ((ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le hLK)).comp
        (⟨HB, HB.continuous⟩ : C(↥(N ∩ D), L.space))) b' d = _
    rw [FundamentalGroup.map_comp_apply]
    exact (congrArg (FundamentalGroup.map
      (ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le hLK)) b) hd).trans hz
  have hcap : IsSimplyConnected (N ∪ D) := isSimplyConnected_union_of_closed_cover_capping
    (hKc.isClosed.prod isClosed_singleton)
    (isFinitePLBallPair_boundaryCircleCap true gamma hgamma).isCompact.isClosed
    (hND.symm ▸ hLc.prod isCompact_singleton) hNp
    (boundaryCircleCap_isSimplyConnected gamma hgamma) hWp b' hgen hlocalN hlocalD
  have hplane : (fun x : E => (x, (0 : ℝ))) '' K.space = N := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, rfl⟩
    · intro hx
      exact ⟨x.1, hx.1, Prod.ext rfl hx.2.symm⟩
  rwa [hplane]

end PoincareConjecture.M76.HamiltonIntervalTorus
