import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalOppositeDiskDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.GlobalExteriorDiskProduct
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.OriginalDiskCutCollars









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem ChartwisePLSphere.exists_original_whole_disk_product
    {X ι E : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R S U V : Set X} {d q : Set E}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hU : IsOpen U) (hSU : S ⊆ U)
    (hd : IsFinitePLBallPair P2 d q) (j : E → X)
    (hj : PolyhedralPLInCharts e j d) (hji : InjOn j d)
    (hjR : MapsTo j d (interior R))
    (hproper : ∀ z ∈ d, j z ∈ S ↔ z ∈ q)
    (hV : IsOpen V) (hjV : j '' d ⊆ V) :
    ∃ (K B : Set X) (H : Disk ≃ₜ d) (k : V2 → X),
      IsCompact K ∧ PLDomain e K ∧ K ⊆ U ∩ interior R ∧
      Nonempty (ChartwisePLSphere e B) ∧ Disjoint S B ∧ frontier K = S ∪ B ∧
      K ∩ (j '' d) = j '' q ∧ H.IsFinitePL ∧
      (∀ z : Disk, k z = j (H z)) ∧
      (∀ z : Disk, (z : V2) ∈ Rim ↔ (H z : E) ∈ q) ∧
      k '' Disk = j '' d ∧ k '' Rim = j '' q ∧
      IsCompact (R ∩ (interior K)ᶜ) ∧ PLDomain e (R ∩ (interior K)ᶜ) ∧
      ∃ P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) k,
        MapsTo P.map (Disk ×ˢ I) (V ∩ interior R ∩ Bᶜ) ∧
        (∀ z ∈ Disk ×ˢ I, P.map z ∈ S ↔ z.1 ∈ Rim) ∧
        IsCompact P.cutCarrier ∧ PLDomain e P.cutCarrier ∧
        P.closedStrip ∩ K = P.map '' (Rim ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2)) ∧
        ∀ η : ℝ, 0 < η → η ≤ 1 →
          IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹'
            (P.map '' (Disk ×ˢ Ioo (-η) η))) ∧
          IsOpen ((Subtype.val : S → X) ⁻¹'
            (P.map '' (Rim ×ˢ Ioo (-η) η))) := by
  classical
  obtain ⟨K,B,hK,hKPL,hKU,⟨sB⟩,hSB,hfront,hcontact⟩ :=
    s.exists_original_opposite_finite_disk_domain hR he hSR hU hSU hd j hj.continuousOn hproper
  have hKR : K ⊆ interior R := hKU.trans inter_subset_right
  obtain ⟨hL,hLPL,_,hmeet,hLfront⟩ := he.interior_removal_geometry hR hKPL hKR
  have hjK (z : E) (hz : z ∈ d) : j z ∉ interior K := by
    intro hzK
    obtain ⟨w,hw,heq⟩ := hcontact.subset ⟨interior_subset hzK,⟨z,hz,rfl⟩⟩
    have hzS : j z ∈ S := heq ▸ (hproper w (hd.1 hw)).mpr hw
    exact (hfront.symm.subset (Or.inl hzS)).2 hzK
  have hjB : Disjoint (j '' d) B := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hxB
    have hxK := hKPL.closed.frontier_subset (hfront.symm.subset (Or.inr hxB))
    obtain ⟨w,hw,heq⟩ := hcontact.subset ⟨hxK,⟨z,hz,rfl⟩⟩
    exact disjoint_left.mp hSB (heq ▸ (hproper w (hd.1 hw)).mpr hw) hxB
  have hjproper (z : E) (hz : z ∈ d) : j z ∈ frontier (R ∩ (interior K)ᶜ) ↔ z ∈ q := by
    rw [hLfront,hfront]
    constructor
    · rintro ((hzS | hzB) | hzR)
      · exact (hproper z hz).mp hzS
      · exact False.elim (disjoint_left.mp hjB ⟨z,hz,rfl⟩ hzB)
      · exact False.elim (hzR.2 (hjR hz))
    · intro hzq
      exact Or.inl (Or.inl ((hproper z hz).mpr hzq))
  obtain ⟨H0,hH0,hHq⟩ := hd.exists_cube_chart (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  let H := H0.symm
  have hH : H.IsFinitePL := hH0.symm
  obtain ⟨u,hu,hHu⟩ := hH
  let k := j ∘ u
  have huD : MapsTo u Disk d := fun z hz => (hHu ⟨z,hz⟩) ▸ (H ⟨z,hz⟩).property
  have hkval (z : Disk) : k z = j (H z) := congrArg j (hHu z).symm
  have hkrim (z : Disk) : (z : V2) ∈ Rim ↔ (H z : E) ∈ q := by
    have hh := hHq (H z)
    rw [H0.apply_symm_apply,frontier_closedBall _ one_ne_zero] at hh
    exact hh.symm
  have hkPL : PolyhedralPLInCharts e k Disk := by
    have huCopy := hu
    obtain ⟨J,hJ,hJs,_⟩ := huCopy
    exact hJs ▸ hj.comp_finitePiecewiseAffineOn J hJ (hJs.symm ▸ hu)
      (fun z hz => huD (hJs.subset hz))
  let : CompactSpace Disk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hkemb : Topology.IsEmbedding (fun z : Disk => k z) := by
    apply (hkPL.continuousOn.domRestrict.isClosedEmbedding ?_).isEmbedding
    intro z w hzw
    have hh := hji (H z).property (H w).property ((hkval z).symm.trans (hzw.trans (hkval w)))
    exact H.injective (Subtype.ext hh)
  have hkimage : k '' Disk = j '' d := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact ⟨H ⟨z,hz⟩,(H ⟨z,hz⟩).property,(hkval ⟨z,hz⟩).symm⟩
    · rintro _ ⟨z,hz,rfl⟩
      refine ⟨H.symm ⟨z,hz⟩,(H.symm ⟨z,hz⟩).property,?_⟩
      rw [hkval,H.apply_symm_apply]
  have hkrimimage : k '' Rim = j '' q := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact ⟨H ⟨z,sphere_subset_closedBall hz⟩,(hkrim _).mp hz,(hkval _).symm⟩
    · rintro _ ⟨z,hz,rfl⟩
      refine ⟨H.symm ⟨z,hd.1 hz⟩,(hkrim _).mpr ?_,?_⟩
      · simpa only [H.apply_symm_apply] using hz
      · rw [hkval,H.apply_symm_apply]
  have hkL : MapsTo k Disk (R ∩ (interior K)ᶜ) := fun z hz =>
    ⟨interior_subset (hjR (huD hz)),hjK _ (huD hz)⟩
  have hkproper (z : Disk) : k z ∈ frontier (R ∩ (interior K)ᶜ) ↔ (z : V2) ∈ Rim := by
    rw [hkval,hjproper _ (H z).property]
    exact (hkrim z).symm
  have hsmallOpen : IsOpen (V ∩ interior R ∩ Bᶜ) :=
    (hV.inter isOpen_interior).inter sB.isCompact.isClosed.isOpen_compl
  have hkSmall : k '' Disk ⊆ V ∩ interior R ∩ Bᶜ := by
    rw [hkimage]
    rintro x hx
    exact ⟨⟨hjV hx,by obtain ⟨z,hz,rfl⟩ := hx; exact hjR hz⟩,
      fun hxB => disjoint_left.mp hjB hx hxB⟩
  obtain ⟨P,hPsmall,_,hcutPL,hcut,_,_,_,_,_,hcollars⟩ :=
    exists_original_disk_cut_domain_with_collars hL hLPL hkPL hkemb hkL hkproper hsmallOpen hkSmall
  have hmark (z : V2 × ℝ) (hz : z ∈ Disk ×ˢ I) : P.map z ∈ S ↔ z.1 ∈ Rim := by
    rw [←P.proper z hz,hLfront,hfront]
    exact ⟨fun h => Or.inl (Or.inl h),fun h => h.elim
      (fun h => h.elim id (fun hb => False.elim ((hPsmall hz).2 hb)))
      (fun hr => False.elim (hr.2 (hPsmall hz).1.2))⟩
  have hstrip : P.closedStrip ∩ K = P.map '' (Rim ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    apply Subset.antisymm
    · rintro x ⟨⟨z,hz,rfl⟩,hzK⟩
      have hzfull : z ∈ Disk ×ˢ I := ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
      have hzfront : P.map z ∈ frontier K := hmeet.subset ⟨P.inside hzfull,hzK⟩
      have hzr := (P.proper z hzfull).mp (hLfront.symm.subset (Or.inl hzfront))
      exact ⟨z,⟨hzr,hz.2⟩,rfl⟩
    · rintro _ ⟨z,hz,rfl⟩
      have hzfull : z ∈ Disk ×ˢ I := ⟨sphere_subset_closedBall hz.1,
        by constructor <;> linarith [hz.2.1,hz.2.2]⟩
      exact ⟨⟨z,⟨sphere_subset_closedBall hz.1,hz.2⟩,rfl⟩,
        hKPL.closed.frontier_subset (hfront.symm.subset (Or.inl ((hmark z hzfull).mpr hz.1)))⟩
  refine ⟨K,B,H,k,hK,hKPL,hKU,⟨sB⟩,hSB,hfront,hcontact,⟨u,hu,hHu⟩,
    hkval,hkrim,hkimage,hkrimimage,hL,hLPL,P,hPsmall,hmark,hcut,hcutPL,hstrip,?_⟩
  intro η hη hη1
  refine ⟨(hcollars η hη hη1).1,?_⟩
  have hSfront : S ⊆ frontier (R ∩ (interior K)ᶜ) := fun x hx =>
    hLfront.symm.subset (Or.inl (hfront.symm.subset (Or.inl hx)))
  exact ((hcollars η hη hη1).2).preimage (continuous_inclusion hSfront)

end PoincareConjecture.M76
