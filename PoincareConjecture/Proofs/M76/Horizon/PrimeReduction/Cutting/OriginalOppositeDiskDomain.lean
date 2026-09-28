import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.OriginalProperDiskCollarSide
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.ClosedCollarIntervalGeometry
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphereCutPLDomain








set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "Disk" => closedBall (0 : P2) 1
local notation "Rim" => sphere (0 : P2) 1

theorem ChartwisePLSphere.exists_original_opposite_disk_domain
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S U : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hU : IsOpen U) (hSU : S ⊆ U)
    (j : P2 → X) (hj : ContinuousOn j Disk)
    (hproper : ∀ z ∈ Disk, j z ∈ S ↔ z ∈ Rim) :
    ∃ K B : Set X, IsCompact K ∧ PLDomain e K ∧ K ⊆ U ∩ interior R ∧
      Nonempty (ChartwisePLSphere e B) ∧ Disjoint S B ∧
      frontier K = S ∪ B ∧ K ∩ (j '' Disk) = j '' Rim := by
  classical
  obtain ⟨t,F,N,HB,c,ε,positive,_,hF,hFi,hNF,hN,hc,hci,hc0,_,hε,hεsmall,
      hsmall,hopen,hcontact⟩ :=
    s.exists_original_opposite_disk_half_collar hR he hSR hU hSU j hj hproper
  let E := t → ℝ × V3
  let a : ℝ := if positive then -ε else 0
  let b : ℝ := if positive then 0 else ε
  have ha : -1 < a := by cases positive <;> dsimp [a] <;> linarith
  have hab : a < b := by cases positive <;> dsimp [a,b] <;> linarith
  have hb : b < 1 := by cases positive <;> dsimp [b] <;> linarith
  have habε : Icc a b ⊆ Icc (-ε) ε := by
    cases positive <;> dsimp [a,b] <;> exact Icc_subset_Icc (by linarith) (by linarith)
  have hinj : InjOn c (N.space ×ˢ I) := by
    intro z hz w hw hzw
    exact congrArg Subtype.val (hci.injective (a₁ := ⟨z,hz⟩) (a₂ := ⟨w,hw⟩) hzw)
  let O := c '' (N.space ×ˢ Ioo a b)
  have hO : IsOpen O := by
    let V : Set (N.space ×ˢ I : Set (E × ℝ)) := {z | z.1.2 ∈ Ioo a b}
    have hV : IsOpen V := isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val)
    have hVe : (fun z : (N.space ×ˢ I : Set (E × ℝ)) => c z) '' V = O := by
      apply Subset.antisymm
      · rintro _ ⟨z,hz,rfl⟩
        exact ⟨z,⟨z.property.1,hz⟩,rfl⟩
      · rintro _ ⟨z,hz,rfl⟩
        exact ⟨⟨z,hz.1,ha.le.trans hz.2.1.le,hz.2.2.le.trans hb.le⟩,hz.2,rfl⟩
    rw [←hVe]
    apply hci.isInducing.isOpen_image_of_subset_open hV (hopen ε hε le_rfl)
    · rintro _ ⟨z,hz,rfl⟩
      refine ⟨z,⟨z.property.1,?_⟩,rfl⟩
      change a < z.1.2 ∧ z.1.2 < b at hz
      cases positive <;> dsimp [a,b] at hz <;> constructor <;> linarith [hz.1,hz.2]
    · rintro _ ⟨z,hz,rfl⟩
      exact ⟨⟨z,hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩,rfl⟩
  obtain ⟨hK,_,hreg,hfront⟩ := closed_collar_interval_geometry
    (N.isCompact_space_of_finite hN) c hc.continuousOn hinj ha hab hb hO
  let K := c '' (N.space ×ˢ Icc a b)
  let B := c '' (N.space ×ˢ {if positive then -ε else ε})
  have hzero : c '' (N.space ×ˢ ({0} : Set ℝ)) = S := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      have ht0 : z.2 = 0 := hz.2
      have hv : c (z.1,0) ∈ S := (hc0 ⟨z.1,hz.1⟩).symm ▸ (HB ⟨z.1,hz.1⟩).property
      simpa only [←ht0] using hv
    · intro x hx
      refine ⟨((HB.symm ⟨x,hx⟩ : E),0),⟨(HB.symm ⟨x,hx⟩).property,rfl⟩,?_⟩
      exact (hc0 _).trans (congrArg Subtype.val (HB.apply_symm_apply ⟨x,hx⟩))
  have hfront' : frontier K = S ∪ B := by
    dsimp [K] at hfront ⊢
    cases positive <;> simpa only [a,b,B,Bool.false_eq_true,reduceIte,hzero,union_comm] using hfront
  have hSB : Disjoint S B := by
    rw [←hzero]
    apply disjoint_left.mpr
    rintro x ⟨z,hz,hzx⟩ ⟨w,hw,hwx⟩
    have ht0 : z.2 = 0 := hz.2
    have htB : w.2 = if positive then -ε else ε := hw.2
    have heq := congrArg Prod.snd (hinj
      ⟨hz.1,by rw [ht0]; norm_num⟩
      ⟨hw.1,by rw [htB]; cases positive <;> norm_num <;> constructor <;> linarith⟩
      (hzx.trans hwx.symm))
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] at htB <;> linarith
  obtain ⟨sB,_⟩ := s.exists_bicollar_level_sphere F hF
    (hFi.mono (hSR.trans interior_subset)) hNF c hc hci
    (show (if positive then -ε else ε) ∈ I by
      cases positive <;> norm_num <;> constructor <;> linarith)
  have hKPL : PLDomain e K := by
    refine ⟨he.cover,he.compatible,hK.isClosed,?_⟩
    intro x hx
    rcases hfront'.subset hx with hxS | hxB
    · exact s.exists_regular_boundary_halfspace_chart hK.isClosed hreg sB.isCompact.isClosed
        he.compatible he.cover (hfront'.trans (union_comm _ _)) hxS
        (fun hxB => disjoint_left.mp hSB hxS hxB)
    · exact sB.exists_regular_boundary_halfspace_chart hK.isClosed hreg s.isCompact.isClosed
        he.compatible he.cover hfront' hxB (fun hxS => disjoint_left.mp hSB hxS hxB)
  refine ⟨K,B,hK,hKPL,?_,⟨sB⟩,hSB,hfront',?_⟩
  · rintro x ⟨z,hz,rfl⟩
    exact hsmall ⟨hz.1,habε hz.2⟩
  · cases positive <;> simpa only [K,a,b,Bool.false_eq_true,reduceIte] using hcontact

theorem ChartwisePLSphere.exists_original_opposite_finite_disk_domain
    {X ι E : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R S U : Set X} {d q : Set E}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hU : IsOpen U) (hSU : S ⊆ U)
    (hd : IsFinitePLBallPair P2 d q) (j : E → X) (hj : ContinuousOn j d)
    (hproper : ∀ z ∈ d, j z ∈ S ↔ z ∈ q) :
    ∃ K B : Set X, IsCompact K ∧ PLDomain e K ∧ K ⊆ U ∩ interior R ∧
      Nonempty (ChartwisePLSphere e B) ∧ Disjoint S B ∧
      frontier K = S ∪ B ∧ K ∩ (j '' d) = j '' q := by
  classical
  have hDisk : IsFinitePLBallPair P2 Disk Rim := by
    have h := CoordinateHalfBoxes.base_ballPair (by norm_num : (0 : ℝ) < 1)
    have heq : CoordinateHalfBoxes.base 1 = Disk := by
      ext x
      simp only [CoordinateHalfBoxes.base,mem_prod,mem_Icc,mem_closedBall,
        dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le]
    have hb := h.frontier_eq_of_finrank_eq rfl
    rw [heq,frontier_closedBall _ one_ne_zero] at hb
    rwa [heq,←hb] at h
  obtain ⟨H,hH,hHr⟩ := hd.exists_homeomorph hDisk
  obtain ⟨f,hf,hHf⟩ := hH.symm
  have hfd : MapsTo f Disk d := fun z hz =>
    (hHf ⟨z,hz⟩) ▸ (H.symm ⟨z,hz⟩).property
  have hproper' (z : P2) (hz : z ∈ Disk) : j (f z) ∈ S ↔ z ∈ Rim := by
    rw [hproper _ (hfd hz),←hHf ⟨z,hz⟩]
    have hh := hHr (H.symm ⟨z,hz⟩)
    simpa only [H.apply_symm_apply,frontier_closedBall _ one_ne_zero] using hh
  have hfdImage : f '' Disk = d := by
    apply Subset.antisymm (image_subset_iff.mpr hfd)
    intro z hz
    refine ⟨H ⟨z,hz⟩,(H ⟨z,hz⟩).property,?_⟩
    rw [←hHf,H.symm_apply_apply]
  have hfqImage : f '' Rim = q := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      have hh := hHr (H.symm ⟨z,sphere_subset_closedBall hz⟩)
      rw [H.apply_symm_apply] at hh
      simpa only [hHf] using hh.mpr hz
    · intro z hz
      refine ⟨H ⟨z,hd.1 hz⟩,?_,?_⟩
      · have hh := (hHr ⟨z,hd.1 hz⟩).mp hz
        simpa only [frontier_closedBall _ one_ne_zero] using hh
      · rw [←hHf,H.symm_apply_apply]
  obtain ⟨K,B,hK,hKPL,hKU,hB,hSB,hfront,hcontact⟩ :=
    s.exists_original_opposite_disk_domain hR he hSR hU hSU (j ∘ f)
      (hj.comp hf.continuousOn hfd) hproper'
  refine ⟨K,B,hK,hKPL,hKU,hB,hSB,hfront,?_⟩
  simpa only [image_comp,hfdImage,hfqImage] using hcontact

end PoincareConjecture.M76
