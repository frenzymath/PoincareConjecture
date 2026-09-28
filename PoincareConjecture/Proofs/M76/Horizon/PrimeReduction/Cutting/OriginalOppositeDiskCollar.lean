import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.ClosedSphereCollarInterval
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.CenteredOppositeCollar
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)
local notation "Disk" => closedBall (0 : P2) 1
local notation "Rim" => sphere (0 : P2) 1

theorem ChartwisePLSphere.exists_original_opposite_disk_collar
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S U : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hU : IsOpen U) (hSU : S ⊆ U)
    (j : P2 → X) (hj : ContinuousOn j Disk)
    (hproper : ∀ z ∈ Disk, j z ∈ S ↔ z ∈ Rim) :
    ∃ (t : Finset R) (N : SimplicialComplex ℝ (t → ℝ × V3))
      (C : (t → ℝ × V3) × ℝ → X) (K B : Set X),
      N.faces.Finite ∧ PolyhedralPLInCharts e C (N.space ×ˢ I) ∧
      InjOn C (N.space ×ˢ I) ∧
      K = C '' (N.space ×ˢ J) ∧
      S = C '' (N.space ×ˢ ({1 / 2} : Set ℝ)) ∧
      B = C '' (N.space ×ˢ ({-(1 / 2)} : Set ℝ)) ∧
      IsCompact K ∧ PLDomain e K ∧ K ⊆ U ∩ interior R ∧
      Nonempty (ChartwisePLSphere e B) ∧ Disjoint B S ∧
      frontier K = B ∪ S ∧ K ∩ (j '' Disk) = j '' Rim ∧
      ∃ (c : (t → ℝ × V3) × ℝ → X) (ε : ℝ) (positive : Bool),
        PolyhedralPLInCharts e c (N.space ×ˢ I) ∧ InjOn c (N.space ×ˢ I) ∧
        0 < ε ∧ ε ≤ 1 / 4 ∧ IsConnected N.space ∧
        S = c '' (N.space ×ˢ ({0} : Set ℝ)) ∧
        MapsTo c (N.space ×ˢ Icc (-ε) ε) (U ∩ interior R) ∧
        IsOpen (c '' (N.space ×ˢ Ioo (-ε) ε)) ∧
        K = c '' (N.space ×ˢ (if positive then Icc (-ε) 0 else Icc 0 ε)) ∧
        interior K = c '' (N.space ×ˢ (if positive then Ioo (-ε) 0 else Ioo 0 ε)) ∧
        ∃ F : X → (t → ℝ × V3),
          (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
          InjOn F S ∧ N.space = F '' S := by
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
  have hO : IsOpen (c '' (N.space ×ˢ Ioo a b)) :=
    isOpen_bicollar_subinterval hci (by linarith : ε ≤ 1)
      (by
        intro u hu
        cases positive <;> dsimp [a,b] at hu <;> constructor <;> linarith [hu.1,hu.2])
      (hopen ε hε le_rfl)
  obtain ⟨hK,hKPL,hKi,hB,hdis,hfront⟩ := s.closed_bicollar_interval_domain
    he.compatible he.cover F hF (hFi.mono (hSR.trans interior_subset)) hNF
    (N.isCompact_space_of_finite hN) c hc hci ha hab hb hO
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
  have hB' : Nonempty (ChartwisePLSphere e B) := by
    cases positive
    · exact hB true
    · exact hB false
  have hBS : Disjoint B S := by
    cases positive
    · simpa only [a,b,B,Bool.false_eq_true,reduceIte,hzero] using hdis.symm
    · simpa only [a,b,B,Bool.false_eq_true,reduceIte,hzero] using hdis
  have hfront' : frontier K = B ∪ S := by
    cases positive <;>
      simpa only [K,a,b,B,Bool.false_eq_true,reduceIte,hzero,union_comm] using hfront
  have hci' : InjOn c (N.space ×ˢ I) := by
    intro z hz w hw hzw
    exact congrArg Subtype.val (hci.injective (a₁ := ⟨z,hz⟩) (a₂ := ⟨w,hw⟩) hzw)
  obtain ⟨C,hC,hCi,hCK,hCS,hCB⟩ := exists_centered_opposite_collar N hN c hc hci' hε hεsmall positive
  refine ⟨t,N,C,K,B,hN,hC,hCi,?_,(hCS.trans hzero).symm,hCB.symm,hK,hKPL,
    ?_,hB',hBS,hfront',?_,?_⟩
  · cases positive <;> simpa only [K,a,b,Bool.false_eq_true,reduceIte] using hCK.symm
  · rintro x ⟨z,hz,rfl⟩
    exact hsmall ⟨hz.1,habε hz.2⟩
  · cases positive <;> simpa only [K,a,b,Bool.false_eq_true,reduceIte] using hcontact
  · have hNc : IsConnected N.space := isConnected_iff_connectedSpace.mpr
      (HB.connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp s.isConnected))
    refine ⟨c,ε,positive,hc,hci',hε,hεsmall,hNc,hzero.symm,hsmall,hopen ε hε le_rfl,?_,?_,
      F,hF,hFi.mono (hSR.trans interior_subset),hNF⟩
    · cases positive <;> rfl
    · cases positive <;> simpa only [K,a,b,Bool.false_eq_true,reduceIte] using hKi

theorem ChartwisePLSphere.exists_original_opposite_finite_disk_collar
    {X ι E : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R S U : Set X} {d q : Set E}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hU : IsOpen U) (hSU : S ⊆ U)
    (hd : IsFinitePLBallPair P2 d q) (j : E → X) (hj : ContinuousOn j d)
    (hproper : ∀ z ∈ d, j z ∈ S ↔ z ∈ q) :
    ∃ (t : Finset R) (N : SimplicialComplex ℝ (t → ℝ × V3))
      (C : (t → ℝ × V3) × ℝ → X) (K B : Set X),
      N.faces.Finite ∧ PolyhedralPLInCharts e C (N.space ×ˢ I) ∧ InjOn C (N.space ×ˢ I) ∧
      K = C '' (N.space ×ˢ J) ∧ S = C '' (N.space ×ˢ ({1 / 2} : Set ℝ)) ∧
      B = C '' (N.space ×ˢ ({-(1 / 2)} : Set ℝ)) ∧
      IsCompact K ∧ PLDomain e K ∧ K ⊆ U ∩ interior R ∧
      Nonempty (ChartwisePLSphere e B) ∧ Disjoint B S ∧
      frontier K = B ∪ S ∧ K ∩ (j '' d) = j '' q ∧
      ∃ (c : (t → ℝ × V3) × ℝ → X) (ε : ℝ) (positive : Bool),
        PolyhedralPLInCharts e c (N.space ×ˢ I) ∧ InjOn c (N.space ×ˢ I) ∧
        0 < ε ∧ ε ≤ 1 / 4 ∧ IsConnected N.space ∧
        S = c '' (N.space ×ˢ ({0} : Set ℝ)) ∧
        MapsTo c (N.space ×ˢ Icc (-ε) ε) (U ∩ interior R) ∧
        IsOpen (c '' (N.space ×ˢ Ioo (-ε) ε)) ∧
        K = c '' (N.space ×ˢ (if positive then Icc (-ε) 0 else Icc 0 ε)) ∧
        interior K = c '' (N.space ×ˢ (if positive then Ioo (-ε) 0 else Ioo 0 ε)) ∧
        ∃ F : X → (t → ℝ × V3),
          (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
          InjOn F S ∧ N.space = F '' S := by
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
    simpa only [H.apply_symm_apply] using hHr (H.symm ⟨z,hz⟩)
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
      refine ⟨H ⟨z,hd.1 hz⟩,(hHr ⟨z,hd.1 hz⟩).mp hz,?_⟩
      rw [←hHf,H.symm_apply_apply]
  obtain ⟨t,N,C,K,B,hN,hC,hCi,hCK,hCS,hCB,hK,hKPL,hKU,hB,hBS,hfront,hcontact,hraw⟩ :=
    s.exists_original_opposite_disk_collar hR he hSR hU hSU (j ∘ f)
      (hj.comp hf.continuousOn hfd) hproper'
  refine ⟨t,N,C,K,B,hN,hC,hCi,hCK,hCS,hCB,hK,hKPL,hKU,hB,hBS,hfront,?_,hraw⟩
  simpa only [image_comp,hfdImage,hfqImage] using hcontact

end PoincareConjecture.M76
