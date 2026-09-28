import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.WitnessProtectedCocoreRegion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PositionedPortFaceProduct

set_option autoImplicit false
open Set Geometry Metric
namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

theorem ChartwisePLSphere.exists_cocore_positioned_product_of_disk_of_paired_charts
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (hcover : ∀x,∃i,x∈(e i).source)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀i,(e i).symm.trans Q∈piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space⊆Q.target)
    (H : V3 ≃ᴬ[ℝ] P3) (t : ℝ)
    {n : ℕ} (L : Polygon V3 (n+3)) (hLi : Function.Injective L) (hL : L.HasSimplicialEdges)
    {D U0 : Set V3} (hD : IsFinitePLBallPair P2 D (L.boundary ℝ))
    (hDsub : D⊆interior J.space∩{x | (H x).2=t})
    (hcontact : D∩Q '' (S∩Q.source)=L.boundary ℝ)
    (hU0 : IsOpen U0) (hDU0 : D⊆U0) (hU0J : U0⊆interior J.space)
    (hisolate : ∀x∈U0,x∈L.boundary ℝ ↔ Q.symm x∈S ∧ (H x).2=t)
    (hcross : ∀w∈L.boundary ℝ,∀O : Set V3,IsOpen O → w∈O →
      ∃B : OpenPartialHomeomorph V3 P3,
        w∈B.source ∧ B.source⊆O∩interior J.space ∧ B w=0 ∧
        LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀x∈B.source,Q.symm x∈S ↔ (B x).2=0) ∧ ∀x∈B.source,(H x).2=t ↔ (B x).1.1=0) :
    ∃rho : V2 × ℝ → X,
          PolyhedralPLInCharts e rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
          InjOn rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
          MapsTo rho (Disk ×ˢ Icc (-1 : ℝ) 1) (Q.symm '' U0) ∧
          (∀z∈Disk ×ˢ Icc (-1 : ℝ) 1,rho z∈S ↔ z.1∈Rim) ∧
          (∀c : Bool,Disjoint (rho '' (Disk ×ˢ {if c then (1/2 : ℝ) else -(1/2)}))
            (Q.symm '' (Q.target∩{x | (H x).2=t}))) ∧
          (rho '' (Rim ×ˢ Icc (-(1/2 : ℝ)) (1/2)))∩
            (Q.symm '' (Q.target∩{x | (H x).2=t}))=Q.symm '' L.boundary ℝ := by
  have hLS : L.boundary ℝ⊆(Q '' (S∩Q.source)∩interior J.space)∩{x | (H x).2=t} :=
    fun x hx => ⟨⟨(hcontact.symm.subset hx).2,(hDsub (hD.1 hx)).1⟩,(hDsub (hD.1 hx)).2⟩
  obtain ⟨k,sigma,caps,region,hRegionU0,hSigma,hMap,hPlane,hSphere,hfib,hImage,hcaps,
    hdis,hcapPlane,hRegion,hRegionJ,hFront,hPhysicalBall,hregionContact,hinterior,C,hC,hCcaps⟩ :=
    s.exists_witness_protected_cocore_region_of_disk_of_paired_charts hcover Q hQ J hJ hJQ H t
      L hLi hL hD hDsub hcontact hU0 hDU0 hU0J hisolate hcross
  let band := (fun z : P2 => sigma ((z.1,0),z.2)) ''
    (Icc (-1/4 : ℝ) (1/4) ×ˢ Icc (0 : ℝ) (k+3))
  have hRegionQ : region⊆Q.target := hRegionJ.trans (interior_subset.trans hJQ)
  have hcapsRegion (c : Bool) : caps c⊆region := by
    intro x hx
    apply hRegion.1
    right
    cases c
    · exact Or.inr hx
    · exact Or.inl hx
  have hcapsQ (c : Bool) : caps c⊆Q.target := (hcapsRegion c).trans hRegionQ
  let physicalC := C.trans (Q.symm.homeomorphOfImageSubsetSource hRegionQ rfl)
  obtain ⟨p,hp,hpval⟩ := hC
  have hpQ : MapsTo p (_root_.Dehn.annulusSquare 8 0 ×ˢ Icc (0 : ℝ) 1) Q.target := by
    intro z hz
    rw [←hpval ⟨z,hz⟩]
    exact hRegionQ (C ((Homeomorph.Set.prod _ _) ⟨z,hz⟩)).property
  have hPL : PolyhedralPLInCharts e (Q.symm∘p)
      (_root_.Dehn.annulusSquare 8 0 ×ˢ Icc (0 : ℝ) 1) := by
    have hpCopy := hp
    obtain ⟨K,hK,hKs,_⟩ := hpCopy
    rw [←hKs]
    exact polyhedralPLInCharts_of_compatible_inverse e Q (fun x _ => hcover x) hQ
      K hK (hKs.symm ▸ hp) (hKs.symm ▸ hpQ)
  have hval (z : (_root_.Dehn.annulusSquare 8 0 ×ˢ Icc (0 : ℝ) 1 : Set P3)) :
      (Q.symm∘p) z=(physicalC ((Homeomorph.Set.prod _ _) z) : X) :=
    congrArg Q.symm (hpval z).symm
  have hcval (c : Bool) (z) : (physicalC z : X)∈Q.symm '' caps c ↔ z.2=if c then 1 else 0 := by
    rw [←hCcaps c z]
    change Q.symm (C z)∈Q.symm '' caps c ↔ (C z : V3)∈caps c
    constructor
    · rintro ⟨x,hx,hxeq⟩
      exact Q.symm.injOn (hcapsQ c hx) (hRegionQ (C z).property) hxeq ▸ hx
    · exact fun hx => ⟨C z,hx,rfl⟩
  have hPhysicalCompact : IsCompact (Q.symm '' region) :=
    hRegion.isCompact.image_of_continuousOn (Q.continuousOn_symm.mono hRegionQ)
  have hPhysicalQ : Q.symm '' region⊆Q.source := by
    rintro _ ⟨x,hx,rfl⟩
    exact Q.map_target (hRegionQ hx)
  have hPhysicalFront : frontier (Q.symm '' region)=
      Q.symm '' band ∪ (Q.symm '' caps true ∪ Q.symm '' caps false) := by
    have hh := Q.symm.image_frontier_eq_target_inter_of_closure_subset
      (D := region) (by rwa [hRegion.isCompact.isClosed.closure_eq])
    change Q.symm '' frontier region=Q.source∩frontier (Q.symm '' region) at hh
    rw [inter_eq_right.mpr (hPhysicalCompact.isClosed.frontier_subset.trans hPhysicalQ)] at hh
    rw [←hh,hFront,image_union,image_union]
  let T := J.space∩{x | (H x).2=t}
  let F : Set X := Q.symm '' T
  let Ffull : Set X := Q.symm '' (Q.target∩{x | (H x).2=t})
  have hTc : IsCompact T := (J.isCompact_space_of_finite hJ).inter_right
    (isClosed_eq (continuous_snd.comp H.continuous) continuous_const)
  have hF : IsClosed F := (hTc.image_of_continuousOn
    (Q.continuousOn_symm.mono (inter_subset_left.trans hJQ))).isClosed
  have hFF : F⊆Ffull := image_mono (inter_subset_inter_left _ hJQ)
  have hlevel (x : V3) (hx : x∈J.space) : Q.symm x∈F ↔ Q.symm x∈Ffull := by
    constructor
    · exact fun h => hFF h
    · rintro ⟨y,hy,hyeq⟩
      have heq := Q.symm.injOn hy.1 (hJQ hx) hyeq
      exact ⟨x,⟨hx,heq ▸ hy.2⟩,rfl⟩
  have hcapsF (c : Bool) : Disjoint (Q.symm '' caps c) F := by
    apply disjoint_left.mpr
    rintro x ⟨y,hy,hyx⟩ ⟨z,hz,hzx⟩
    have heq := Q.symm.injOn (hcapsQ c hy) (hJQ hz.1) (hyx.trans hzx.symm)
    exact disjoint_left.mp (hcapPlane c) hy (heq.symm ▸ hz.2)
  have hbandF : (Q.symm '' band)∩F=Q.symm '' L.boundary ℝ := by
    apply Subset.antisymm
    · rintro x ⟨⟨_,⟨z,hz,rfl⟩,hzx⟩,⟨y,hy,hyx⟩⟩
      have hz' : ((z.1,0),z.2)∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3) := by
        simpa only [signedSheetStripMap_apply,Fin.reduceEq,if_false] using
          signedSheetStripMap_mem (1 : Fin 2)
            (show z∈Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) (k+3) from
              ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,hz.2⟩)
      have heq := Q.symm.injOn (hJQ (interior_subset (hMap hz'))) (hJQ hy.1)
        (hzx.trans hyx.symm)
      have hzero : z.1=0 := by
        have hh := (hPlane _ hz').mp (heq.symm ▸ hy.2)
        simpa using (signedTubeSheet_coordinate_iff _ hz'.1 0).mp hh
      refine ⟨sigma ((0,0),z.2),hImage.subset ⟨z.2,hz.2,rfl⟩,?_⟩
      simpa only [hzero] using hzx
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨u,hu,hux⟩ := hImage.symm.subset hx
      refine ⟨⟨x,?_,rfl⟩,x,⟨interior_subset (hLS hx).1.2,(hLS hx).2⟩,rfl⟩
      exact ⟨(0,u),⟨by norm_num,hu⟩,hux⟩
  obtain ⟨rho,hρ,hρi,hρregion,hρS,hρcaps,hρband,_⟩ :=
    exists_original_two_port_face_product (fun c => Q.symm '' caps c)
      (_root_.Dehn.isFinitePLBallPair_annulusSquare (by norm_num))
      physicalC (Q.symm∘p) hPL hval hcval hPhysicalFront hregionContact hF hcapsF hbandF
  have hρJ : MapsTo rho (Disk ×ˢ Icc (-1 : ℝ) 1) (Q.symm '' interior J.space) :=
    fun z hz => image_mono hRegionJ (hρregion hz)
  have hρlevel (z : V2 × ℝ) (hz : z∈Disk ×ˢ Icc (-1 : ℝ) 1) : rho z∈F ↔ rho z∈Ffull := by
    obtain ⟨x,hx,hxeq⟩ := hρJ hz
    rw [←hxeq]
    exact hlevel x (interior_subset hx)
  refine ⟨rho,hρ,hρi,(fun z hz => image_mono hRegionU0 (hρregion hz)),hρS,?_,?_⟩
  · intro c
    apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hx
    apply disjoint_left.mp (hρcaps c) ⟨z,hz,rfl⟩
    apply (hρlevel z ⟨hz.1,?_⟩).mpr hx
    have hz2 : z.2=if c then (1/2 : ℝ) else -(1/2) := hz.2
    cases c <;> simp only [Bool.false_eq_true,reduceIte] at hz2 <;>
      rw [hz2] <;> norm_num
  · rw [←hρband]
    ext x
    constructor
    · rintro ⟨⟨z,hz,rfl⟩,hx⟩
      exact ⟨⟨z,hz,rfl⟩,(hρlevel z ⟨sphere_subset_closedBall hz.1,
        ⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩⟩).mpr hx⟩
    · exact fun hx => ⟨hx.1,hFF hx.2⟩

theorem ChartwisePLSphere.exists_cocore_positioned_product_of_disk
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (hcover : ∀x,∃i,x∈(e i).source)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀i,(e i).symm.trans Q∈piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space⊆Q.target)
    (H : V3 ≃ᴬ[ℝ] P3) (t : ℝ)
    {n : ℕ} (L : Polygon V3 (n+3)) (hLi : Function.Injective L) (hL : L.HasSimplicialEdges)
    {D U0 : Set V3} (hD : IsFinitePLBallPair P2 D (L.boundary ℝ))
    (hDsub : D⊆interior J.space∩{x | (H x).2=t})
    (hcontact : D∩Q '' (S∩Q.source)=L.boundary ℝ)
    (hU0 : IsOpen U0) (hDU0 : D⊆U0) (hU0J : U0⊆interior J.space)
    (hisolate : ∀x∈U0,x∈L.boundary ℝ ↔ Q.symm x∈S ∧ (H x).2=t)
    (hcross : ∀w∈L.boundary ℝ,∀O : Set V3,IsOpen O → w∈O →
      ∃B : OpenPartialHomeomorph V3 P3,
        w∈B.source ∧ B.source⊆O∩interior J.space ∧ B w=0 ∧
        LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀x∈B.source,Q.symm x∈S ↔ (B x).2=0) ∧ ∀x∈B.source,(H x).2-t=(B x).1.1) :
    ∃rho : V2 × ℝ → X,
          PolyhedralPLInCharts e rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
          InjOn rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
          MapsTo rho (Disk ×ˢ Icc (-1 : ℝ) 1) (Q.symm '' U0) ∧
          (∀z∈Disk ×ˢ Icc (-1 : ℝ) 1,rho z∈S ↔ z.1∈Rim) ∧
          (∀c : Bool,Disjoint (rho '' (Disk ×ˢ {if c then (1/2 : ℝ) else -(1/2)}))
            (Q.symm '' (Q.target∩{x | (H x).2=t}))) ∧
          (rho '' (Rim ×ˢ Icc (-(1/2 : ℝ)) (1/2)))∩
            (Q.symm '' (Q.target∩{x | (H x).2=t}))=Q.symm '' L.boundary ℝ := by
  apply s.exists_cocore_positioned_product_of_disk_of_paired_charts hcover Q hQ J hJ hJQ H t L hLi hL hD hDsub hcontact hU0 hDU0 hU0J hisolate ?_
  intro w hw O hO hwO
  obtain ⟨B, hwB, hBO, hBw, hB, hBi, hBS, hheight⟩ := hcross w hw O hO hwO
  refine ⟨B, hwB, hBO, hBw, hB, hBi, hBS, ?_⟩
  intro x hx
  rw [← sub_eq_zero, hheight x hx]

theorem ChartwisePLSphere.exists_cocore_positioned_product
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (hcover : ∀x,∃i,x∈(e i).source)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀i,(e i).symm.trans Q∈piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space⊆Q.target)
    (hJcv : Convex ℝ J.space) (H : V3 ≃ᴬ[ℝ] P3) {a b : ℝ} (hab : a<b)
    (hband : ∀x∈Q '' (S∩Q.source)∩J.space,(H x).2∈Ioo a b → x∈interior J.space) :
    ∃t∈Ioo a b,
      HasDisjointPolygonPresentation ((Q '' (S∩Q.source)∩J.space)∩{x | (H x).2=t}) ∧
      (((Q '' (S∩Q.source)∩J.space)∩{x | (H x).2=t}=∅) ∨
        ∃(n : ℕ) (L : Polygon V3 (n+3)) (rho : V2 × ℝ → X),
          Function.Injective L ∧ L.HasSimplicialEdges ∧
          L.boundary ℝ⊆(Q '' (S∩Q.source)∩interior J.space)∩{x | (H x).2=t} ∧
          IsCompact (((Q '' (S∩Q.source)∩J.space)∩{x | (H x).2=t})\L.boundary ℝ) ∧
          PolyhedralPLInCharts e rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
          InjOn rho (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
          MapsTo rho (Disk ×ˢ Icc (-1 : ℝ) 1) (Q.symm '' interior J.space) ∧
          (∀z∈Disk ×ˢ Icc (-1 : ℝ) 1,rho z∈S ↔ z.1∈Rim) ∧
          (∀c : Bool,Disjoint (rho '' (Disk ×ˢ {if c then (1/2 : ℝ) else -(1/2)}))
            (Q.symm '' (Q.target∩{x | (H x).2=t}))) ∧
          (rho '' (Rim ×ˢ Icc (-(1/2 : ℝ)) (1/2)))∩
            (Q.symm '' (Q.target∩{x | (H x).2=t}))=Q.symm '' L.boundary ℝ) := by
  obtain ⟨t,ht,hpres,hempty | ⟨n,L,D,hLi,hL,hD,hDsub,hcontact,hrem,U0,hU0,hDU0,hU0J,hisolate,hcross⟩⟩ :=
    s.exists_cocore_innermost_disk_with_crossings_and_presentation Q hQ J hJ hJQ hJcv H hab hband
  · exact ⟨t,ht,hpres,Or.inl hempty⟩
  · obtain ⟨rho,hρ,hρi,hρU,hρS,hcap,hstrip⟩ :=
      s.exists_cocore_positioned_product_of_disk hcover Q hQ J hJ hJQ H t
        L hLi hL hD hDsub hcontact hU0 hDU0 hU0J hisolate hcross
    have hLS : L.boundary ℝ⊆(Q '' (S∩Q.source)∩interior J.space)∩{x | (H x).2=t} :=
      fun x hx => ⟨⟨(hcontact.symm.subset hx).2,(hDsub (hD.1 hx)).1⟩,(hDsub (hD.1 hx)).2⟩
    exact ⟨t,ht,hpres,Or.inr ⟨n,L,rho,hLi,hL,hLS,hrem,hρ,hρi,
      (fun z hz => image_mono hU0J (hρU hz)),hρS,hcap,hstrip⟩⟩

end PoincareConjecture.M76
