import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.FixedCocoreCircleTubes
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CocoreInnermostCrossings
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.CircleSphereScene
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.MemberCircleCut
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineLevelComplex
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Disks.SeparatedTubeCaps
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.CircleNormalSides
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PlanarDiskBallNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.CircleSurgeryRegion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleCollarRegionIncidence
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.ChartwiseBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.TwoPortRegionProduct
import PoincareConjecture.Proofs.Horizon.Topology.Maps.OpenPartialHomeomorph.Compact










set_option autoImplicit false
open Set Geometry Metric
namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem ChartwisePLSphere.exists_witness_protected_cocore_region_of_disk_of_paired_charts
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
    ∃(k : ℕ) (sigma : P3 → V3) (caps : Bool → Set V3) (region : Set V3),
      region⊆U0 ∧
        let band := (fun z : P2 => sigma ((z.1,0),z.2)) ''
          (Icc (-1/4 : ℝ) (1/4) ×ˢ Icc (0 : ℝ) (k+3))
        FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3)) ∧
        MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3)) (interior J.space) ∧
        (∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          (H (sigma x)).2=t ↔ x.1∈signedTubeSheet 0) ∧
        (∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          Q.symm (sigma x)∈S ↔ x.1∈signedTubeSheet 1) ∧
        (∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          ∀y∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),sigma x=sigma y ↔ x.1=y.1 ∧
            (x.2=y.2 ∨ (x.2=0 ∧ y.2=k+3) ∨ (x.2=k+3 ∧ y.2=0))) ∧
        (fun u : ℝ => sigma ((0,0),u)) '' Icc (0 : ℝ) (k+3)=L.boundary ℝ ∧
        (∀c,IsFinitePLBallPair P2 (caps c)
          ((fun u : ℝ => sigma ((if c then 1/4 else -1/4,0),u)) '' Icc (0 : ℝ) (k+3)) ∧
          caps c∩Q.symm ⁻¹' S=
            (fun u : ℝ => sigma ((if c then 1/4 else -1/4,0),u)) '' Icc (0 : ℝ) (k+3)) ∧
        Disjoint (caps true) (caps false) ∧
        (∀c,Disjoint (caps c) {x | (H x).2=t}) ∧
        IsFinitePLBallPair P3 region (band∪(caps true∪caps false)) ∧
        region⊆interior J.space ∧ frontier region=band∪(caps true∪caps false) ∧
        Nonempty (ChartwisePLBall e (Q.symm '' region) (Q.symm '' (band∪(caps true∪caps false)))) ∧
        (Q.symm '' region)∩S=Q.symm '' band ∧
        Disjoint (interior (Q.symm '' region)) S ∧
        ∃C : ((_root_.Dehn.annulusSquare 8 0 : Set P2) × unitInterval) ≃ₜ region,
          ((Homeomorph.Set.prod _ (Icc (0 : ℝ) 1)).trans C).IsFinitePL ∧
          ∀c z,(C z : V3)∈caps c ↔ z.2=if c then 1 else 0 := by
  have hLS : L.boundary ℝ⊆(Q '' (S∩Q.source)∩interior J.space)∩{x | (H x).2=t} :=
    fun x hx => ⟨⟨(hcontact.symm.subset hx).2,(hDsub (hD.1 hx)).1⟩,(hDsub (hD.1 hx)).2⟩
  obtain ⟨d,r,hd,hdwhole,hdinter,hrimage,tubes⟩ :=
    s.exists_fixed_cocore_circle_tubes_of_paired_charts Q hQ J hJ hJQ H t L hLi hL hLS hU0J hisolate hcross
  have hU0Q : U0⊆Q.target := hU0J.trans (interior_subset.trans hJQ)
  have hDQ : D⊆Q.target := hDU0.trans hU0Q
  have hphysicalContact : (Q.symm '' D)∩S=s.map '' r := by
    rw [hrimage]
    apply Subset.antisymm
    · rintro _ ⟨⟨x,hx,rfl⟩,hxS⟩
      exact ⟨x,hcontact.subset ⟨hx,Q.symm x,⟨hxS,Q.map_target (hDQ hx)⟩,
        Q.right_inv (hDQ hx)⟩,rfl⟩
    · rintro _ ⟨x,hx,rfl⟩
      refine ⟨⟨x,hD.1 hx,rfl⟩,?_⟩
      obtain ⟨y,hy,hyeq⟩ := (hcontact.symm.subset hx).2
      rw [←hyeq,Q.left_inv hy.2]
      exact hy.1
  obtain ⟨p,Up,hUp,hDUp,hUpO,_,hp⟩ :=
    s.exists_circle_cut_witness_neighborhood d hd hdwhole hdinter subset_rfl
      hphysicalContact (Q.symm.isOpen_image_of_subset_source hU0 hU0Q) (image_mono hDU0)
  let V := U0∩(Q.target∩Q.symm ⁻¹' Up)
  have hV : IsOpen V := hU0.inter (Q.symm.isOpen_inter_preimage hUp)
  have hDV : D⊆V := fun x hx => ⟨hDU0 hx,hDQ hx,hDUp ⟨x,hx,rfl⟩⟩
  have hVU : V⊆U0 := inter_subset_left
  obtain ⟨k0,sigma0,hSigma0,hMap0,hInt0,hPlane0,hSphere0,hAxis0,hImage0,hFib0⟩ :=
    tubes V hV (hD.1.trans hDV) hVU
  let F : P2 →ᴬ[ℝ] V3 := H.symm.toContinuousAffineMap.comp
    ((ContinuousAffineMap.id ℝ P2).prod (ContinuousAffineMap.const ℝ P2 t))
  let G : V3 →ᴬ[ℝ] P2 :=
    (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap
  have hF (z : P2) : F z=H.symm (z,t) := rfl
  have hG (x : V3) : G x=(H x).1 := rfl
  have hleft : Function.LeftInverse G F := by intro z; rw [hG,hF,H.apply_symm_apply]
  have hright : EqOn (F∘G) id {x | (H x).2=t} := by
    intro x hx
    change F (G x)=x
    rw [hF,hG,←hx]
    exact H.symm_apply_apply x
  obtain ⟨B,bd,hB,hDB,hBV⟩ := exists_ball_neighborhood_of_identity_circle_tube
    L hL hLi hD (fun x hx => (hDsub hx).2) F G hleft hright
    (by positivity : (0 : ℝ)<k0+3) sigma0 hSigma0 hPlane0 hAxis0 hImage0 hFib0 hV hDV
    (by rintro _ ⟨z,hz,rfl⟩; exact hMap0 hz)
  let W := interior B∩V
  have hW : IsOpen W := isOpen_interior.inter hV
  have hDW : D⊆W := fun x hx => ⟨hDB hx,hDV hx⟩
  have hWU : W⊆U0 := inter_subset_right.trans hVU
  have hWJ : W⊆interior J.space := hWU.trans hU0J
  obtain ⟨k,sigma,hSigma,hMap,hInt,hPlane,hSphere,hAxis,hImage,hFib⟩ :=
    tubes W hW (hD.1.trans hDW) hWU
  obtain ⟨M,hM,hMs,_,hMlocal⟩ := s.exists_finite_chart_carrier Q hQ J hJ hJQ
  let A : V3 →ᴬ[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap -
      ContinuousAffineMap.const ℝ V3 t
  have hAx (x : V3) : A x=(H x).2-t := rfl
  have hA : A.linear≠0 := by
    intro hzero
    obtain ⟨c,hc⟩ := A.toAffineMap.linear_eq_zero_iff_exists_const.mp hzero
    have h0 := DFunLike.congr_fun hc (H.symm ((0,0),0))
    have h1 := DFunLike.congr_fun hc (H.symm ((0,0),1))
    change A (H.symm ((0,0),0))=c at h0
    change A (H.symm ((0,0),1))=c at h1
    rw [hAx,H.apply_symm_apply] at h0 h1
    norm_num at h0 h1
    linarith
  have hzero : ∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),A (sigma x)=0 ↔ x.1.1=0 := by
    intro x hx
    rw [hAx,sub_eq_zero,hPlane x hx,signedTubeSheet_coordinate_iff _ hx.1]
    simp
  have hsides := circle_tube_affine_height_sides (by positivity : (0 : ℝ)≤k+3)
    sigma hSigma.continuousOn A hA hzero
    (hInt (hImage.subset ⟨0,⟨le_rfl,by positivity⟩,rfl⟩))
  have hDM : D∩M.space=L.boundary ℝ := by
    apply Subset.antisymm
    · exact fun x hx => hcontact.subset ⟨hx.1,(hMs.subset hx.2).1⟩
    · intro x hx
      exact ⟨hD.1 hx,hMs.symm.subset ⟨(hcontact.symm.subset hx).2,interior_subset (hDsub (hD.1 hx)).1⟩⟩
  have hSphereM : ∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
      sigma x∈M.space ↔ x.1∈signedTubeSheet 1 :=
    fun x hx => (hMlocal _ (interior_subset (hWJ (hMap hx)))).symm.trans (hSphere x hx)
  obtain ⟨caps,hcaps,hdis⟩ := exists_separated_caps_of_circle_tube L hL hLi hD
    (fun x hx => (hDsub hx).2) F G hleft hright M hM hDM hW hDW
    (by positivity : (0 : ℝ)<k+3) sigma hSigma hMap hPlane hSphereM hAxis hFib
    A.toAffineMap hA (fun x hx => sub_eq_zero.mpr hx) hzero hsides
  have hcapS (c : Bool) : caps c∩Q.symm ⁻¹' S=
      (fun u : ℝ => sigma ((if c then 1/4 else -1/4,0),u)) '' Icc (0 : ℝ) (k+3) := by
    rw [←(hcaps c).2.2.1]
    ext x
    constructor
    · exact fun hx => ⟨hx.1,(hMlocal x (interior_subset (hWJ ((hcaps c).2.1 hx.1)))).mp hx.2⟩
    · exact fun hx => ⟨hx.1,(hMlocal x (interior_subset (hWJ ((hcaps c).2.1 hx.1)))).mpr hx.2⟩
  have hfib : ∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
      ∀y∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),sigma x=sigma y ↔ x.1=y.1 ∧
      (x.2=y.2 ∨ (x.2=0 ∧ y.2=k+3) ∨ (x.2=k+3 ∧ y.2=0)) := by
    intro x hx y hy
    simpa only [and_comm] using hFib x hx y hy
  obtain ⟨_,_,region,hRegion,hRegionB,hFront,hFrontS⟩ := exists_circle_surgery_region
    (by simp : Module.finrank ℝ V3=3) (by positivity : (0 : ℝ)<k+3) sigma hSigma hfib
    (fun x hx => (hSphere x hx).trans (signedTubeSheet_coordinate_iff x.1 hx.1 1))
    caps (fun c => (hcaps c).1) hcapS hdis hB
    (by rintro _ ⟨z,hz,rfl⟩; exact (hMap hz).1) (fun c x hx => ((hcaps c).2.1 hx).1)
  let band := (fun z : P2 => sigma ((z.1,0),z.2)) ''
    (Icc (-1/4 : ℝ) (1/4) ×ˢ Icc (0 : ℝ) (k+3))
  have hRegionV : region⊆V := hRegionB.trans (interior_subset.trans hBV)
  have hRegionQ : region⊆Q.target := fun x hx => (hRegionV hx).2.1
  have hPhysicalCompact : IsCompact (Q.symm '' region) :=
    hRegion.isCompact.image_of_continuousOn (Q.continuousOn_symm.mono hRegionQ)
  have hPhysicalQ : Q.symm '' region⊆Q.source := by
    rintro _ ⟨x,hx,rfl⟩
    exact Q.map_target (hRegionQ hx)
  have hPhysicalFrontier : frontier (Q.symm '' region)=Q.symm '' frontier region := by
    have hh := Q.symm.image_frontier_eq_target_inter_of_closure_subset
      (D := region) (by rwa [hRegion.isCompact.isClosed.closure_eq])
    change Q.symm '' frontier region=Q.source∩frontier (Q.symm '' region) at hh
    rw [inter_eq_right.mpr (hPhysicalCompact.isClosed.frontier_subset.trans hPhysicalQ)] at hh
    exact hh.symm
  have hPhysicalFront : frontier (Q.symm '' region)∩S=Q.symm '' band := by
    rw [hPhysicalFrontier,←image_inter_preimage,hFrontS]
  have hRegionUp : Q.symm '' region⊆Up := by
    rintro _ ⟨x,hx,rfl⟩
    exact (hRegionV hx).2.2
  have hrAxis : s.map '' r=(fun u : ℝ => Q.symm (sigma ((0,0),u))) '' Icc (0 : ℝ) (k+3) := by
    rw [hrimage,←hImage,image_image]
  obtain ⟨phi,ret,hphi,hphiS,hphival,hphiaxis,hret,hretdis,hwhole,hinc,hint⟩ :=
    s.exists_circle_collar_region_incidence Q hQ d hd hdwhole hdinter p
      (fun c => (hp c).1) (fun c => (hp c).2.2.2) (by positivity : (0 : ℝ)<k+3)
      sigma hSigma (fun x hx => (hMap hx).2.2)
      (fun x hx hz => (hSphere x hx).mpr ((signedTubeSheet_coordinate_iff x.1 hx.1 1).mpr hz))
      hfib hrAxis hPhysicalCompact.isClosed hRegionUp
      (by simpa only [band,image_image] using hPhysicalFront)
  obtain ⟨C,hC,hCcaps⟩ := exists_circle_two_port_product_handle
    (by positivity : (0 : ℝ)<k+3) sigma hSigma hfib
    (fun x hx => (hSphere x hx).trans (signedTubeSheet_coordinate_iff x.1 hx.1 1))
    caps (fun c => (hcaps c).1) hcapS hdis hRegion
  exact ⟨k,sigma,caps,region,hRegionV.trans hVU,hSigma,
    (fun x hx => hWJ (hMap hx)),hPlane,hSphere,hfib,hImage,
    (fun c => ⟨(hcaps c).1,hcapS c⟩),hdis,(fun c => (hcaps c).2.2.2),hRegion,
    hRegionV.trans (hVU.trans hU0J),hFront,
    chartwisePLBall_of_finitePLBallPair_in_chart e Q (fun x _ => hcover x) hQ
      (ContinuousLinearEquiv.ofFinrankEq (by simp) : P3 ≃L[ℝ] V3) hRegion hRegionQ,
    by simpa only [band,image_image] using hinc,hint,C,hC,hCcaps⟩


theorem ChartwisePLSphere.exists_witness_protected_cocore_region_of_disk
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
    ∃(k : ℕ) (sigma : P3 → V3) (caps : Bool → Set V3) (region : Set V3),
      region⊆U0 ∧
        let band := (fun z : P2 => sigma ((z.1,0),z.2)) ''
          (Icc (-1/4 : ℝ) (1/4) ×ˢ Icc (0 : ℝ) (k+3))
        FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3)) ∧
        MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3)) (interior J.space) ∧
        (∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          (H (sigma x)).2=t ↔ x.1∈signedTubeSheet 0) ∧
        (∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          Q.symm (sigma x)∈S ↔ x.1∈signedTubeSheet 1) ∧
        (∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          ∀y∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),sigma x=sigma y ↔ x.1=y.1 ∧
            (x.2=y.2 ∨ (x.2=0 ∧ y.2=k+3) ∨ (x.2=k+3 ∧ y.2=0))) ∧
        (fun u : ℝ => sigma ((0,0),u)) '' Icc (0 : ℝ) (k+3)=L.boundary ℝ ∧
        (∀c,IsFinitePLBallPair P2 (caps c)
          ((fun u : ℝ => sigma ((if c then 1/4 else -1/4,0),u)) '' Icc (0 : ℝ) (k+3)) ∧
          caps c∩Q.symm ⁻¹' S=
            (fun u : ℝ => sigma ((if c then 1/4 else -1/4,0),u)) '' Icc (0 : ℝ) (k+3)) ∧
        Disjoint (caps true) (caps false) ∧
        (∀c,Disjoint (caps c) {x | (H x).2=t}) ∧
        IsFinitePLBallPair P3 region (band∪(caps true∪caps false)) ∧
        region⊆interior J.space ∧ frontier region=band∪(caps true∪caps false) ∧
        Nonempty (ChartwisePLBall e (Q.symm '' region) (Q.symm '' (band∪(caps true∪caps false)))) ∧
        (Q.symm '' region)∩S=Q.symm '' band ∧
        Disjoint (interior (Q.symm '' region)) S ∧
        ∃C : ((_root_.Dehn.annulusSquare 8 0 : Set P2) × unitInterval) ≃ₜ region,
          ((Homeomorph.Set.prod _ (Icc (0 : ℝ) 1)).trans C).IsFinitePL ∧
          ∀c z,(C z : V3)∈caps c ↔ z.2=if c then 1 else 0 := by
  apply s.exists_witness_protected_cocore_region_of_disk_of_paired_charts hcover Q hQ J hJ hJQ H t L hLi hL hD hDsub hcontact hU0 hDU0 hU0J hisolate ?_
  intro w hw O hO hwO
  obtain ⟨B, hwB, hBO, hBw, hB, hBi, hBS, hheight⟩ := hcross w hw O hO hwO
  refine ⟨B, hwB, hBO, hBw, hB, hBi, hBS, ?_⟩
  intro x hx
  rw [← sub_eq_zero, hheight x hx]

theorem ChartwisePLSphere.exists_witness_protected_cocore_region
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
      ∃(n : ℕ) (L : Polygon V3 (n+3)) (k : ℕ) (sigma : P3 → V3)
        (caps : Bool → Set V3) (region : Set V3),
        let band := (fun z : P2 => sigma ((z.1,0),z.2)) ''
          (Icc (-1/4 : ℝ) (1/4) ×ˢ Icc (0 : ℝ) (k+3))
        Function.Injective L ∧ L.HasSimplicialEdges ∧
        L.boundary ℝ ⊆ (Q '' (S∩Q.source)∩interior J.space)∩{x | (H x).2=t} ∧
        IsCompact (((Q '' (S∩Q.source)∩J.space)∩{x | (H x).2=t})\L.boundary ℝ) ∧
        FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3)) ∧
        MapsTo sigma (signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3)) (interior J.space) ∧
        (∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          (H (sigma x)).2=t ↔ x.1∈signedTubeSheet 0) ∧
        (∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          Q.symm (sigma x)∈S ↔ x.1∈signedTubeSheet 1) ∧
        (∀x∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),
          ∀y∈signedTubeDiamond ×ˢ Icc (0 : ℝ) (k+3),sigma x=sigma y ↔ x.1=y.1 ∧
            (x.2=y.2 ∨ (x.2=0 ∧ y.2=k+3) ∨ (x.2=k+3 ∧ y.2=0))) ∧
        (fun u : ℝ => sigma ((0,0),u)) '' Icc (0 : ℝ) (k+3)=L.boundary ℝ ∧
        (∀c,IsFinitePLBallPair P2 (caps c)
          ((fun u : ℝ => sigma ((if c then 1/4 else -1/4,0),u)) '' Icc (0 : ℝ) (k+3)) ∧
          caps c∩Q.symm ⁻¹' S=
            (fun u : ℝ => sigma ((if c then 1/4 else -1/4,0),u)) '' Icc (0 : ℝ) (k+3)) ∧
        Disjoint (caps true) (caps false) ∧
        (∀c,Disjoint (caps c) {x | (H x).2=t}) ∧
        IsFinitePLBallPair P3 region (band∪(caps true∪caps false)) ∧
        region⊆interior J.space ∧ frontier region=band∪(caps true∪caps false) ∧
        Nonempty (ChartwisePLBall e (Q.symm '' region) (Q.symm '' (band∪(caps true∪caps false)))) ∧
        (Q.symm '' region)∩S=Q.symm '' band ∧
        Disjoint (interior (Q.symm '' region)) S ∧
        ∃C : ((_root_.Dehn.annulusSquare 8 0 : Set P2) × unitInterval) ≃ₜ region,
          ((Homeomorph.Set.prod _ (Icc (0 : ℝ) 1)).trans C).IsFinitePL ∧
          ∀c z,(C z : V3)∈caps c ↔ z.2=if c then 1 else 0) := by
  obtain ⟨t,ht,hpres,hempty | ⟨n,L,D,hLi,hL,hD,hDsub,hcontact,hrem,U0,hU0,hDU0,hU0J,hisolate,hcross⟩⟩ :=
    s.exists_cocore_innermost_disk_with_crossings_and_presentation Q hQ J hJ hJQ hJcv H hab hband
  · exact ⟨t,ht,hpres,Or.inl hempty⟩
  · obtain ⟨k,sigma,caps,region,_,hdata⟩ :=
      s.exists_witness_protected_cocore_region_of_disk hcover Q hQ J hJ hJQ H t
        L hLi hL hD hDsub hcontact hU0 hDU0 hU0J hisolate hcross
    have hLS : L.boundary ℝ⊆(Q '' (S∩Q.source)∩interior J.space)∩{x | (H x).2=t} :=
      fun x hx => ⟨⟨(hcontact.symm.subset hx).2,(hDsub (hD.1 hx)).1⟩,(hDsub (hD.1 hx)).2⟩
    exact ⟨t,ht,hpres,Or.inr ⟨n,L,k,sigma,caps,region,hLi,hL,hLS,hrem,hdata⟩⟩

end PoincareConjecture.M76
