import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalSpanningReplacement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningOriginalCornerSector
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningMatchingCornerBox
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningOriginalSideChart
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningPatchCrossings
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningSideProvenance







set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1
local notation "Rect" => (J ×ˢ I)
local notation "Ends" => (({0,1} : Set ℝ) ×ˢ I)
local notation "Sides" => (J ×ˢ ({-1,1} : Set ℝ))
local notation "Corners" => (({0,1} : Set ℝ) ×ˢ ({-1,1} : Set ℝ))
local notation "RectRim" => Ends ∪ Sides
local notation "Wide" => (Icc (-1 : ℝ) 2 ×ˢ I)
local notation "WideRim" => ((({-1,2} : Set ℝ) ×ˢ I) ∪ (Icc (-1 : ℝ) 2 ×ˢ ({-1,1} : Set ℝ)))

theorem HamiltonMarkedProtectedBall.exists_original_spanning_replacement_with_crossings
    {ι κ α V : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S W : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (s : ChartwisePLSphere e S) (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (hn : ¬∃ B,B ⊆ latticeHandleDomain ι κ L ∧ Nonempty (ChartwisePLBall e B S))
    (hW : PLDomain e W) (hWS : frontier W = S) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀ (_hcross : ∀ x ∈ S ∩ frontier E,∃ H : OpenPartialHomeomorph X V3,
      x ∈ H.source ∧ H x = 0 ∧
      (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0) ∧
      ∀ y ∈ H.source,y ∈ frontier E ↔ H y 0 = 0)
      {j : V2 → X} (P : OriginalDiskProduct e (E ∩ W) j)
      (_hNfront : frontier (E ∩ W) = (E ∩ W) ∩ (frontier E ∪ S))
      (_hPO : MapsTo P.map (Disk ×ˢ I) (interior R))
      {d U C : Set V} {a₀ a₁ : V}
      (_hd : IsFinitePLBallPair P2 d (U ∪ C))
      (_hU : IsFinitePLBallPair ℝ U {a₀,a₁}) (_hC : IsFinitePLBallPair ℝ C {a₀,a₁})
      (_hab : a₀ ≠ a₁) (_hUC : U ∩ C = {a₀,a₁})
      (H : Disk ≃ₜ d) (_hH : H.IsFinitePL)
      (_hHrim : ∀ z : Disk,(z : V2) ∈ Rim ↔ (H z : V) ∈ U ∪ C)
      {f : V → X} (_hj : ∀ z : Disk,j z = f (H z))
      (_hjU : ∀ z : Disk,j z ∈ frontier E ↔ (H z : V) ∈ U)
      (_hjC : ∀ z : Disk,j z ∈ S ↔ (H z : V) ∈ C)
      (_hmark : ∀ z ∈ Rim,∀ t ∈ I,
        (P.map (z,t) ∈ frontier E ↔ j z ∈ frontier E) ∧
        (P.map (z,t) ∈ S ↔ j z ∈ S)),
    ∃ (S' : Set X) (r : P2 → X),
      Nonempty (ChartwisePLSphere e S') ∧ S' ⊆ interior R ∧
      (¬∃ A,A ⊆ R ∧ Nonempty (ChartwisePLBall e A S')) ∧
      PolyhedralPLInCharts e r Rect ∧ InjOn r Rect ∧
      r '' Rect ⊆ frontier E ∩ D ∧ r (0,0) = f a₀ ∧ r (1,0) = f a₁ ∧
      r '' Rect ∩ (S ∩ frontier E) = r '' Ends ∧
      S' ∩ frontier E = ((S ∩ frontier E) \ (r '' Ends \ r '' Corners)) ∪ r '' Sides ∧
      ∀ x ∈ S' ∩ frontier E,∃ G : OpenPartialHomeomorph X V3,
        x ∈ G.source ∧ G x = 0 ∧
        (∀ i,(e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ G.source,y ∈ S' ↔ G y 1 = 0) ∧
        ∀ y ∈ G.source,y ∈ frontier E ↔ G y 0 = 0 := by
  classical
  intro X R E hcross j P hNfront hPO d U C a₀ a₁ hd hU hC hab hUC H hH hHrim f hj hjU hjC hmark
  obtain ⟨k,B,T,r,a,cap,hk,hki,hk0,hkP,hB,hT,hball,hBE,hBR,hkE,hkS,
    hr,hri,hrimage,hrSides,hBF,hTF,hTout,hrMap,hr0,hr1,hrS,ha,hai,haimage,hBSa,haT,har,haF,
    hcap,hcapi,hcapDW,hcapR,hcap0,hcapE,hcapends,hcapbase,hcapball,hret,
    Q,T',S',f',g,d',q',⟨bQ⟩,hQ,hQR,hdWide,hf',hfi',hQS,hfT,
    hd',hg,hgi,hgd,hgq,hSp,hs',hSR',hn',hQS',hgdF,hnew⟩ :=
    b.exists_original_spanning_replacement he hdim hi s hSR hn hW hWS hcross
      P hNfront hPO hd hU hC hab hUC H hH hHrim hj hjU hjC hmark
  obtain ⟨Hc,v,c,vInv,hHc,hv,hHv,hc,hci,hvInv,hHi,hcapval,hcapimage,K,q,Pc,hPc,hPcInv⟩ := hret
  have hvimage : v '' Disk = Rect := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      exact hHv ⟨z,hz⟩ ▸ (Hc ⟨z,hz⟩).property
    · intro z hz
      refine ⟨Hc.symm ⟨z,hz⟩,(Hc.symm ⟨z,hz⟩).property,?_⟩
      rw [←hHv,Hc.apply_symm_apply]
  have hbaseimage : (r ∘ v) '' Disk = r '' Rect := by rw [image_comp,hvimage]
  have hBhalf : B = P.map '' (Disk ×ˢ Icc (-1/2 : ℝ) (1/2)) := by
    rw [hB]
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      refine ⟨(H.symm ⟨z.1,hz.1⟩,z.2/2),⟨(H.symm ⟨z.1,hz.1⟩).property,?_⟩,
        (hkP z hz).symm⟩
      constructor <;> linarith [hz.2.1,hz.2.2]
    · rintro _ ⟨z,hz,rfl⟩
      have ht : 2*z.2 ∈ I := by constructor <;> linarith [hz.2.1,hz.2.2]
      refine ⟨((H ⟨z.1,hz.1⟩ : V),2*z.2),⟨(H ⟨z.1,hz.1⟩).property,ht⟩,?_⟩
      rw [hkP _ ⟨(H ⟨z.1,hz.1⟩).property,ht⟩]
      simp only [H.symm_apply_apply]
      congr 1
      apply Prod.ext
      · rfl
      · dsimp
        ring
  have hcapPc : cap '' (Rect ×ˢ J) = Pc.map '' (Disk ×ˢ J) := by rw [hPc]; exact hcapimage
  have hQPc : Q = B ∪ Pc.map '' (Disk ×ˢ J) := by rw [←hcapPc]; exact hQ
  have hbasePc : B ∩ frontier E = (r ∘ v) '' Disk := hBF.trans hbaseimage.symm
  have hCapEPc : Pc.map '' (Disk ×ˢ J) ∩ E = (r ∘ v) '' Disk := by
    rw [←hcapPc,hcapbase,hbaseimage]
  have hPatchS : f' '' Wide ⊆ S := fun _ hx => (hQS.symm.subset hx).2
  have hSout : (S \ f' '' Wide).Nonempty := by
    by_contra hnone
    have hSQ : S ⊆ Q := by
      intro x hx
      apply (hQS.symm.subset ?_).1
      by_contra hnot
      exact hnone ⟨x,hx,hnot⟩
    obtain ⟨A,hAQ,hA⟩ := s.exists_original_closed_ball_filling he.compatible bQ hSQ
    exact hn ⟨A,hAQ.trans (hQR.trans interior_subset),hA⟩
  have hsideRect : Sides ⊆ Rect := by
    rintro z ⟨hz,ht⟩
    refine ⟨hz,?_⟩
    rcases ht with ht | ht <;> norm_num [show z.2 = _ from ht]
  have hTout' : (T' \ f' '' Wide).Nonempty := by
    have hz : ((1/2,1) : P2) ∈ Sides := ⟨by norm_num,by simp⟩
    have hxg := (hgdF.symm.subset ⟨(1/2,1),hz,rfl⟩).1
    refine ⟨r (1/2,1),(hgd.subset hxg).1,?_⟩
    intro hx
    have hbad := (hrS (1/2,1) (hsideRect hz)).mp (hPatchS hx)
    norm_num at hbad
  have hSformula : S' = (S \ (f' '' Wide \ f' '' WideRim)) ∪
      (T' \ (f' '' Wide \ f' '' WideRim)) := by rw [hSp,hgd]
  have hrFD : r '' Rect ⊆ frontier E ∩ D := by
    rintro _ ⟨z,hz,rfl⟩
    exact ⟨(hrMap hz).1.1,b.ball.boundary_subset
      ((b.frontier_complement_iff_interior he hdim hi (hrMap hz).2).mp (hrMap hz).1.1)⟩
  have htrace : r '' Rect ∩ (S ∩ frontier E) = r '' Ends := by
    apply Subset.antisymm
    · rintro _ ⟨⟨z,hz,rfl⟩,hzS,hzF⟩
      exact ⟨z,⟨(hrS z hz).mp hzS,hz.2⟩,rfl⟩
    · rintro _ ⟨z,hz,rfl⟩
      have hzR : z ∈ Rect := by
        refine ⟨?_,hz.2⟩
        rcases hz.1 with h | h <;> norm_num [show z.1 = _ from h]
      exact ⟨⟨z,hzR,rfl⟩,(hrS z hzR).mpr hz.1,(hrMap hzR).1.1⟩
  refine ⟨S',r,hs',hSR',hn',hr,hri,hrFD,?_,?_,htrace,hnew,?_⟩
  · rw [hr0 0 (by norm_num),hk0 a₀ (hd.1 (Or.inl (hU.1 (by simp))))]
  · rw [hr1 0 (by norm_num),hk0 a₁ (hd.1 (Or.inl (hU.1 (by simp))))]
  · intro x hx
    by_cases hxQ : x ∈ Q
    · have hxSides : x ∈ r '' Sides := hgdF.subset ⟨hQS'.subset ⟨hxQ,hx.1⟩,hx.2⟩
      by_cases hxS : x ∈ S
      · have hxCorner : x ∈ r '' Corners := by
          obtain ⟨z,hz,rfl⟩ := hxSides
          exact ⟨z,⟨(hrS z (hsideRect hz)).mp hxS,hz.2⟩,rfl⟩
        obtain ⟨endpoint,hepoint,positive,kWide,qCorner,u,hw,hq,hqi,hqd,hq0,
          hu,hui,huval,hu0,huMap,huF,huS,huB⟩ :=
          P.exists_original_spanning_corner_sector hNfront hPO hd hU hC hab hUC H hH hHrim
            hj hjU hjC hmark hkP hr0 hr1 hxCorner
        obtain ⟨G,hxG,hGx,hGe,hGS,hGF⟩ := b.paired_corner_chart_of_inside_sector
          he hdim hi s hW hWS bQ Pc hQPc hBE hCapEPc hbasePc hdWide f' hf' hfi'
          hQS hfT hSout hTout' hu hui (image_subset_iff.mp huMap) huF huS
          (fun z hz => by rw [hBhalf]; exact huB z hz) hcross
        refine ⟨G,hu0 ▸ hxG,hu0 ▸ hGx,hGe,?_,hGF⟩
        simpa only [hSformula] using hGS
      · obtain ⟨z,hzrim,_,positive,hxP'⟩ := P.exists_half_height_of_spanning_side
          (fun y hy => hd.1 (Or.inl hy)) H hHrim hkP hrSides hxSides
        have hxP := hxP'.symm
        obtain ⟨G,hxG,hGx,_,hGe,hGS,hGF⟩ := b.exists_spanning_side_chart_at_half_height
          he hdim hi hWS s.isCompact.isClosed P hNfront hPO Pc bQ
          (hQPc.trans (by rw [hBhalf])) (by rw [←hBhalf]; exact hbasePc)
          hPatchS hzrim positive (by simpa only [hxP] using hxS)
        refine ⟨G,hxP ▸ hxG,hxP ▸ hGx,hGe,?_,hGF⟩
        simpa only [hSformula] using hGS
    · obtain ⟨G,hxG,hGx,_,hGe,hGS,hGF⟩ := bQ.patch_pair_charts_off_ball hfT hcross
        x ⟨hSformula ▸ hx.1,hx.2⟩ hxQ
      refine ⟨G,hxG,hGx,hGe,?_,hGF⟩
      simpa only [hSformula] using hGS

end PoincareConjecture.M76
