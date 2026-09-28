import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningInsideHalfBox
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningCapBaseExtension
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningJoinedSectorCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningProtectedCorner

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Band" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1
local notation "Square" => Set.prod Band Band
local notation "Minus" => Set.prod Square (Icc (-1 : ℝ) 0)
local notation "Plus" => Set.prod Square J

theorem HamiltonMarkedProtectedBall.exists_spanning_side_chart_at_half_height
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀ {W S : Set X} {f : V2 → X} (_hWS : frontier W = S) (_hS : IsClosed S)
      (P : OriginalDiskProduct e (E ∩ W) f)
      (_hNfront : frontier (E ∩ W) = (E ∩ W) ∩ (frontier E ∪ S))
      (_hPO : MapsTo P.map (Disk ×ˢ Band) (interior R))
      {O K : Set X} {j : V2 → X} {t : Finset (D ∪ K : Set X)}
      (Pc : RelativeFrontierDiskProduct e D W O j K t)
      {Q T Patch Boundary : Set X} (_ball : ChartwisePLBall e Q T)
      (_hQ : Q = P.map '' (Disk ×ˢ Icc (-1/2 : ℝ) (1/2)) ∪ Pc.map '' (Disk ×ˢ J))
      (_hbase : (P.map '' (Disk ×ˢ Icc (-1/2 : ℝ) (1/2))) ∩ frontier E = j '' Disk)
      (_hPatch : Patch ⊆ S)
      {z : V2} (_hz : z ∈ Rim) (positive : Bool)
      (_hclear : P.map (z,if positive then (1/2 : ℝ) else -1/2) ∉ S),
    ∃ G : OpenPartialHomeomorph X V3,
      P.map (z,if positive then (1/2 : ℝ) else -1/2) ∈ G.source ∧
      G (P.map (z,if positive then (1/2 : ℝ) else -1/2)) = 0 ∧ G.source ⊆ Sᶜ ∧
      (∀ i,(e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ G.source,y ∈ (S \ (Patch \ Boundary)) ∪ (T \ (Patch \ Boundary)) ↔ G y 1 = 0) ∧
      ∀ y ∈ G.source,y ∈ frontier E ↔ G y 0 = 0 := by
  intro X R E W S f hWS hS P hNfront hPO O K j t Pc Q T Patch Boundary ball hQ hbase hPatch z hz positive hclear
  let B := P.map '' (Disk ×ˢ Icc (-1/2 : ℝ) (1/2))
  let Cap := Pc.map '' (Disk ×ˢ J)
  have hBE : B ⊆ E := by
    rintro _ ⟨w,hw,rfl⟩
    exact (P.inside ⟨hw.1,by constructor <;> linarith [hw.2.1,hw.2.2]⟩).1
  have hjF : MapsTo j Disk (frontier E) := fun w hw => (hbase.symm.subset ⟨w,hw,rfl⟩).2
  have hout : E ⊆ (interior D)ᶜ := closure_minimal
    (fun _ hy h => hy.2 (interior_subset h)) isOpen_interior.isClosed_compl
  have hCapE : Cap ∩ E = j '' Disk := by
    apply Subset.antisymm
    · rintro _ ⟨⟨w,hw,rfl⟩,hwE⟩
      have hzero := (Pc.map_frontier w hw).mp
        ⟨subset_closure (Pc.map_inside hw).1.1.1,hout hwE⟩
      rw [show w = (w.1,0) from Prod.ext rfl hzero,Pc.map_central _ hw.1]
      exact ⟨w.1,hw.1,rfl⟩
    · rintro _ ⟨w,hw,rfl⟩
      exact ⟨⟨(w,0),⟨hw,by norm_num⟩,Pc.map_central w hw⟩,
        isClosed_closure.frontier_subset (hjF hw)⟩
  obtain ⟨H,ε,u,_,_,_,_,hu,hui,_,hu0,huNS,huF,huB,huP⟩ :=
    P.exists_inside_half_box_at_half_height_with_image hNfront hS hz positive hclear
  let a : P2 → X := fun q => u (q,0)
  let base : P2 →ᴬ[ℝ] C3 := (ContinuousAffineMap.id ℝ P2).prod
    (ContinuousAffineMap.const ℝ P2 (0 : ℝ))
  have hbaseval (q : P2) : base q = (q,0) := rfl
  have hbmap : MapsTo base Square Minus := fun q hq =>
    show (q,0) ∈ Minus from ⟨hq,by norm_num⟩
  have hbf : FinitePiecewiseAffineOn base Square := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨M,hM,hMs,_⟩,_⟩,_⟩ :=
      (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).prod
        (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
    exact ⟨M,hM,hMs,M.affineOnFaces_affine base⟩
  have ha : PolyhedralPLInCharts e a Square := by
    obtain ⟨M,hM,hMs,hMf⟩ := hbf
    rw [←hMs]
    exact hu.comp_finitePiecewiseAffineOn M hM ⟨M,hM,rfl,hMf⟩
      (fun q hq => hbmap (hMs.subset hq))
  have hai : InjOn a Square := by
    intro q hq w hw heq
    exact congrArg Prod.fst (hui (hbmap hq) (hbmap hw) heq)
  have haR : MapsTo a Square (interior R) := by
    intro q hq
    obtain ⟨w,hw,heq⟩ := huP ⟨(q,0),hbmap hq,rfl⟩
    change u (q,0) ∈ interior R
    rw [←heq]
    exact hPO hw
  have haF (q : P2) (hq : q ∈ Square) : a q ∈ frontier E := (huF (q,0) (hbmap hq)).mpr rfl
  have haS : MapsTo a Square (frontier D ∩ W) := fun q hq =>
    ⟨(b.frontier_complement_iff_interior he hdim hi (haR hq)).mp (haF q hq),
      (huNS ⟨(q,0),hbmap hq,rfl⟩).1.2⟩
  have haW (q : P2) (hq : q ∈ Square) : a q ∉ frontier W := by
    rw [hWS]
    exact (huNS ⟨(q,0),hbmap hq,rfl⟩).2
  have haCap (q : P2) (hq : q ∈ Square) : a q ∈ j '' Disk ↔ q.1 ≤ 0 := by
    rw [←hbase]
    exact (and_iff_left (haF q hq)).trans (huB (q,0) (hbmap hq))
  obtain ⟨δ,v,_,_,_,hv,hvi,hvDW,hv0,hvD,hvCap⟩ :=
    Pc.exists_cap_side_box ha hai haS haW haCap isOpen_interior (image_subset_iff.mpr haR)
  have hvE (q : C3) (hq : q ∈ Plus) : v q ∈ E ↔ q.2 = 0 := by
    constructor
    · intro h
      exact (hvD q hq).mp ⟨subset_closure (hvDW hq).1.1.1,hout h⟩
    · intro h
      rw [show q = (q.1,0) from Prod.ext rfl h,hv0 q.1 hq.1]
      exact isClosed_closure.frontier_subset (haF q.1 hq.1)
  have hvF (q : C3) (hq : q ∈ Plus) : v q ∈ frontier E ↔ q.2 = 0 :=
    (b.frontier_complement_iff_interior he hdim hi (hvDW hq).1.2.1).trans (hvD q hq)
  have huv : EqOn u v (Square ×ˢ ({0} : Set ℝ)) := by
    intro q hq
    have hzero : q.2 = 0 := hq.2
    rw [show q = (q.1,0) from Prod.ext rfl hzero,hv0 q.1 hq.1]
  have hzero : (0 : C3) ∈ Minus := by
    change (((-1 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1) ∧ ((-1 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1)) ∧
      ((-1 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 0)
    norm_num
  obtain ⟨G,hxG,hGx,hGS,hGe,hpatch,hGF⟩ := ball.patch_side_chart_of_joined_sectors
    he.compatible hQ hBE hCapE hbase hS hPatch hu hui hv hvi
    (fun q hq => (huNS ⟨q,hq,rfl⟩).1.1) hvE huv ((huNS ⟨0,hzero,rfl⟩).2)
    (fun q hq => ⟨huF q hq,huB q hq⟩) (fun q hq => ⟨hvF q hq,hvCap q hq⟩)
  exact ⟨G,hu0 ▸ hxG,hu0 ▸ hGx,hGS,hGe,hpatch,hGF⟩

end PoincareConjecture.M76
