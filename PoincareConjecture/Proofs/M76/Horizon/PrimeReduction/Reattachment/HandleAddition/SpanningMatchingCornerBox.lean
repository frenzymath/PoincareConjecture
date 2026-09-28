import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningCapBaseExtension
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningProtectedCorner
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningJoinedSectorCharts

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1
local notation "Rect" => Set.prod I J
local notation "Minus" => Set.prod (Set.prod (Icc (-1 : ℝ) 0) I) J
local notation "Plus" => Set.prod (Set.prod J I) J
local notation "Base" => Set.prod (Set.prod ({0} : Set ℝ) I) J

theorem HamiltonMarkedProtectedBall.exists_matching_protected_corner_box
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S W O K B : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (hWS : frontier W = S)
    {j : V2 → LatticeHandleAmbient ι κ L} {s : Finset (D ∪ K : Set (LatticeHandleAmbient ι κ L))}
    (P : RelativeFrontierDiskProduct e D W O j K s) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀ (_hBF : B ∩ frontier E = j '' Disk)
      {u : C3 → X} (_hu : PolyhedralPLInCharts e u Minus) (_hui : InjOn u Minus)
      (_huMap : MapsTo u Minus ((E ∩ W) ∩ interior R))
      (_huF : ∀ z ∈ Minus,u z ∈ frontier E ↔ z.1.1 = 0)
      (_huS : ∀ z ∈ Minus,u z ∈ S ↔ z.2 = 0)
      (_huB : ∀ z ∈ Minus,u z ∈ B ↔ z.1.2 ≤ 0),
    ∃ v : C3 → X,
      PolyhedralPLInCharts e v Plus ∧ InjOn v Plus ∧
      MapsTo v Plus ((D ∩ W) ∩ interior R) ∧ EqOn u v Base ∧
      (∀ z ∈ Plus,v z ∈ E ↔ z.1.1 = 0) ∧
      (∀ z ∈ Plus,v z ∈ frontier E ↔ z.1.1 = 0) ∧
      (∀ z ∈ Plus,v z ∈ S ↔ z.2 = 0) ∧
      ∀ z ∈ Plus,v z ∈ P.map '' (Disk ×ˢ J) ↔ z.1.2 ≤ 0 := by
  intro X R E hBF u hu hui huMap huF huS huB
  let A : P2 →L[ℝ] C3 :=
    ((0 : P2 →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hAval (z : P2) : A z = ((0,z.1),z.2) := rfl
  have hAmap : MapsTo A Rect Minus := by
    intro z hz
    exact ⟨⟨by norm_num [hAval],hz.1⟩,hz.2⟩
  have hAf : FinitePiecewiseAffineOn A Rect := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨T,hT,hTs,_⟩,_⟩,_⟩ :=
      (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).prod
        (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
    exact ⟨T,hT,hTs,T.affineOnFaces_affine A.toContinuousAffineMap⟩
  let a := u ∘ A
  have ha : PolyhedralPLInCharts e a Rect := by
    obtain ⟨T,hT,hTs,hTf⟩ := hAf
    rw [←hTs]
    exact hu.comp_finitePiecewiseAffineOn T hT ⟨T,hT,rfl,hTf⟩
      (fun z hz => hAmap (hTs.subset hz))
  have hai : InjOn a Rect := by
    intro z hz w hw heq
    have h := hui (hAmap hz) (hAmap hw) heq
    exact Prod.ext (congrArg (fun z : C3 => z.1.2) h) (congrArg (fun z : C3 => z.2) h)
  have haF (z) (hz : z ∈ Rect) : a z ∈ frontier E := (huF (A z) (hAmap hz)).mpr rfl
  have haDW : MapsTo a Rect (frontier D ∩ W) := by
    intro z hz
    exact ⟨(b.frontier_complement_iff_interior he hdim hi (huMap (hAmap hz)).2).mp
      (haF z hz),(huMap (hAmap hz)).1.2⟩
  have haW (z) (hz : z ∈ Rect) : a z ∈ frontier W ↔ z.2 = 0 := by
    rw [hWS]
    exact huS (A z) (hAmap hz)
  have haCap (z) (hz : z ∈ Rect) : a z ∈ j '' Disk ↔ z.1 ≤ 0 := by
    rw [←hBF]
    exact (and_iff_left (haF z hz)).trans (huB (A z) (hAmap hz))
  have haR : a '' Rect ⊆ interior R := by
    rintro _ ⟨z,hz,rfl⟩
    exact (huMap (hAmap hz)).2
  obtain ⟨_,v,_,_,_,hv,hvi,hvMap,hv0,hvD,hvS,hvCap⟩ :=
    P.exists_cap_quarter_box ha hai haDW haW haCap isOpen_interior haR
  have hvR (z) (hz : z ∈ Plus) : v z ∈ interior R := (hvMap hz).2.1
  have hvF (z) (hz : z ∈ Plus) : v z ∈ frontier E ↔ z.1.1 = 0 :=
    (b.frontier_complement_iff_interior he hdim hi (hvR z hz)).trans (hvD z hz)
  have hout : E ⊆ (interior D)ᶜ := closure_minimal
    (fun _ hy hz => hy.2 (interior_subset hz)) isOpen_interior.isClosed_compl
  refine ⟨v,hv,hvi,fun z hz => ⟨(hvMap hz).1,hvR z hz⟩,?_,?_,hvF,?_,hvCap⟩
  · intro z hz
    have h := hv0 (z.1.2,z.2) ⟨hz.1.2,hz.2⟩
    have heq : z = ((0,z.1.2),z.2) := Prod.ext (Prod.ext hz.1.1 rfl) rfl
    rw [heq]
    exact h.symm
  · intro z hz
    constructor
    · intro hzE
      exact (hvD z hz).mp ⟨subset_closure (hvMap hz).1.1,hout hzE⟩
    · intro hz0
      exact isClosed_closure.frontier_subset ((hvF z hz).mpr hz0)
  · intro z hz
    simpa only [hWS] using hvS z hz

theorem HamiltonMarkedProtectedBall.paired_corner_chart_of_inside_sector
    {ι κ α V : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S W O K B Q T : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (sS : ChartwisePLSphere e S) (hW : PLDomain e W) (hWS : frontier W = S)
    (bQ : ChartwisePLBall e Q T)
    {j : V2 → LatticeHandleAmbient ι κ L} {s : Finset (D ∪ K : Set (LatticeHandleAmbient ι κ L))}
    (P : RelativeFrontierDiskProduct e D W O j K s) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀ (_hQ : Q = B ∪ P.map '' (Disk ×ˢ J)) (_hBE : B ⊆ E ∩ W)
      (_hCapE : P.map '' (Disk ×ˢ J) ∩ E = j '' Disk)
      (_hBF : B ∩ frontier E = j '' Disk)
      {d q : Set V} (_hd : IsFinitePLBallPair P2 d q)
      (p : V → X) (_hp : PolyhedralPLInCharts e p d) (_hpi : InjOn p d)
      (_hcontact : Q ∩ S = p '' d) (_hdT : p '' d ⊆ T)
      (_hSout : (S \ p '' d).Nonempty) (_hTout : (T \ p '' d).Nonempty)
      {u : C3 → X} (_hu : PolyhedralPLInCharts e u Minus) (_hui : InjOn u Minus)
      (_huMap : MapsTo u Minus ((E ∩ W) ∩ interior R))
      (_huF : ∀ z ∈ Minus,u z ∈ frontier E ↔ z.1.1 = 0)
      (_huS : ∀ z ∈ Minus,u z ∈ S ↔ z.2 = 0)
      (_huB : ∀ z ∈ Minus,u z ∈ B ↔ z.1.2 ≤ 0)
      (_hcross : ∀ x ∈ S ∩ frontier E,∃ H : OpenPartialHomeomorph X V3,
        x ∈ H.source ∧ H x = 0 ∧
        (∀ i,(e i).symm.trans H ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ H.source,y ∈ S ↔ H y 1 = 0) ∧
        ∀ y ∈ H.source,y ∈ frontier E ↔ H y 0 = 0),
    ∃ G : OpenPartialHomeomorph X V3,
      u 0 ∈ G.source ∧ G (u 0) = 0 ∧
      (∀ i,(e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ G.source,y ∈ (S \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q)) ↔ G y 1 = 0) ∧
      ∀ y ∈ G.source,y ∈ frontier E ↔ G y 0 = 0 := by
  intro X R E hQ hBE hCapE hBF d q hd p hp hpi hcontact hdT hSout hTout u hu hui huMap huF huS huB hcross
  obtain ⟨v,hv,hvi,hvMap,huv,hvE,hvF,hvS,hvCap⟩ :=
    b.exists_matching_protected_corner_box he hdim hi hWS P hBF hu hui huMap huF huS huB
  have hQW : Q ⊆ W := by
    rw [hQ]
    refine union_subset (hBE.trans inter_subset_right) ?_
    rintro _ ⟨z,hz,rfl⟩
    exact (P.map_inside hz).1.1.2
  have h0 : (0 : C3) ∈ Minus := by
    change (((0 : ℝ) ∈ Icc (-1) 0) ∧ ((0 : ℝ) ∈ I)) ∧ ((0 : ℝ) ∈ J)
    norm_num
  obtain ⟨H,hxH,hHx,hHe,hHS,hHF⟩ := hcross (u 0)
    ⟨(huS 0 h0).mpr rfl,(huF 0 h0).mpr rfl⟩
  exact sS.patch_corner_chart_of_joined_sectors bQ hW hWS hQ
    (hBE.trans inter_subset_left) hQW hCapE hBF hd p hp hpi hcontact hdT hSout hTout
    hu hui hv hvi (fun _ hz => (huMap hz).1.1) hvE huv
    (fun z hz => ⟨(huMap hz).1.2,huS z hz,huF z hz,huB z hz⟩)
    (fun z hz => ⟨(hvMap hz).1.2,hvS z hz,hvF z hz,hvCap z hz⟩)
    H hxH hHx hHe hHS hHF

end PoincareConjecture.M76
