import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcDiskSplit
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcHeterogeneousUnion
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates



set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
open Dehn.Annuli.BoundaryUnionDisk
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

theorem exists_original_terminal_joined_disk
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {A U C Z : Set P2} {a b c d : P2} {f p : P2 → X} {j : V2 → X}
    {S N : Set X} (hN : IsClosed N)
    (hA : IsFinitePLBallPair P2 A (U ∪ C))
    (hU : IsFinitePLBallPair ℝ U {a,b}) (hC : IsFinitePLBallPair ℝ C {a,b})
    (hUC : U ∩ C = {a,b}) (hab : a ≠ b)
    (hZ : IsFinitePLBallPair ℝ Z {c,d})
    (hf : PolyhedralPLInCharts e f A) (hfi : InjOn f A)
    (hp : PolyhedralPLInCharts e p Z) (hpi : InjOn p Z)
    (hj : PolyhedralPLInCharts e j Disk) (hji : InjOn j Disk)
    (h0 : f a = p c) (h1 : f b = p d)
    (hrim : j '' Rim = f '' U ∪ p '' Z)
    (hUZ : f '' U ∩ p '' Z = {f a,f b})
    (hAj : f '' A ∩ j '' Disk = f '' U)
    (hAS : f '' A ∩ S = f '' C) (hjS : j '' Disk ∩ S = p '' Z)
    (hAN : f '' A ⊆ N) (hjN : j '' Disk ⊆ frontier N)
    (hAF : f '' A ∩ frontier N = f '' U) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k whole ∧ InjOn k whole ∧
      k '' whole = f '' A ∪ j '' Disk ∧
      k '' frontier whole = f '' C ∪ p '' Z ∧
      k '' whole ⊆ N ∧ k '' whole ∩ S = k '' frontier whole ∧
      k '' whole ∩ frontier N = j '' Disk := by
  classical
  have hstd : IsFinitePLBallPair P2 Disk Rim :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have hUA : U ⊆ A := subset_union_left.trans hA.1
  have hfU : PolyhedralPLInCharts e f U := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hU
    exact hKs ▸ hf.restrict_finite K hK (hKs.subset.trans hUA)
  obtain ⟨JU,JZ,x,y,hJU,hJZ,hcover,hinter,hxy,hjU,hjZ,hx,hy⟩ :=
    exists_original_disk_boundary_arc_split he hstd hU hZ hj hji hfU
      (hfi.mono hUA) hp hpi hab h0 h1 hrim hUZ
  let E : Bool → Type := Bool.rec P2 V2
  let nc : ∀ i : Bool, NormedAddCommGroup (E i) := Bool.rec
    (motive := fun i => NormedAddCommGroup (E i))
    (inferInstance : NormedAddCommGroup P2) (inferInstance : NormedAddCommGroup V2)
  let ns : ∀ i : Bool, @NormedSpace ℝ (E i) Real.normedField (nc i).toSeminormedAddCommGroup := Bool.rec
    (motive := fun i => @NormedSpace ℝ (E i) Real.normedField (nc i).toSeminormedAddCommGroup)
    (inferInstance : NormedSpace ℝ P2) (inferInstance : NormedSpace ℝ V2)
  let fd : ∀ i : Bool, @FiniteDimensional ℝ (E i) Real.instDivisionRing
      (nc i).toAddCommGroup (ns i).toModule := Bool.rec
    (motive := fun i => @FiniteDimensional ℝ (E i) Real.instDivisionRing
      (nc i).toAddCommGroup (ns i).toModule)
    (inferInstance : FiniteDimensional ℝ P2) (inferInstance : FiniteDimensional ℝ V2)
  let Ds : ∀ i, Set (E i) := Bool.rec (motive := fun i => Set (E i)) A Disk
  let Us : ∀ i, Set (E i) := Bool.rec (motive := fun i => Set (E i)) C JZ
  let Ws : ∀ i, Set (E i) := Bool.rec (motive := fun i => Set (E i)) U JU
  let as : ∀ i, E i := Bool.rec (motive := E) a x
  let bs : ∀ i, E i := Bool.rec (motive := E) b y
  let fs : ∀ i, E i → X := Bool.rec (motive := fun i => E i → X) f j
  have hDs (i : Bool) : @IsFinitePLBallPair P2 _ _ (E i) (nc i) (ns i)
      (Ds i) (Set.union (Us i) (Ws i)) := by
    cases i
    · change IsFinitePLBallPair P2 A (C ∪ U)
      rw [union_comm]
      exact hA
    · change IsFinitePLBallPair P2 Disk (JZ ∪ JU)
      rw [union_comm,hcover]
      exact hstd
  have hUs (i : Bool) : @IsFinitePLBallPair ℝ _ _ (E i) (nc i) (ns i)
      (Us i) (Set.insert (as i) (Set.singleton (bs i))) := by
    cases i
    · exact hC
    · exact hJZ
  have hWs (i : Bool) : @IsFinitePLBallPair ℝ _ _ (E i) (nc i) (ns i)
      (Ws i) (Set.insert (as i) (Set.singleton (bs i))) := by
    cases i
    · exact hU
    · exact hJU
  have hUW (i : Bool) : Set.inter (Us i) (Ws i) =
      Set.insert (as i) (Set.singleton (bs i)) := by
    cases i
    · exact (inter_comm _ _).trans hUC
    · exact (inter_comm _ _).trans hinter
  have habs (i : Bool) : as i ≠ bs i := by cases i; exact hab; exact hxy
  have hfs (i : Bool) : @PolyhedralPLInCharts (E i) V3 X ι (nc i) (ns i) _ _ _
      e (fs i) (Ds i) := by
    cases i; exact hf; exact hj
  have hfis (i : Bool) : InjOn (fs i) (Ds i) := by cases i; exact hfi; exact hji
  obtain ⟨k,hk,hki,hke,hhalf,hrims⟩ :=
    @exists_original_union_disk_map_heterogeneous X ι E _ _ nc ns fd e he Ds Us Ws as bs fs
      hDs hUs hWs hUW habs hfs hfis hjU.symm hx.symm hy.symm hAj
  have himage : k '' whole = f '' A ∪ j '' Disk := by
    rw [←half_union,image_union,hhalf false,hhalf true]
  have hrim' : k '' frontier whole = f '' C ∪ p '' Z := by
    have hcoverrim : frontier whole = (half false ∩ frontier whole) ∪
        (half true ∩ frontier whole) := by
      rw [←union_inter_distrib_right,half_union]
      exact (inter_eq_right.mpr whole_ball.1).symm
    rw [hcoverrim,image_union,hrims false,hrims true]
    exact congrArg (fun T => f '' C ∪ T) hjZ
  refine ⟨k,hk,hki,himage,hrim',?_,?_,?_⟩
  · rw [himage]
    exact union_subset hAN (hjN.trans hN.frontier_subset)
  · rw [himage,union_inter_distrib_right,hAS,hjS,hrim']
  · rw [himage,union_inter_distrib_right,hAF,
      inter_eq_left.mpr hjN,union_eq_right.mpr]
    exact hAj.symm.subset.trans inter_subset_right

end PoincareConjecture.M76

