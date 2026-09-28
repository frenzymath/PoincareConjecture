import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcOriginalUnion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedArcSphereObstruction
import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskProduct








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

theorem terminal_disk_subset_original_bigon_side
    {X : Type*} [TopologicalSpace X] {W S Z : Set X}
    (hW : IsClosed W) (hWS : frontier W = S)
    {A U C : Set P2} {a b : P2} {f : P2 → X} {j : V2 → X}
    (hA : IsFinitePLBallPair P2 A (U ∪ C))
    (hU : IsFinitePLBallPair ℝ U {a,b}) (hUC : U ∩ C = {a,b})
    (hfi : InjOn f A) (hAS : f '' A ∩ S = f '' C) (hAW : f '' A ⊆ W)
    (hj : ContinuousOn j Disk) (hji : InjOn j Disk)
    (hjr : j '' Rim = f '' U ∪ Z) (hjS : j '' Disk ∩ S = Z) :
    j '' Disk ⊆ W ∧ j '' Disk \ S ⊆ interior W := by
  have hUA : U ⊆ A := subset_union_left.trans hA.1
  have hCA : C ⊆ A := subset_union_right.trans hA.1
  have hstd : IsFinitePLBallPair V2 Disk Rim := isFinitePLBallPair_unit_cube
  have hZrim : Z ⊆ j '' Rim := fun x hx => hjr.symm.subset (Or.inr hx)
  let N : Set X := j '' Disk \ S
  have hinner : j '' (Disk \ Rim) ⊆ N := by
    rintro _ ⟨z,hz,rfl⟩
    refine ⟨mem_image_of_mem j hz.1,?_⟩
    intro hs
    obtain ⟨w,hw,hh⟩ := hZrim (hjS.subset ⟨mem_image_of_mem j hz.1,hs⟩)
    exact hz.2 (hji (sphere_subset_closedBall hw) hz.1 hh ▸ hw)
  have hdense : j '' Disk ⊆ closure (j '' (Disk \ Rim)) := by
    have hh := (show ContinuousOn j (closure (Disk \ Rim)) from hstd.closure_sdiff.symm ▸ hj).image_closure
    rwa [hstd.closure_sdiff] at hh
  have hconn : IsPreconnected N :=
    ((hstd.isConnected_sdiff.isPreconnected).image j (hj.mono sdiff_subset)).subset_closure
      hinner (sdiff_subset.trans hdense)
  obtain ⟨z,hz,hzend⟩ := hU.sdiff_nonempty
  have hzS : f z ∉ S := by
    intro hs
    obtain ⟨w,hw,hh⟩ := hAS.subset ⟨mem_image_of_mem f (hUA hz),hs⟩
    have hwz := hfi (hCA hw) (hUA hz) hh
    exact hzend (hUC.subset ⟨hz,hwz ▸ hw⟩)
  have hzN : f z ∈ N :=
    ⟨(image_mono sphere_subset_closedBall) (hjr.symm.subset (Or.inl (mem_image_of_mem f hz))),hzS⟩
  have hzW : f z ∈ W := hAW (mem_image_of_mem f (hUA hz))
  have havoid : Disjoint N (frontier W) := by
    rw [hWS]
    exact disjoint_left.mpr (fun x hx hs => hx.2 hs)
  have hN : N ⊆ interior W := by
    rcases preconnected_interior_or_exterior_of_frontier_avoidance hW hconn havoid with hi | ho
    · exact hi
    · exact False.elim (ho hzN hzW)
  refine ⟨?_,hN⟩
  intro x hx
  by_cases hs : x ∈ S
  · exact hW.frontier_subset (hWS.symm ▸ hs)
  · exact interior_subset (hN ⟨hx,hs⟩)



theorem OriginalDiskProduct.terminal_disk_subset_marked_side
    {X α : Type*} [TopologicalSpace X]
    {e : α → OpenPartialHomeomorph X (Fin 3 → ℝ)} {E W S Z : Set X}
    {j₀ : V2 → X} (P : OriginalDiskProduct e (E ∩ W) j₀)
    (hW : IsClosed W) (hWS : frontier W = S)
    {A U C : Set P2} {a b : P2} {f : P2 → X} {j : V2 → X}
    (hcenter : P.map '' (Disk ×ˢ {(0 : ℝ)}) = f '' A)
    (hA : IsFinitePLBallPair P2 A (U ∪ C))
    (hU : IsFinitePLBallPair ℝ U {a,b}) (hUC : U ∩ C = {a,b})
    (hfi : InjOn f A) (hAS : f '' A ∩ S = f '' C)
    (hj : ContinuousOn j Disk) (hji : InjOn j Disk)
    (hjE : j '' Disk ⊆ frontier E)
    (hjr : j '' Rim = f '' U ∪ Z) (hjS : j '' Disk ∩ S = Z) :
    j '' Disk ⊆ frontier E ∩ W ∧
      j '' Disk \ S ⊆ interior W ∧
      f '' A ∪ j '' Disk ⊆ (E ∪ frontier E) ∩ W := by
  have hAEW : f '' A ⊆ E ∩ W := by
    rw [←hcenter]
    rintro _ ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
    have ht0 : t = 0 := ht
    subst t
    exact P.inside ⟨hz,by norm_num⟩
  obtain ⟨hjW,hjiW⟩ := terminal_disk_subset_original_bigon_side hW hWS hA hU hUC
    hfi hAS (hAEW.trans inter_subset_right) hj hji hjr hjS
  refine ⟨subset_inter hjE hjW,hjiW,?_⟩
  intro x hx
  rcases hx with hx | hx
  · exact ⟨Or.inl (hAEW hx).1,(hAEW hx).2⟩
  · exact ⟨Or.inr (hjE hx),hjW hx⟩

open PLAnnularStrip Dehn.Annuli.BoundaryUnionDisk
local notation "Ann" => squareAnnulus 8 1
local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.exists_original_terminal_disk_union_in_marked_side
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (p : P2 → LatticeHandleAmbient ι κ L)
    (hp : PolyhedralPLInCharts e p Ann) (hpi : InjOn p Ann)
    (hfront : p '' Ann ⊆ frontier D)
    (hfull : frontier D ∩ interior (latticeHandleDomain ι κ L) ⊆ p '' Ann)
    (hint : p '' {z | -1 < depth 8 z ∧ depth 8 z < 1} ⊆
      interior (latticeHandleDomain ι κ L))
    (hends : ∀ z : Ann, p z ∈ frontier (latticeHandleDomain ι κ L) ↔
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1)
    {n : ℕ} (P : Polygon P2 (n+3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P)
    (hdepth : ∀ x ∈ P.boundary ℝ, -1 < depth 8 x ∧ depth 8 x < 1)
        (hencl : Dehn.annulusSquare 8 1 ⊆ P.inside)
    {S : Set (LatticeHandleAmbient ι κ L)} (s : ChartwisePLSphere e S)
    {A U C : Set P2} {f : P2 → LatticeHandleAmbient ι κ L}
    {u0 u1 c d : P2} (hA : IsFinitePLBallPair P2 A (U ∪ C))
    (hU : IsFinitePLBallPair ℝ U {u0,u1}) (hC : IsFinitePLBallPair ℝ C {u0,u1})
    (hUC : U ∩ C = {u0,u1}) (hu : u0 ≠ u1)
    (hf : PolyhedralPLInCharts e f A) (hfi : InjOn f A)
    (hS : f '' A ∩ S = f '' C)
    (hF : f '' A ∩ frontier (closure (latticeHandleDomain ι κ L \ D)) = f '' U)
    (hPS : p '' P.boundary ℝ ⊆ S)
    (hc : c ∈ P.boundary ℝ) (hd : d ∈ P.boundary ℝ) (hcd : c ≠ d)
    (h0 : f u0 = p c) (h1 : f u1 = p d)
    (hinter : f '' U ∩ p '' P.boundary ℝ = {f u0,f u1})
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (m : ℕ) (ns : Fin m → ℕ) (Ps : ∀ i, Polygon P2 (ns i+3)) (k : Fin m)
    (hPk : (Ps k).boundary ℝ = P.boundary ℝ)
    (hcontacts : p '' (⋃ i, (Ps i).boundary ℝ) = S ∩ frontier D)
    (hPs : ∀ i, Function.Injective (Ps i) ∧ (Ps i).HasSimplicialEdges)
    (hdisjoint : Pairwise (fun i j => Disjoint ((Ps i).boundary ℝ) ((Ps j).boundary ℝ)))
    (hstrict : ∀ i x, x ∈ (Ps i).boundary ℝ →
      -1 < depth 8 x ∧ depth 8 x < 1)
    (henclosing : ∀ i, Dehn.annulusSquare 8 1 ⊆ (Ps i).inside)
    {W₀ : Set (LatticeHandleAmbient ι κ L)} (hW₀ : IsClosed W₀)
    (hW₀S : frontier W₀ = S)
    {j₀ : (Fin 2 → ℝ) → LatticeHandleAmbient ι κ L}
    (Q : OriginalDiskProduct e (closure (latticeHandleDomain ι κ L \ D) ∩ W₀) j₀)
    (hcenter : Q.map '' (closedBall 0 1 ×ˢ {(0 : ℝ)}) = f '' A) :
    let E := closure (latticeHandleDomain ι κ L \ D)
    ∃ V W : Set P2, IsFinitePLBallPair ℝ V {c,d} ∧ IsFinitePLBallPair ℝ W {c,d} ∧
      V ∪ W = P.boundary ℝ ∧ V ∩ W = {c,d} ∧
      ∃ Z : Set P2, (Z = V ∨ Z = W) ∧
      ∃ j : (Fin 2 → ℝ) → LatticeHandleAmbient ι κ L,
        PolyhedralPLInCharts e j (closedBall 0 1) ∧ InjOn j (closedBall 0 1) ∧
        j '' closedBall 0 1 ⊆ frontier E ∧
        j '' sphere 0 1 = f '' U ∪ p '' Z ∧
        j '' closedBall 0 1 ∩ S = p '' Z ∧
        f '' A ∩ j '' closedBall 0 1 = f '' U ∧
        ∃ g : P2 → LatticeHandleAmbient ι κ L,
          PolyhedralPLInCharts e g whole ∧ InjOn g whole ∧
          g '' whole = f '' A ∪ j '' closedBall 0 1 ∧
          g '' frontier whole = f '' C ∪ p '' Z ∧
          g '' whole ⊆ E ∧ g '' whole ∩ S = g '' frontier whole ∧
          g '' whole ∩ frontier E = j '' closedBall 0 1 ∧
          j '' closedBall 0 1 ⊆ frontier E ∩ W₀ ∧
          j '' closedBall 0 1 \ S ⊆ interior W₀ ∧
          g '' whole ⊆ E ∩ W₀ := by
  intro E
  have hAE : f '' A ⊆ E := by
    rw [←hcenter]
    rintro _ ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
    have ht0 : t = 0 := ht
    subst t
    exact (Q.inside ⟨hz,by norm_num⟩).1
  obtain ⟨V,W,hV,hW,hVW,hVWint,Z,hZchoice,j,hj,hji,hjF,hjr,hjS,hAj,
      g,hg,hgi,hgimage,hgrim,hgE,hgS,hgF⟩ :=
    b.exists_original_terminal_disk_union he hdim hi p hp hpi hfront hfull hint
      hends P hP hPi hdepth hencl s hA hU hC hUC hu hf hfi hS hF hPS
      hc hd hcd h0 h1 hinter hSR m ns Ps k hPk hcontacts hPs hdisjoint
      hstrict henclosing hAE
  obtain ⟨hjW,hjiW,hunion⟩ := Q.terminal_disk_subset_marked_side hW₀ hW₀S
    hcenter hA hU hUC hfi hS hj.continuousOn hji hjF hjr hjS
  refine ⟨V,W,hV,hW,hVW,hVWint,Z,hZchoice,j,hj,hji,hjF,hjr,hjS,hAj,
    g,hg,hgi,hgimage,hgrim,hgE,hgS,hgF,hjW,hjiW,?_⟩
  exact subset_inter hgE (hgimage.subset.trans (hunion.trans inter_subset_right))

end PoincareConjecture.M76

