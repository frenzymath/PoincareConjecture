import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalDiskOneSideAttachment
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalMarkedDiskGluing
import Mathlib.Tactic.ClearExcept

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

set_option maxHeartbeats 1200000 in
theorem parent_model_of_two_cap_models
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) (a : Bool → X) (ha : ∀ b, a b ∈ P.capDisk b)
    (hdis : Disjoint (connectedComponentIn P.cutCarrier (a false))
      (connectedComponentIn P.cutCarrier (a true)))
    (ret T : Bool → Set X)
    (hretc : ∀ b, IsCompact (ret b)) (hretconn : ∀ b, IsConnected (ret b))
    (hretstrip : ∀ b, ret b ∩ P.closedStrip = P.capRimSet b)
    (hretout : ∀ b, (ret b \ P.capDisk b).Nonempty)
    (hTc : ∀ b, IsClosed (T b))
    (hNT : ∀ b, Disjoint (ret b ∪ P.capDisk b) (T b))
    (hDf : ∀ b, frontier (connectedComponentIn P.cutCarrier (a b)) =
      (ret b ∪ P.capDisk b) ∪ T b)
    (f : X → E) (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ connectedComponentIn R (a false), f x ∈ K.space ∧ g (f x) = x)
    (hm : ∀ b, HasPuncturedSphereModel e f (connectedComponentIn P.cutCarrier (a b))) :
    HasPuncturedSphereModel e f (connectedComponentIn R (a false)) := by
  classical
  let D := fun b => connectedComponentIn P.cutCarrier (a b)
  let C := connectedComponentIn R (a false)
  let N := fun b => ret b ∪ P.capDisk b
  let band := P.map '' (Rim ×ˢ J)
  let U := D false ∪ P.closedStrip
  obtain ⟨hQ, _, _, hattach, _, _⟩ := P.cut_geometry hR hopen
  have hcapQ (b : Bool) : P.capDisk b ⊆ P.cutCarrier := by
    intro x hx
    apply (hattach.symm.subset ?_).2
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact Or.inl hx
    · exact Or.inr hx
  have hDc (b : Bool) : IsCompact (D b) :=
    isCompact_connectedComponentIn_of_mem hQ (hcapQ b (ha b))
  have hSc : IsCompact P.closedStrip := P.isCompact_closed_strip (by norm_num : (1/2 : ℝ) ≤ 1)
  have hrec : C = (D false ∪ D true) ∪ P.closedStrip :=
    (P.component_reconstruction hR hopen hPL (ha false) (ha true)).1
  have hUC : U ⊆ C := by
    rw [hrec]
    exact union_subset (subset_union_of_subset_left subset_union_left _) subset_union_right
  have hDC (b : Bool) : D b ⊆ C := by
    rw [hrec]
    cases b
    · exact subset_union_of_subset_left subset_union_left _
    · exact subset_union_of_subset_left subset_union_right _
  have hSC : P.closedStrip ⊆ C := subset_union_right.trans hUC
  have hfi : InjOn f C := by
    intro x hx y hy hxy
    exact (hreal x hx).2.symm.trans ((congrArg g hxy).trans (hreal y hy).2)
  have hf := (hm false).1
  have hpair (b : Bool) := P.finitePL_cap_pair_in_realization f hf (hfi.mono hSC) b
  have hside (b : Bool) := P.one_side_disk_port_geometry hR he hopen hPL a ha hdis b
  have hcapS (b : Bool) : P.capDisk b ⊆ P.closedStrip := by
    apply subset_trans _ P.endDisks_subset_closedStrip
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hrim (b : Bool) : (P.capRimSet b).Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_sphere (by simp) (0 : V2) zero_le_one).nonempty
    exact ⟨P.map (z, if b then (1/2 : ℝ) else -(1/2)),
      (z, if b then (1/2 : ℝ) else -(1/2)), ⟨hz, rfl⟩, rfl⟩
  have hrimret (b : Bool) : P.capRimSet b ⊆ ret b :=
    fun _ hx => ((hretstrip b).symm.subset hx).1
  have hrimband (b : Bool) : P.capRimSet b ⊆ band := by
    intro x hx
    have hc := (P.capDisk_inter_frontier b).symm.subset hx
    exact P.closedStrip_inter_frontier.subset ⟨hcapS b hc.1, hc.2⟩
  have hbandfull : Rim ×ˢ J ⊆ closedBall (0 : V2) 1 ×ˢ Icc (-1 : ℝ) 1 := by
    rintro z ⟨hz, ht⟩
    exact ⟨sphere_subset_closedBall hz, by constructor <;> linarith [ht.1, ht.2]⟩
  have hbandc : IsCompact band :=
    ((isCompact_sphere (0 : V2) 1).prod isCompact_Icc).image_of_continuousOn
      (P.polyhedral.continuousOn.mono hbandfull)
  have hbandconn : IsConnected band :=
    ((isConnected_sphere (by simp) (0 : V2) zero_le_one).prod
      (isConnected_Icc (by norm_num : -(1/2 : ℝ) ≤ 1/2))).image _
      (P.polyhedral.continuousOn.mono hbandfull)
  have hNc (b : Bool) : IsClosed (N b) :=
    ((hretc b).union (P.isCompact_capDisk b)).isClosed
  have hNconn (b : Bool) : IsConnected (N b) := by
    apply (hretconn b).union _ (P.isConnected_capDisk b)
    obtain ⟨x, hx⟩ := hrim b
    exact ⟨x, hrimret b hx, P.capRimSet_subset_capDisk b hx⟩
  have hTsub (b : Bool) : T b ⊆ D b :=
    (subset_union_right.trans (hDf b).symm.subset).trans (hDc b).isClosed.frontier_subset
  have hTcap (b : Bool) : Disjoint (T b) (P.capDisk b) :=
    (hNT b).symm.mono_right subset_union_right
  have hTout (b : Bool) : Disjoint (T b) P.closedStrip := by
    apply disjoint_left.mpr
    intro x hxT hxS
    exact disjoint_left.mp (hTcap b) hxT ((hside b).1.subset ⟨hTsub b hxT, hxS⟩)
  have hSconn : IsConnected (frontier P.closedStrip) := by
    obtain ⟨ball⟩ := P.exists_closedStrip_ball
    rw [ball.frontier_eq, ← ball.image_sphere]
    exact (isConnected_sphere (by simp) (0 : V3) zero_le_one).image _
      (ball.piecewiseAffine.continuousOn.mono sphere_subset_closedBall)
  have hcapSf (b : Bool) : P.capDisk b ⊆ frontier P.closedStrip := by
    rw [P.frontier_closedStrip, P.endDisks_eq_capDisks]
    cases b
    · exact subset_union_of_subset_right subset_union_left _
    · exact subset_union_of_subset_right subset_union_right _
  have hmS := P.closedStrip_hasPuncturedSphereModel f hf (hfi.mono hSC)
  have hfirstfront : frontier U =
      ((N false \ (P.capDisk false \ P.capRimSet false)) ∪
        (frontier P.closedStrip \ (P.capDisk false \ P.capRimSet false))) ∪ T false := by
    rw [(hside false).2, hDf false, union_sdiff_distrib,
      sdiff_eq_left.mpr ((hTcap false).mono_right sdiff_subset)]
    ext x
    simp only [mem_union]
    tauto
  have hfirst : HasPuncturedSphereModel e f U := by
    let Rs := fun b : Bool => if b then P.closedStrip else D false
    let Bs := fun b : Bool => if b then frontier P.closedStrip else N false
    let Ts := fun b : Bool => if b then ∅ else T false
    apply HasPuncturedSphereModel.of_original_disk_attachment Rs
      (by intro b; cases b; exact hDc false; exact hSc)
      (by intro b; cases b; exact hm false; exact hmS) K g hg hgi
      (by simpa only [Rs, Bool.false_eq_true, if_false, if_true] using
        fun x (hx : x ∈ U) => hreal x (hUC hx))
      Bs Ts
      (by intro b; cases b; exact hNconn false; exact hSconn)
      (by intro b; cases b; exact hNc false; exact isClosed_frontier)
      (by intro b; cases b; exact hTc false; exact isClosed_empty)
      (by intro b; cases b; exact hNT false; exact disjoint_empty _)
      (by intro b; cases b; exact hDf false; simp [Rs, Bs, Ts])
      (P.capRimSet_subset_capDisk false) (hpair false) (hside false).1
      (by intro b; cases b; exact subset_union_right; exact hcapSf false)
      (by
        intro b
        cases b
        · obtain ⟨x, hx, hxc⟩ := hretout false
          exact ⟨x, Or.inl hx, hxc⟩
        · obtain ⟨x, hx⟩ := (P.isConnected_capDisk true).nonempty
          exact ⟨x, hcapSf true hx, fun hc => disjoint_left.mp (P.disjoint_capDisks false) hc hx⟩)
    simpa [Rs, Bs, Ts] using hfirstfront
  let Bnew := (ret false ∪ band) ∪ P.capDisk true
  have hBnewEq : Bnew =
      (N false \ (P.capDisk false \ P.capRimSet false)) ∪
        (frontier P.closedStrip \ (P.capDisk false \ P.capRimSet false)) := by
    rw [P.frontier_closedStrip, P.endDisks_eq_capDisks]
    ext x
    have hr : x ∈ ret false → x ∈ P.capDisk false → x ∈ P.capRimSet false :=
      fun hr hc => (hretstrip false).subset ⟨hr, hcapS false hc⟩
    have hb : x ∈ band → x ∈ P.capDisk false → x ∈ P.capRimSet false :=
      fun hb hc => (P.capDisk_inter_frontier false).subset
        ⟨hc, (P.closedStrip_inter_frontier.symm.subset hb).2⟩
    have hqr : x ∈ P.capRimSet false → x ∈ ret false := fun hx => hrimret false hx
    have hd : x ∈ P.capDisk true → x ∉ P.capDisk false :=
      fun ht hf => disjoint_left.mp (P.disjoint_capDisks false) hf ht
    change (x ∈ ret false ∪ band ∪ P.capDisk true) ↔ _
    simp only [N, mem_union, mem_sdiff] at hr hb hqr hd ⊢
    clear * - hr hb hqr hd
    tauto
  have hBnewc : IsClosed Bnew :=
    (((hretc false).union hbandc).union (P.isCompact_capDisk true)).isClosed
  have hBnewconn : IsConnected Bnew := by
    have hfirstconn : IsConnected (ret false ∪ band) := by
      apply (hretconn false).union _ hbandconn
      obtain ⟨x, hx⟩ := hrim false
      exact ⟨x, hrimret false hx, hrimband false hx⟩
    apply hfirstconn.union _ (P.isConnected_capDisk true)
    obtain ⟨x, hx⟩ := hrim true
    exact ⟨x, Or.inr (hrimband true hx), P.capRimSet_subset_capDisk true hx⟩
  have hBnewT : Disjoint Bnew (T false) := by
    rw [hBnewEq]
    exact ((hNT false).mono_left sdiff_subset).union_left
      ((hTout false).symm.mono_left (sdiff_subset.trans hSc.isClosed.frontier_subset))
  have hUf : frontier U = Bnew ∪ T false := hfirstfront.trans (congrArg (· ∪ T false) hBnewEq.symm)
  have hUunion : U ∪ D true = C := by
    rw [hrec]
    dsimp only [U]
    ext x
    simp only [mem_union]
    tauto
  have hsecondfront : frontier (U ∪ D true) =
      ((Bnew \ (P.capDisk true \ P.capRimSet true)) ∪
        (N true \ (P.capDisk true \ P.capRimSet true))) ∪ (T false ∪ T true) := by
    rw [hUunion, P.second_side_disk_port_frontier hR he hopen hPL a ha hdis false]
    change (frontier U \ _) ∪ (frontier (D true) \ _) = _
    rw [hUf, hDf true]
    ext x
    have ht0 : x ∈ T false → x ∉ P.capDisk true :=
      fun ht hc => disjoint_left.mp (hTout false) ht (hcapS true hc)
    have ht1 : x ∈ T true → x ∉ P.capDisk true :=
      fun ht hc => disjoint_left.mp (hTcap true) ht hc
    simp only [Bool.not_false, N, mem_union, mem_sdiff]
    clear * - ht0 ht1
    tauto
  have hsecond : HasPuncturedSphereModel e f (U ∪ D true) := by
    let Rs := fun b : Bool => if b then D true else U
    let Bs := fun b : Bool => if b then N true else Bnew
    let Ts := fun b : Bool => if b then T true else T false
    apply HasPuncturedSphereModel.of_original_disk_attachment Rs
      (by intro b; cases b; exact (hDc false).union hSc; exact hDc true)
      (by intro b; cases b; exact hfirst; exact hm true) K g hg hgi
      (by simpa only [Rs, Bool.false_eq_true, if_false, if_true, hUunion] using hreal)
      Bs Ts
      (by intro b; cases b; exact hBnewconn; exact hNconn true)
      (by intro b; cases b; exact hBnewc; exact hNc true)
      (by intro b; cases b; exact hTc false; exact hTc true)
      (by intro b; cases b; exact hBnewT; exact hNT true)
      (by intro b; cases b; exact hUf; exact hDf true)
      (P.capRimSet_subset_capDisk true) (hpair true)
      (P.one_side_attachment_frontier hR hopen hPL a ha hdis false).1
      (by intro b; cases b; exact subset_union_right; exact subset_union_right)
      (by
        intro b
        cases b
        · obtain ⟨x, hx, hxc⟩ := hretout false
          refine ⟨x, Or.inl (Or.inl hx), ?_⟩
          intro hct
          exact hxc (P.capRimSet_subset_capDisk false
            ((hretstrip false).subset ⟨hx, hcapS true hct⟩))
        · obtain ⟨x, hx, hxc⟩ := hretout true
          exact ⟨x, Or.inl hx, hxc⟩)
    simpa only [Rs, Bs, Ts, Bool.false_eq_true, if_false, if_true] using hsecondfront
  change HasPuncturedSphereModel e f C
  exact hUunion ▸ hsecond

end PoincareConjecture.M76.OriginalDiskProduct
