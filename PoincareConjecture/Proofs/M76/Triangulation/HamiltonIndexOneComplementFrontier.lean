import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneShellDiskCover
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (ℝ × ℝ)
local notation "W" => (ℝ × V2)


def squareBlock : Set W := Icc (-1) 1 ×ˢ closedBall 0 2


def squareAttachingDisks : Set W := ({-1, 1} : Set ℝ) ×ˢ closedBall 0 (3 / 2)


def squareRims : Set W := ({-1, 1} : Set ℝ) ×ˢ sphere 0 (3 / 2)


def squareOuterAnnulus : Set W :=
  {x | x ∈ frontier squareBlock ∧ (3 / 2 : ℝ) ≤ ‖x.2‖}




def complementaryRegion (B : Set W) : Set W := closure (interior squareBlock \ B)

private theorem squareBlock_interior :
    interior squareBlock = Ioo (-1) 1 ×ˢ ball (0 : V2) 2 := by
  rw [squareBlock, interior_prod_eq, interior_Icc, interior_closedBall _ (by norm_num)]

private theorem squareBlock_closed : IsClosed squareBlock :=
  isClosed_Icc.prod isClosed_closedBall

private theorem squareBlock_regular : closure (interior squareBlock) = squareBlock := by
  rw [squareBlock_interior, closure_prod_eq, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1),
    closure_ball _ (by norm_num)]
  rfl

private theorem squareBlock_convex : Convex ℝ squareBlock :=
  (convex_Icc (-1 : ℝ) 1).prod (convex_closedBall (0 : V2) 2)

private theorem attaching_subset_frontier : squareAttachingDisks ⊆ frontier squareBlock := by
  intro x hx
  have hs : x.1 = -1 ∨ x.1 = 1 := by simpa only [squareAttachingDisks,
    mem_prod, mem_insert_iff, mem_singleton_iff] using hx.1
  have hv : ‖x.2‖ ≤ (3 / 2 : ℝ) := mem_closedBall_zero_iff.mp hx.2
  refine ⟨subset_closure ⟨?_, mem_closedBall_zero_iff.mpr (by linarith)⟩, ?_⟩
  · rcases hs with hs | hs <;> rw [hs] <;> norm_num
  · intro hi
    rw [squareBlock_interior] at hi
    rcases hs with hs | hs
    · exact (lt_irrefl (-1 : ℝ)) (hs ▸ hi.1.1)
    · exact (lt_irrefl (1 : ℝ)) (hs ▸ hi.1.2)

private theorem closure_difference_contact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L B T : Set E} (hL : Convex ℝ L) (hBL : B ⊆ L)
    (hBreg : closure (interior B) = B) (hT : IsClosed T)
    (hfront : frontier B ⊆ T ∪ frontier L) :
    closure (interior L \ B) ∩ B ⊆ T := by
  intro x hx
  by_contra hxT
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hT.isOpen_compl x hxT
  let U := interior L ∩ ball x r
  have hconn : IsPreconnected U := (hL.interior.inter (convex_ball x r)).isPreconnected
  have havoid : Disjoint (frontier (interior B)) U := by
    apply Set.disjoint_left.mpr
    intro y hy hyU
    rcases hfront (frontier_interior_subset hy) with hyT | hyL
    · exact hball hyU.2 hyT
    · exact hyL.2 hyU.1
  have hxB : x ∈ closure (interior B) := hBreg.symm ▸ hx.2
  obtain ⟨y, hyr, hyB⟩ := mem_closure_iff.mp hxB (ball x r) isOpen_ball (mem_ball_self hr)
  have hinside : U ⊆ interior B := hconn.m76_subset_of_disjoint_frontier isOpen_interior
    havoid ⟨y, ⟨interior_mono hBL hyB, hyr⟩, hyB⟩
  obtain ⟨z, hzr, hz⟩ := mem_closure_iff.mp hx.1 (ball x r) isOpen_ball (mem_ball_self hr)
  exact hz.2 (interior_subset (hinside ⟨hz.1, hzr⟩))

private theorem outside_subset_complementary {B : Set W} (hB : IsClosed B) :
    squareBlock \ B ⊆ complementaryRegion B := by
  intro x hx
  have hxcl : x ∈ closure (interior squareBlock) := squareBlock_regular.symm ▸ hx.1
  have hx' : x ∈ closure (Bᶜ ∩ interior squareBlock) :=
    hB.isOpen_compl.inter_closure ⟨hx.2, hxcl⟩
  have hsub : Bᶜ ∩ interior squareBlock ⊆ interior squareBlock \ B :=
    fun _ hy => ⟨hy.2, hy.1⟩
  exact closure_mono hsub hx'

private theorem rims_subset_complementary {B : Set W} (hB : IsClosed B)
    (hcontact : B ∩ frontier squareBlock = squareAttachingDisks) :
    squareRims ⊆ complementaryRegion B := by
  intro x hx
  have hs : x.1 = -1 ∨ x.1 = 1 := by simpa only [squareRims,
    mem_prod, mem_insert_iff, mem_singleton_iff] using hx.1
  have hv : ‖x.2‖ = (3 / 2 : ℝ) := mem_sphere_zero_iff_norm.mp hx.2
  let f : ℝ → W := fun t => (x.1, (t / (3 / 2 : ℝ)) • x.2)
  have hf : Continuous f := continuous_const.prodMk
    ((continuous_id.div_const _).smul continuous_const)
  have hnorm (t : ℝ) (ht : 0 ≤ t) : ‖(f t).2‖ = t := by
    change ‖(t / (3 / 2 : ℝ)) • x.2‖ = t
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ht (by norm_num)), hv]
    ring
  have hmaps : MapsTo f (Ioc (3 / 2 : ℝ) 2) (complementaryRegion B) := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hyL : f t ∈ squareBlock := by
      refine ⟨?_, mem_closedBall_zero_iff.mpr ?_⟩
      · rcases hs with hs | hs <;> change -1 ≤ x.1 ∧ x.1 ≤ 1 <;> rw [hs] <;> norm_num
      · rw [hnorm t ht0]
        exact ht.2
    have hyfront : f t ∈ frontier squareBlock := by
      refine ⟨subset_closure hyL, ?_⟩
      intro hi
      rw [squareBlock_interior] at hi
      rcases hs with hs | hs
      · exact (lt_irrefl (-1 : ℝ)) (hs ▸ hi.1.1)
      · exact (lt_irrefl (1 : ℝ)) (hs ▸ hi.1.2)
    have hyB : f t ∉ B := by
      intro hy
      have hc : f t ∈ squareAttachingDisks := hcontact ▸ ⟨hy, hyfront⟩
      have hb := mem_closedBall_zero_iff.mp hc.2
      rw [hnorm t ht0] at hb
      exact (not_lt_of_ge hb) ht.1
    exact outside_subset_complementary hB ⟨hyL, hyB⟩
  have hbase : (3 / 2 : ℝ) ∈ closure (Ioc (3 / 2 : ℝ) 2) := by
    rw [closure_Ioc (by norm_num : (3 / 2 : ℝ) ≠ 2)]
    constructor <;> norm_num
  have hlim := hf.continuousWithinAt.mem_closure hbase hmaps
  rw [(show IsClosed (complementaryRegion B) from isClosed_closure).closure_eq] at hlim
  simpa only [f, div_self (by norm_num : (3 / 2 : ℝ) ≠ 0), one_smul, Prod.mk.eta] using hlim






theorem complementaryRegion_geometry {B T : Set W}
    (hB : IsClosed B) (hBreg : closure (interior B) = B) (hBL : B ⊆ squareBlock)
    (hT : IsClosed T) (hfront : frontier B = T ∪ squareAttachingDisks)
    (hcontact : B ∩ frontier squareBlock = squareAttachingDisks)
    (hrims : T ∩ frontier squareBlock = squareRims) :
    IsCompact (complementaryRegion B) ∧
      closure (interior (complementaryRegion B)) = complementaryRegion B ∧
      frontier (complementaryRegion B) = T ∪ squareOuterAnnulus := by
  have hEL : complementaryRegion B ⊆ squareBlock :=
    closure_minimal (fun _ hx => interior_subset hx.1) squareBlock_closed
  have hEB : complementaryRegion B ∩ B ⊆ T :=
    closure_difference_contact squareBlock_convex hBL hBreg hT (by
      rw [hfront]
      exact union_subset subset_union_left (attaching_subset_frontier.trans subset_union_right))
  have hEout : complementaryRegion B ⊆ (interior B)ᶜ :=
    closure_minimal (fun _ hx hy => hx.2 (interior_subset hy)) isOpen_interior.isClosed_compl
  have hiEout : interior (complementaryRegion B) ⊆ Bᶜ := by
    have h := interior_mono hEout
    rwa [interior_compl, hBreg] at h
  have hTB : T ⊆ B := fun x hx => hB.frontier_subset (hfront.symm ▸ Or.inl hx)
  have hTE : T ⊆ complementaryRegion B := by
    intro x hx
    by_cases hxi : x ∈ interior squareBlock
    · have hxf : x ∈ frontier B := hfront.symm ▸ Or.inl hx
      have hxcl : x ∈ closure Bᶜ := by rw [closure_compl]; exact hxf.2
      exact isOpen_interior.inter_closure ⟨hxi, hxcl⟩
    · have hxf : x ∈ frontier squareBlock := ⟨subset_closure (hBL (hTB hx)), hxi⟩
      exact rims_subset_complementary hB hcontact (hrims ▸ ⟨hx, hxf⟩)
  have hreg : closure (interior (complementaryRegion B)) = complementaryRegion B := by
    apply Subset.antisymm isClosed_closure.closure_interior_subset
    exact closure_mono ((isOpen_interior.sdiff hB).subset_interior_closure)
  refine ⟨(isCompact_Icc.prod (isCompact_closedBall (0 : V2) 2)).of_isClosed_subset
    isClosed_closure hEL, hreg, ?_⟩
  apply Subset.antisymm
  · intro x hx
    have hxE : x ∈ complementaryRegion B := isClosed_closure.frontier_subset hx
    by_cases hxB : x ∈ B
    · exact Or.inl (hEB ⟨hxE, hxB⟩)
    · right
      have hxf : x ∈ frontier squareBlock := by
        refine ⟨subset_closure (hEL hxE), ?_⟩
        intro hi
        have hio : x ∈ interior (complementaryRegion B) :=
          (isOpen_interior.sdiff hB).subset_interior_closure ⟨hi, hxB⟩
        exact hx.2 hio
      refine ⟨hxf, ?_⟩
      by_contra hn
      have hv : ‖x.2‖ ≤ (3 / 2 : ℝ) := (lt_of_not_ge hn).le
      have hxL := hEL hxE
      have hs : x.1 = -1 ∨ x.1 = 1 := by
        by_contra h
        push Not at h
        apply hxf.2
        rw [squareBlock_interior]
        exact ⟨⟨lt_of_le_of_ne hxL.1.1 (Ne.symm h.1),
          lt_of_le_of_ne hxL.1.2 h.2⟩, mem_ball_zero_iff.mpr (by linarith)⟩
      have hc : x ∈ squareAttachingDisks :=
        ⟨by simpa only [mem_insert_iff, mem_singleton_iff] using hs,
          mem_closedBall_zero_iff.mpr hv⟩
      exact hxB ((hcontact.symm ▸ hc).1)
  · rintro x (hxT | hxO)
    · exact ⟨subset_closure (hTE hxT), fun hi => hiEout hi (hTB hxT)⟩
    · have hxE : x ∈ complementaryRegion B := by
        by_cases hxB : x ∈ B
        · have hc : x ∈ squareAttachingDisks := hcontact ▸ ⟨hxB, hxO.1⟩
          have hv : ‖x.2‖ = (3 / 2 : ℝ) :=
            le_antisymm (mem_closedBall_zero_iff.mp hc.2) hxO.2
          exact rims_subset_complementary hB hcontact
            ⟨hc.1, mem_sphere_zero_iff_norm.mpr hv⟩
        · exact outside_subset_complementary hB
            ⟨squareBlock_closed.frontier_subset hxO.1, hxB⟩
      exact ⟨subset_closure hxE, fun hi => hxO.1.2 (interior_mono hEL hi)⟩

end PoincareConjecture.M76.HamiltonIndexOne
