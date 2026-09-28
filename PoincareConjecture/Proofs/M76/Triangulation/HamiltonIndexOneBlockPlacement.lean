import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneMiddleBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLClosedExtension
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalTransport










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "W" => (ℝ × (ℝ × ℝ))

private theorem middle_shell_geometry :
    squareMiddleBlock ∩ squareShell = squareInnerAnnulus ∧
      squareMiddleBlock ∪ squareShell = squareBlock := by
  constructor
  · ext x
    simp only [squareMiddleBlock, squareShell, squareInnerAnnulus, mem_inter_iff,
      mem_prod, mem_preimage, mem_Icc, mem_closedBall_zero_iff, mem_sphere_zero_iff_norm]
    constructor
    · rintro ⟨⟨hs, hn⟩, ⟨_, hlo, _⟩⟩
      exact ⟨hs, le_antisymm hn hlo⟩
    · rintro ⟨hs, hn⟩
      exact ⟨⟨hs, hn.le⟩, ⟨hs, hn.ge, by linarith⟩⟩
  · ext x
    simp only [squareMiddleBlock, squareShell, squareBlock, mem_union,
      mem_prod, mem_preimage, mem_Icc, mem_closedBall_zero_iff]
    constructor
    · rintro (⟨hs, hn⟩ | ⟨hs, _, hn⟩)
      · exact ⟨hs, by linarith⟩
      · exact ⟨hs, hn⟩
    · rintro ⟨hs, hn⟩
      by_cases h : ‖x.2‖ ≤ (3 / 2 : ℝ)
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr ⟨hs, (lt_of_not_ge h).le, hn⟩

private theorem block_frontier_partition :
    frontier squareBlock ⊆ squareAttachingDisks ∪ squareOuterAnnulus := by
  intro x hx
  by_cases hn : (3 / 2 : ℝ) ≤ ‖x.2‖
  · exact Or.inr ⟨hx, hn⟩
  have hL : IsClosed squareBlock := isClosed_Icc.prod isClosed_closedBall
  have hxL := hL.frontier_subset hx
  have hs : x.1 = -1 ∨ x.1 = 1 := by
    by_contra h
    push Not at h
    apply hx.2
    rw [squareBlock, interior_prod_eq, interior_Icc,
      interior_closedBall _ (by norm_num)]
    exact ⟨⟨lt_of_le_of_ne hxL.1.1 (Ne.symm h.1),
      lt_of_le_of_ne hxL.1.2 h.2⟩, mem_ball_zero_iff.mpr (by linarith)⟩
  exact Or.inl ⟨by simpa only [mem_insert_iff, mem_singleton_iff] using hs,
    mem_closedBall_zero_iff.mpr (lt_of_not_ge hn).le⟩

private theorem protected_ball_complement_geometry {B T : Set W}
    (hB : IsFinitePLBallPair W B (T ∪ squareAttachingDisks))
    (hBL : B ⊆ squareBlock) (hT : IsClosed T)
    (hcontact : B ∩ frontier squareBlock = squareAttachingDisks)
    (hrims : T ∩ frontier squareBlock = squareRims) :
    B ∩ complementaryRegion B = T ∧ B ∪ complementaryRegion B = squareBlock := by
  have hBc := hB.isCompact.isClosed
  have hreg := hB.closure_interior_of_finrank_eq rfl
  have hfront := hB.frontier_eq_of_finrank_eq rfl
  obtain ⟨_, _, hEf⟩ := complementaryRegion_geometry hBc hreg hBL hT hfront hcontact hrims
  have hL : IsClosed squareBlock := isClosed_Icc.prod isClosed_closedBall
  have hEL : complementaryRegion B ⊆ squareBlock :=
    closure_minimal (fun _ hx => interior_subset hx.1) hL
  have hEB : complementaryRegion B ⊆ (interior B)ᶜ :=
    closure_minimal (fun _ hx hy => hx.2 (interior_subset hy)) isOpen_interior.isClosed_compl
  have hiEB : interior (complementaryRegion B) ⊆ Bᶜ := by
    have h := interior_mono hEB
    rwa [interior_compl, hreg] at h
  constructor
  · ext x
    constructor
    · intro hx
      have hxf : x ∈ frontier (complementaryRegion B) :=
        ⟨subset_closure hx.2, fun hi => hiEB hi hx.1⟩
      rcases hEf.subset hxf with hxT | hxO
      · exact hxT
      · have hc := hcontact.subset ⟨hx.1, hxO.1⟩
        have hn : ‖x.2‖ = (3 / 2 : ℝ) :=
          le_antisymm (mem_closedBall_zero_iff.mp hc.2) hxO.2
        exact (hrims.symm.subset ⟨hc.1, mem_sphere_zero_iff_norm.mpr hn⟩).1
    · intro hx
      exact ⟨hB.1 (Or.inl hx), isClosed_closure.frontier_subset (hEf.symm.subset (Or.inl hx))⟩
  · apply Subset.antisymm (union_subset hBL hEL)
    intro x hx
    by_cases hxB : x ∈ B
    · exact Or.inl hxB
    · right
      have hregular : closure (interior squareBlock) = squareBlock := by
        rw [squareBlock, interior_prod_eq, interior_Icc,
          interior_closedBall _ (by norm_num), closure_prod_eq,
          closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1), closure_ball _ (by norm_num)]
      have h := hBc.isOpen_compl.inter_closure ⟨hxB, hregular.symm.subset hx⟩
      exact closure_mono
        (show Bᶜ ∩ interior squareBlock ⊆ interior squareBlock \ B from
          fun _ hy => ⟨hy.2, hy.1⟩) h




theorem exists_supported_block_placement_of_marked_shell {B T : Set W}
    (hB : IsFinitePLBallPair W B (T ∪ squareAttachingDisks))
    (hBL : B ⊆ squareBlock) (hT : IsClosed T)
    (hcontact : B ∩ frontier squareBlock = squareAttachingDisks)
    (hrims : T ∩ frontier squareBlock = squareRims)
    (tau : squareInnerAnnulus ≃ₜ T) (htau : tau.IsFinitePL)
    (hfix : ∀ x : squareInnerAnnulus, (x : W) ∈ squareRims → (tau x : W) = x)
    (H : squareShell ≃ₜ complementaryRegion B) (hH : H.IsFinitePL)
    (hHinner : ∀ (x : squareInnerAnnulus) (hx : (x : W) ∈ squareShell),
      (H ⟨x, hx⟩ : W) = tau x)
    (hHouter : ∀ (x : squareOuterAnnulus) (hx : (x : W) ∈ squareShell),
      (H ⟨x, hx⟩ : W) = x) :
    ∃ Q : W ≃ₜ W, FinitePiecewiseAffineOn Q squareBlock ∧
      Q '' squareMiddleBlock = B ∧ EqOn Q id (interior squareBlock)ᶜ := by
  obtain ⟨hMS, hcoverS⟩ := middle_shell_geometry
  obtain ⟨hBE, hcoverT⟩ := protected_ball_complement_geometry hB hBL hT hcontact hrims
  obtain ⟨phi, hphi, hphiInner, hphiCaps, hphiT⟩ :=
    exists_marked_middle_ball hB tau htau hrims hfix
  have hover (x : squareMiddleBlock) : (x : W) ∈ squareShell ↔
      (phi x : W) ∈ complementaryRegion B := by
    have hs : (x : W) ∈ squareShell ↔ (x : W) ∈ squareInnerAnnulus := by
      rw [← hMS]
      exact (and_iff_right x.property).symm
    have ht : (phi x : W) ∈ T ↔ (phi x : W) ∈ complementaryRegion B := by
      rw [← hBE]
      exact and_iff_right (phi x).property
    exact hs.trans ((hphiT x).trans ht)
  have hagree (x : W) (hxM : x ∈ squareMiddleBlock) (hxS : x ∈ squareShell) :
      (phi ⟨x, hxM⟩ : W) = H ⟨x, hxS⟩ := by
    have hxI := hMS.subset ⟨hxM, hxS⟩
    exact (hphiInner ⟨x, hxI⟩ hxM).trans (hHinner ⟨x, hxI⟩ hxS).symm
  obtain ⟨G, hG, hGM, hGS⟩ := Homeomorph.exists_union_finitePL phi H hphi hH hover hagree
  let F : squareBlock ≃ₜ squareBlock :=
    (Homeomorph.setCongr hcoverS.symm).trans (G.trans (Homeomorph.setCongr hcoverT))
  have hF : F.IsFinitePL := hG.setCongr hcoverS hcoverT
  have hFM (x : squareMiddleBlock) :
      (F ⟨x, hcoverS.subset (Or.inl x.property)⟩ : W) = phi x := hGM x
  have hFS (x : squareShell) :
      (F ⟨x, hcoverS.subset (Or.inr x.property)⟩ : W) = H x := hGS x
  have hFfix (x : squareBlock) (hx : (x : W) ∈ frontier squareBlock) : F x = x := by
    apply Subtype.ext
    rcases block_frontier_partition hx with hxC | hxO
    · have hs : x.val.1 ∈ Icc (-1 : ℝ) 1 := x.property.1
      have hxM : (x : W) ∈ squareMiddleBlock := ⟨hs, hxC.2⟩
      exact (hFM ⟨x, hxM⟩).trans (hphiCaps ⟨x, hxC⟩ hxM)
    · have hxf : (x : W) ∈ frontier squareShell := squareShell_frontier.symm.subset (Or.inr hxO)
      have hxS : (x : W) ∈ squareShell :=
        (isClosed_Icc.prod (isClosed_Icc.preimage continuous_norm)).frontier_subset hxf
      exact (hFS ⟨x, hxS⟩).trans (hHouter ⟨x, hxO⟩ hxS)
  have hL : IsClosed squareBlock := isClosed_Icc.prod isClosed_closedBall
  let Q := F.closedExtension hL hFfix
  have hQM (x : squareMiddleBlock) : Q x = (phi x : W) :=
    (F.closedExtension_apply_mem hL hFfix (hcoverS.subset (Or.inl x.property))).trans (hFM x)
  refine ⟨Q, ?_, ?_, fun _ hx => F.closedExtension_apply_notMem_interior hL hFfix hx⟩
  · obtain ⟨f, hf, hFf⟩ := hF
    exact hf.congr fun x hx => (hFf ⟨x, hx⟩).symm.trans
      (F.closedExtension_apply_mem hL hFfix hx).symm
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hQM ⟨x, hx⟩]
      exact (phi ⟨x, hx⟩).property
    · intro y hy
      let x := phi.symm ⟨y, hy⟩
      exact ⟨x, x.property, (hQM x).trans (congrArg Subtype.val (phi.apply_symm_apply ⟨y, hy⟩))⟩

end PoincareConjecture.M76.HamiltonIndexOne
