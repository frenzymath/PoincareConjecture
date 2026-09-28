import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerCoreChart
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonOriginalSourceCollar
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonOriginalAtlasGluing
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardBoundaryAtlas
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

private theorem PLDomain.open_subtype
    {X ι : Type*} [TopologicalSpace X]
    {d : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (hd : PLDomain d R) (U : TopologicalSpace.Opens X) (hU : Nonempty U) :
    PLDomain (fun i => (d i).subtypeRestr hU) ((Subtype.val : U → X) ⁻¹' R) := by
  have hcompat (c e : OpenPartialHomeomorph X V3)
      (hce : c.symm.trans e ∈ piecewiseAffineGroupoid V3) :
      (c.subtypeRestr hU).symm.trans (e.subtypeRestr hU) ∈ piecewiseAffineGroupoid V3 := by
    apply (piecewiseAffineGroupoid V3).mem_of_eqOnSource
      (closedUnderRestriction' hce (c.isOpen_inter_preimage_symm U.isOpen))
    exact OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr hU c e
  refine ⟨?_, fun i j => hcompat _ _ (hd.compatible i j),
    hd.closed.preimage continuous_subtype_val, ?_⟩
  · intro x
    obtain ⟨i, hi⟩ := hd.cover x
    exact ⟨i, by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hi⟩
  · intro x hx
    have hxR : (x : X) ∈ frontier R := by
      have hopen : IsOpenMap (Subtype.val : U → X) := U.isOpen.isOpenMap_subtype_val
      have heq := hopen.preimage_frontier_eq_frontier_preimage
        (continuous_subtype_val : Continuous (Subtype.val : U → X)) R
      exact heq.symm.subset hx
    obtain ⟨ell, v, B, hv, hxB, hzero, hB, hhalf⟩ := hd.halfspace x hxR
    refine ⟨ell, v, B.subtypeRestr hU, hv, ?_, hzero,
      fun i => hcompat _ _ (hB i), ?_⟩
    · simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxB
    · intro y hy
      rw [OpenPartialHomeomorph.subtypeRestr_source] at hy
      exact hhalf y hy

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "V" => ((ι → ℝ) × (κ → ℝ))
local notation "W" => LatticeHandleAmbient ι κ (hamiltonLowerPeriodLattice κ)

theorem HamiltonLowerLatticeImmersion.exists_original_PL_domain
    (I : HamiltonLowerLatticeImmersion κ)
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (h : OpenPartialHomeomorph V V3)
    (hsource : closedBall (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ)) ⊆ h.source)
    {N : Set V} (hN : IsOpen N)
    (hboundary : sphere (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N)) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 1 < b ∧
      ∃ U : TopologicalSpace.Opens W,
        (U : Set W) =
          (ball (0 : ι → ℝ) b ×ˢ {hamiltonLowerLatticePuncture κ}ᶜ) ∪
            ({x : ι → ℝ | a < ‖x‖ ∧ ‖x‖ < b} ×ˢ univ) ∧
        ∃ (hU : Nonempty U)
          (d : V → OpenPartialHomeomorph W V3)
          (charts : Set (OpenPartialHomeomorph U V3))
          (c : OpenPartialHomeomorph U V3),
          StandardLatticeHandleAtlas ι κ (hamiltonLowerPeriodLattice κ) d ∧
          PLDomain (fun e : charts => (e : OpenPartialHomeomorph U V3))
            ((Subtype.val : U → W) ⁻¹' latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ)) ∧
          c ∈ charts ∧ EqOn c (fun z : U => h ((z : W).1, I.map (z : W).2)) c.source ∧
          (∀ x ∈ closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 2,
            ∃ z : U, (z : W) = (x.1, QuotientAddGroup.mk x.2) ∧
              z ∈ c.source ∧ c z = h x) ∧
          ∀ (e : charts) i,
            (((d i).subtypeRestr hU).restr
              {z : U | a < ‖(z : W).1‖ ∧ ‖(z : W).1‖ < b}).symm.trans
              (e : OpenPartialHomeomorph U V3) ∈ piecewiseAffineGroupoid V3 := by
  classical
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  let : T2Space ((κ → ℝ) ⧸ (hamiltonLowerPeriodLattice κ).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv κ).isEmbedding.t2Space
  obtain ⟨a, b, ha, ha1, hb, hbig, hband⟩ := exists_original_source_uniform_collar
    I.compact h.open_source hN
    (fun x hx => hsource ⟨hx.1, mem_univ _⟩)
    (fun x hx => hboundary ⟨hx.1, mem_univ _⟩)
  let A : Set W := ball (0 : ι → ℝ) b ×ˢ {hamiltonLowerLatticePuncture κ}ᶜ
  let B : Set W := {x : ι → ℝ | a < ‖x‖ ∧ ‖x‖ < b} ×ˢ univ
  have hA : IsOpen A := isOpen_ball.prod isClosed_singleton.isOpen_compl
  have hB : IsOpen B :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).prod isOpen_univ
  let U : TopologicalSpace.Opens W := ⟨A ∪ B, hA.union hB⟩
  have hU : Nonempty U := by
    have hz := (I.core 0 (by norm_num)).1
    refine ⟨⟨(0, QuotientAddGroup.mk (0 : κ → ℝ)), Or.inl ⟨?_, hz⟩⟩⟩
    exact mem_ball_zero_iff.mpr (by simpa using zero_lt_one.trans hb)
  let AU : Set U := (Subtype.val : U → W) ⁻¹' A
  let BU : Set U := (Subtype.val : U → W) ⁻¹' B
  have hAU : IsOpen AU := hA.preimage continuous_subtype_val
  have hBU : IsOpen BU := hB.preimage continuous_subtype_val
  have hcover : AU ∪ BU = univ := by
    ext x
    simp only [mem_union, mem_univ, iff_true]
    exact x.property
  obtain ⟨d, hd⟩ := exists_standard_lattice_handle_atlas ι κ
    (hamiltonLowerPeriodLattice κ) hdim
  let dU : V → OpenPartialHomeomorph U V3 := fun i => (d i).subtypeRestr hU
  let R : Set U := (Subtype.val : U → W) ⁻¹'
    latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ)
  have hdU : PLDomain dU R := hd.domain.open_subtype U hU
  have hboundaryU : frontier R ⊆ BU := by
    intro z hz
    have hopen : IsOpenMap (Subtype.val : U → W) := U.isOpen.isOpenMap_subtype_val
    have heq := hopen.preimage_frontier_eq_frontier_preimage
      (continuous_subtype_val : Continuous (Subtype.val : U → W))
      (latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ))
    have hz' : (z : W) ∈ frontier (latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ)) :=
      heq.symm.subset hz
    have hznorm : ‖(z : W).1‖ = 1 := by
      change (z : W) ∈ frontier (closedBall (0 : ι → ℝ) 1 ×ˢ univ) at hz'
      rw [frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero] at hz'
      simpa only [mem_sphere, dist_zero_right] using hz'.1
    exact ⟨⟨by simpa only [hznorm] using ha1, by simpa only [hznorm] using hb⟩, mem_univ _⟩
  let F : W → V3 := fun z => h (z.1, I.map z.2)
  let FU : U → V3 := fun z => F z
  have hmap : IsLocalHomeomorphOn (fun z : W => (z.1, I.map z.2)) A := by
    apply IsLocalHomeomorphOn.mk
    intro z hz
    obtain ⟨e, hze, he⟩ := I.localHomeomorph z.2 hz.2
    refine ⟨(Homeomorph.refl (ι → ℝ)).toOpenPartialHomeomorph.prod e,
      ⟨mem_univ _, hze⟩, ?_⟩
    intro y _
    change (y.1, I.map y.2) = (y.1, e y.2)
    exact congrArg (Prod.mk y.1) (congrFun he y.2)
  have hF : IsLocalHomeomorphOn F A :=
    (IsLocalHomeomorphOn.OpenPartialHomeomorph.isLocalHomeomorphOn h).comp hmap
      (fun z hz => hbig ⟨hz.1, I.image_subset ⟨z.2, hz.2, rfl⟩⟩)
  have hFU : IsLocalHomeomorphOn FU AU :=
    hF.comp (U.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn.mono
      (subset_univ AU)) (fun _ hx => hx)
  let π : V → W := fun x => (x.1, QuotientAddGroup.mk x.2)
  let g : V → V := fun x => (x.1, I.map (QuotientAddGroup.mk x.2))
  let D : Set V := univ ×ˢ
    (QuotientAddGroup.mk ⁻¹' {hamiltonLowerLatticePuncture κ}ᶜ)
  have hg : LocallyPiecewiseAffineOn g D :=
    (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ (ι → ℝ))
      isOpen_univ).prodMap I.quotientPL
  have hFg := hPL.comp hg
  have hFPL (i : V) : LocallyPiecewiseAffineOn (FU ∘ (dU i).symm)
      ((dU i).target ∩ (dU i).symm ⁻¹' (AU ∩ BU)) := by
    obtain ⟨L, hL⟩ := hd.inverse_formula i
    have hcoord (z : V3) (hz : z ∈ (dU i).target) :
        ((dU i).symm z : W) = π (L z) :=
      ((d i).subtypeRestr_symm_apply hU hz).trans
        (hL z ((d i).subtypeRestr_target_subset hU hz))
    have hcomp := hFg.comp
      (locallyPiecewiseAffineOn_affine L.toContinuousAffineMap isOpen_univ)
    have hsub : (dU i).target ∩ (dU i).symm ⁻¹' (AU ∩ BU) ⊆
        univ ∩ L ⁻¹' (D ∩ g ⁻¹' (h.source ∩ N)) := by
      intro z hz
      have hzA : π (L z) ∈ A := by
        rw [← hcoord z hz.1]
        exact hz.2.1
      have hzB : π (L z) ∈ B := by
        rw [← hcoord z hz.1]
        exact hz.2.2
      have hzK : I.map (QuotientAddGroup.mk (L z).2) ∈ I.compactCarrier :=
        I.image_subset ⟨QuotientAddGroup.mk (L z).2, hzA.2, rfl⟩
      have hzG : g (L z) ∈ {x : ι → ℝ | a < ‖x‖ ∧ ‖x‖ < b} ×ˢ I.compactCarrier :=
        ⟨hzB.1, hzK⟩
      have hzN := hband hzG
      exact ⟨mem_univ _, ⟨mem_univ _, hzA.2⟩, hzN.2, hzN.1⟩
    have hopen := (dU i).continuousOn_invFun.isOpen_inter_preimage
      (dU i).open_target (hAU.inter hBU)
    apply (hcomp.mono hopen hsub).congr
    intro z hz
    change h ((L z).1, I.map (QuotientAddGroup.mk (L z).2)) =
      h ((((dU i).symm z : U) : W).1, I.map (((dU i).symm z : U) : W).2)
    rw [hcoord z hz.1]
  obtain ⟨charts, hcharts, hinsert, _, hcollar⟩ :=
    exists_original_immersion_collar_PL_domain dU hdU hAU hBU hcover
      hboundaryU FU hFU hFPL
  obtain ⟨c0, hc0A, hc0F, hc0core⟩ := I.exists_original_doubled_core_chart h hb hbig
  let c := c0.subtypeRestr hU
  have hcsource (z : U) (hz : z ∈ c.source) : (z : W) ∈ c0.source := by
    simpa only [c, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hz
  have hcA : c.source ⊆ AU := fun z hx => hc0A (hcsource z hx)
  have hcF : EqOn c FU c.source := by
    intro z hz
    change c0 (z : W) = h ((z : W).1, I.map (z : W).2)
    exact hc0F (hcsource z hz)
  refine ⟨a, b, ha, ha1, hb, U, rfl, hU, d, charts, c, hd, hcharts,
    hinsert c hcA hcF, hcF, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxc, hval⟩ := hc0core x hx
    let z : U := ⟨π x, Or.inl (hc0A hxc)⟩
    refine ⟨z, rfl, ?_, ?_⟩
    · simpa only [c, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxc
    · change c0 (π x) = h x
      exact hval
  · intro e i
    have hBUeq : BU = {z : U | a < ‖(z : W).1‖ ∧ ‖(z : W).1‖ < b} := by
      ext z
      simp only [BU, B, mem_preimage, mem_prod, mem_ofPred_eq, mem_univ, and_true]
    rw [← hBUeq]
    exact hcollar e i

end PoincareConjecture.M76
