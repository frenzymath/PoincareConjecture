import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerSourceEnd
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerSourceConnected
import Mathlib.Topology.EMetricSpace.Paracompact











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76



instance hamiltonLowerAmbientT2 (ι κ : Type*) [Finite κ] :
    T2Space (LatticeHandleAmbient ι κ (hamiltonLowerPeriodLattice κ)) := by
  let : Fintype κ := Fintype.ofFinite κ
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  exact ((Homeomorph.refl (ι → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv κ)).isEmbedding.t2Space



instance hamiltonLowerOpenParacompact (ι κ : Type*) [Finite ι] [Finite κ]
    (U : TopologicalSpace.Opens
      (LatticeHandleAmbient ι κ (hamiltonLowerPeriodLattice κ))) :
    ParacompactSpace U := by
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  let q := (Homeomorph.refl (ι → ℝ)).prodCongr (hamiltonLowerLatticePiEquiv κ)
  exact (q.image (U : Set _)).isClosedEmbedding.paracompactSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]

local notation "V" => ((ι → ℝ) × (κ → ℝ))
local notation "W" => LatticeHandleAmbient ι κ (hamiltonLowerPeriodLattice κ)
local notation "V3" => (Fin 3 → ℝ)







theorem HamiltonLowerLatticeImmersion.exists_original_marked_wall_core
    (I : HamiltonLowerLatticeImmersion κ)
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (h : OpenPartialHomeomorph V V3)
    (hsource : closedBall (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ)) ⊆ h.source)
    {N : Set V} (hN : IsOpen N)
    (hboundary : sphere (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ)) ⊆ N)
    (hPL : LocallyPiecewiseAffineOn h (h.source ∩ N))
    (wall : ∀ (U : TopologicalSpace.Opens W)
      (charts : Set (OpenPartialHomeomorph U V3)),
      HasWallCompactCore (fun c : charts => (c : OpenPartialHomeomorph U V3))) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 1 < b ∧
      ∃ U : TopologicalSpace.Opens W,
        (U : Set W) =
          (ball (0 : ι → ℝ) b ×ˢ {hamiltonLowerLatticePuncture κ}ᶜ) ∪
            ({x : ι → ℝ | a < ‖x‖ ∧ ‖x‖ < b} ×ˢ univ) ∧
        ∃ (hU : Nonempty U)
          (d : V → OpenPartialHomeomorph W V3)
          (charts : Set (OpenPartialHomeomorph U V3))
          (c : OpenPartialHomeomorph U V3) (K S : Set U),
          let e := fun j : charts => (j : OpenPartialHomeomorph U V3)
          let R := (Subtype.val : U → W) ⁻¹'
            latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ)
          StandardLatticeHandleAtlas ι κ (hamiltonLowerPeriodLattice κ) d ∧
          PLDomain e R ∧ c ∈ charts ∧ IsCompact K ∧ K ⊆ R ∧ PLDomain e K ∧
          S ⊆ interior R ∧ Nonempty (ChartwisePLSphere e S) ∧
          Disjoint (frontier R) S ∧ frontier K = frontier R ∪ S ∧
          frontier ((Subtype.val : R → U) ⁻¹' K) = (Subtype.val : R → U) ⁻¹' S ∧
          (Subtype.val : R → U) ⁻¹' frontier R ⊆
            interior ((Subtype.val : R → U) ⁻¹' K) ∧
          (∀ x ∈ closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 2,
            ∃ (z : U) (hzR : z ∈ R), (z : W) = (x.1, QuotientAddGroup.mk x.2) ∧
              z ∈ c.source ∧ c z = h x ∧
                (⟨z, hzR⟩ : R) ∈ interior ((Subtype.val : R → U) ⁻¹' K)) ∧
          (∀ (j : charts) i,
            (((d i).subtypeRestr hU).restr
              {z : U | a < ‖(z : W).1‖ ∧ ‖(z : W).1‖ < b}).symm.trans (e j) ∈
                piecewiseAffineGroupoid V3) ∧
          ∃ c0 : OpenPartialHomeomorph W V3,
            (∀ x : ι → ℝ, (x, hamiltonLowerLatticePuncture κ) ∈ c0.source) ∧
            latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ) \
                ((Subtype.val : U → W) '' ((Subtype.val : R → U) ''
                  interior ((Subtype.val : R → U) ⁻¹' K))) ⊆ c0.source := by
  classical
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  let : DiscreteTopology (hamiltonLowerPeriodLattice κ) := inferInstance
  let T := ((κ → ℝ) ⧸ (hamiltonLowerPeriodLattice κ).toAddSubgroup)
  let : CompactSpace T := (hamiltonLowerLatticePiEquiv κ).symm.compactSpace
  have hquotient : IsLocalHomeomorph (QuotientAddGroup.mk : (κ → ℝ) → T) :=
    ((hamiltonLowerPeriodLattice κ).toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap.isLocalHomeomorph
  obtain ⟨q0, hq0, hqval⟩ := hquotient (fun _ : κ => (256 : ℝ))
  let linear : V ≃ᴬ[ℝ] V3 :=
    (LinearEquiv.ofFinrankEq _ _ (by
      simpa only [Module.finrank_prod, Module.finrank_pi, Module.finrank_self,
        Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
        Fintype.card_fin] using hdim)).toContinuousLinearEquiv.toContinuousAffineEquiv
  let c0 := ((OpenPartialHomeomorph.refl (ι → ℝ)).prod q0.symm).transHomeomorph
    linear.toHomeomorph
  have hc0 (x : ι → ℝ) : (x, hamiltonLowerLatticePuncture κ) ∈ c0.source := by
    change x ∈ univ ∧ hamiltonLowerLatticePuncture κ ∈ q0.target
    refine ⟨mem_univ _, ?_⟩
    have hval : q0 (fun _ : κ => (256 : ℝ)) = hamiltonLowerLatticePuncture κ :=
      congrFun hqval.symm _
    rw [← hval]
    exact q0.map_source hq0
  obtain ⟨a, b, ha, ha1, hb, U, hUeq, hU, d, charts, c, hd, he, hc,
    _, hcore, hcollar⟩ := I.exists_original_PL_domain hdim h hsource hN hboundary hPL
  let R : Set U := (Subtype.val : U → W) ⁻¹'
    latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ)
  let C2 : Set V := closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 2
  have hC2 : IsCompact C2 :=
    (isCompact_closedBall (0 : ι → ℝ) 1).prod (isCompact_closedBall (0 : κ → ℝ) 2)
  let : CompactSpace C2 := isCompact_iff_compactSpace.mp hC2
  have hquot (x : C2) : (x.val.1, QuotientAddGroup.mk x.val.2) ∈ (U : Set W) := by
    obtain ⟨z, hz, _, _⟩ := hcore x x.property
    rw [← hz]
    exact z.property
  let q : C2 → U := fun x => ⟨(x.val.1, QuotientAddGroup.mk x.val.2), hquot x⟩
  have hq : Continuous q := by
    apply Topology.IsEmbedding.subtypeVal.continuous_iff.mpr
    change Continuous (fun x : C2 => (x.val.1, QuotientAddGroup.mk x.val.2))
    exact continuous_subtype_val.fst.prodMk
      (QuotientAddGroup.continuous_mk.comp continuous_subtype_val.snd)
  let A : Set U := range q
  have hA : IsCompact A := isCompact_range hq
  have hAR : A ⊆ R := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x.property.1, mem_univ _⟩
  let A0W : Set W := latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ) ∩ c0.sourceᶜ
  have hA0W : IsCompact A0W :=
    ((isCompact_closedBall (0 : ι → ℝ) 1).prod isCompact_univ).inter_right
      c0.open_source.isClosed_compl
  have hA0U : A0W ⊆ (U : Set W) := by
    intro x hx
    have hxp : x.2 ≠ hamiltonLowerLatticePuncture κ := by
      intro hxp
      apply hx.2
      change (x.1, x.2) ∈ c0.source
      rw [hxp]
      exact hc0 x.1
    rw [hUeq]
    exact Or.inl ⟨closedBall_subset_ball hb hx.1.1, hxp⟩
  let A0 : Set U := (Subtype.val : U → W) ⁻¹' A0W
  have hA0 : IsCompact A0 :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hA0W
      (fun x hx => ⟨⟨x, hA0U hx⟩, rfl⟩)
  have hA0R : A0 ⊆ R := fun _ hx => hx.1
  have hconn : IsConnected R := lower_original_domain_isConnected hb U hUeq
  obtain ⟨hend, hfront⟩ := lower_original_domain_hasOneSimplyConnectedEnd
    hdim ha.le ha1 hb U hUeq
  obtain ⟨K, S, hK, hKR, heK, hSint, hS, hdis, hfrontK, hretain, hrelative⟩ :=
    wall U charts R he hconn hfront hend (A ∪ A0) (hA.union hA0) (union_subset hAR hA0R)
  refine ⟨a, b, ha, ha1, hb, U, hUeq, hU, d, charts, c, K, S,
    hd, he, hc, hK, hKR, heK, hSint, hS, hdis, hfrontK, hrelative,
    fun _ hz => hretain (Or.inr hz), ?_, hcollar, c0, hc0, ?_⟩
  · intro x hx
    obtain ⟨z, hz, hzc, hzh⟩ := hcore x hx
    have hzR : z ∈ R := by
      change (z : W) ∈ latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ)
      rw [hz]
      exact ⟨hx.1, mem_univ _⟩
    refine ⟨z, hzR, hz, hzc, hzh, hretain (Or.inl (Or.inl ?_))⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hz.symm⟩
  · intro x hx
    by_contra hxc
    have hxA0 : x ∈ A0W := ⟨hx.1, hxc⟩
    let z : U := ⟨x, hA0U hxA0⟩
    have hzR : z ∈ R := hA0R hxA0
    have hzK : (⟨z, hzR⟩ : R) ∈ interior ((Subtype.val : R → U) ⁻¹' K) :=
      hretain (Or.inl (Or.inr hxA0))
    exact hx.2 ⟨z, ⟨⟨z, hzR⟩, hzK, rfl⟩, rfl⟩

end PoincareConjecture.M76
