import PoincareConjecture.Proofs.M38.SmoothCoverLift
import Mathlib.Topology.Connected.LocallyConnected










set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38


theorem closure_componentIn_inter_subset
    {A : Type*} [TopologicalSpace A] {V : Set A} {a : A} (ha : a ∈ V) :
    closure (connectedComponentIn V a) ∩ V ⊆ connectedComponentIn V a := by
  intro x hx
  have he := Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image
    (connectedComponent (⟨a, ha⟩ : V))
  rw [isClosed_connectedComponent.closure_eq, ← connectedComponentIn_eq_image ha] at he
  have hsub : (⟨x, hx.2⟩ : V) ∈ connectedComponent (⟨a, ha⟩ : V) := by
    rw [he]
    exact hx.1
  rw [connectedComponentIn_eq_image ha]
  exact ⟨⟨x, hx.2⟩, hsub, rfl⟩



theorem connected_subset_image_precompact_component
    {A Q : Type*} [TopologicalSpace A] [LocallyConnectedSpace A]
    [TopologicalSpace Q] [T2Space Q]
    (q : A → Q) (hq : Continuous q) (ho : IsOpenMap q)
    {U : Set Q} (hU : IsOpen U) {a : A} (ha : q a ∈ U)
    (hcompact : IsCompact (closure (connectedComponentIn (q ⁻¹' U) a)))
    {K : Set Q} (hK : IsPreconnected K) (hKU : K ⊆ U) (hKa : q a ∈ K) :
    K ⊆ q '' connectedComponentIn (q ⁻¹' U) a := by
  let C := connectedComponentIn (q ⁻¹' U) a
  have hCopen : IsOpen C := (hU.preimage hq).connectedComponentIn
  apply hK.subset_of_closure_inter_subset (ho C hCopen)
    ⟨q a, hKa, mem_image_of_mem q (mem_connectedComponentIn ha)⟩
  rintro y ⟨hy, hyK⟩
  have hy' : y ∈ q '' closure C :=
    closure_minimal (image_mono subset_closure) (hcompact.image hq).isClosed hy
  obtain ⟨x, hx, rfl⟩ := hy'
  exact mem_image_of_mem q (closure_componentIn_inter_subset
    (show a ∈ q ⁻¹' U from ha) ⟨hx, hKU hyK⟩)



theorem localDiffeomorph_injective_open_sheet_generic
    {E E' H H' M M' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace M'] [ChartedSpace H' M'] [Nonempty M]
    (q : M → M') (hq : IsLocalDiffeomorph I J ∞ q)
    {C : Set M} (hC : IsOpen C) (hinj : InjOn q C) :
    ∃ e : PartialDiffeomorph I J M M' ∞,
      e.source = C ∧ e.target = q '' C ∧ (e : M → M') = q := by
  classical
  let p := OpenPartialHomeomorph.ofContinuousOpen (hinj.toPartialEquiv q C)
    hq.contMDiff.continuous.continuousOn hq.isLocalHomeomorph.isOpenMap hC
  have hps : ContMDiffOn J I ∞ p.symm p.target := by
    intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    let h := hq (p.symm x)
    have hs := h.localInverse_contMDiffAt
    have hright : q (p.symm x) = x := p.right_inv hx
    rw [hright] at hs
    apply hs.congr_of_eventuallyEq
    filter_upwards [(p.symm.continuousAt hx).preimage_mem_nhds
      (h.localInverse.open_target.mem_nhds h.localInverse_mem_target),
      p.open_target.mem_nhds hx] with y hy hyT
    have hh := h.localInverse_left_inv hy
    rw [show q (p.symm y) = y from p.right_inv hyT] at hh
    exact hh.symm
  exact ⟨{
    toPartialEquiv := p.toPartialEquiv
    open_source := p.open_source
    open_target := p.open_target
    contMDiffOn_toFun := hq.contMDiff.contMDiffOn
    contMDiffOn_invFun := hps }, rfl, rfl, rfl⟩


theorem localDiffeomorph_injective_open_sheet
    {A Q : GeneralizedSliceCarrier} [Nonempty A.carrier]
    (q : A.carrier → Q.carrier) (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    {C : Set A.carrier} (hC : IsOpen C) (hinj : InjOn q C) :
    ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) A.carrier Q.carrier ∞,
      e.source = C ∧ e.target = q '' C ∧ (e : A.carrier → Q.carrier) = q :=
  localDiffeomorph_injective_open_sheet_generic q hq hC hinj

end PoincareConjecture.M38
