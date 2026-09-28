import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcNormalizedGraph
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcLiftedRegion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcRegionPullback

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "CY" => sphere (0 : Fin 2 → ℝ) 1

theorem ChartwisePLSphere.exists_selected_terminal_end_region_with_core_avoidance
    {X α κ : Type*} [MetricSpace X] [Fintype κ]
    {e : α → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] (hk : Fintype.card κ = 2)
    {A qA W : Set P2} {f : P2 → X}
    (hA : IsFinitePLBallPair P2 A qA)
    (hf : ContinuousOn f A) (hfi : InjOn f A)
    (hWA : W ⊆ A) (hW : IsConnected W)
    (hcontact : f '' A ∩ S = f '' W)
    (q : C(X,(κ → ℝ) ⧸ L.toAddSubgroup))
    {End Z B : Set X} (hEnd : IsCompact End)
    (F : C(End,(κ → ℝ) ⧸ L.toAddSubgroup)) (hFi : Function.Injective F)
    (hFhom : F.Homotopic (q.comp ⟨Subtype.val,continuous_subtype_val⟩))
    (hFrange : range F = ((QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
      ball 0 (3/4))ᶜ)
    (hZE : Z ⊆ End) (hZS : Z ⊆ S ∪ f '' A)
    (H : (CY × unitInterval) ≃ₜ B) (hBE : B ⊆ End)
    (hcore : ∀ y, (H (y,1) : X) ∈ Z)
    (v : C(CY,κ → ℝ)) (hvn : ∀ y, ‖v y‖ = (3/2 : ℝ))
    (hFB : ∀ z, F ⟨H z,hBE (H z).property⟩ =
      QuotientAddGroup.mk ((1 - (z.2 : ℝ)/2) • v z.1))
    (gamma delta : C(CY,Z))
    (hgamma : Function.Injective gamma) (hdelta : Function.Injective delta)
    {W' C0 C1 : Set Z} (hg : range gamma = W' ∪ C0) (hd : range delta = W' ∪ C1)
    (hC0 : C0 ⊆ range (fun y => (⟨H (y,1),hcore y⟩ : Z)))
    (hC1 : C1 ⊆ range (fun y => (⟨H (y,1),hcore y⟩ : Z)))
    (hne0 : C0.Nonempty) (hne1 : C1.Nonempty)
    (hdiff : range gamma ≠ range delta) :
    ∃ O : Set End, IsOpen O ∧ IsCompact (closure O) ∧ IsSimplyConnected O ∧
      (frontier O = range (fun y => (⟨gamma y,hZE (gamma y).property⟩ : End)) ∨
       frontier O = range (fun y => (⟨delta y,hZE (delta y).property⟩ : End))) ∧
      Disjoint O (range (fun y => (⟨H (y,1),hBE (H (y,1)).property⟩ : End))) := by
  let : CompactSpace End := isCompact_iff_compactSpace.mp hEnd
  obtain ⟨J,hJi,hJ,hJcore,hJnorm⟩ := s.exists_normalized_terminal_graph_lift L
    hA hf hfi hWA hW hcontact q F hFi hFhom hZE hZS H hBE hcore v hvn hFB
  let inc : C(Z,End) := ⟨Set.inclusion hZE,continuous_inclusion _⟩
  let FZ := F.comp inc
  have hFZi : Function.Injective FZ := hFi.comp (Set.inclusion_injective hZE)
  have hnorm0 (z : Z) (hz : z ∈ C0) : ‖J z‖ = (3/4 : ℝ) := by
    obtain ⟨y,rfl⟩ := hC0 hz
    exact hJnorm y
  have hnorm1 (z : Z) (hz : z ∈ C1) : ‖J z‖ = (3/4 : ℝ) := by
    obtain ⟨y,rfl⟩ := hC1 hz
    exact hJnorm y
  have havoid (z : Z) : FZ z ∉
      (QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) '' ball 0 (3/4) :=
    hFrange.subset (mem_range_self (inc z))
  obtain ⟨U,hU,hK,hsc,hfront,hdis⟩ := exists_selected_region_of_normalized_graph
    hk L FZ hFZi J hJi hJ gamma delta hgamma hdelta hg hd hnorm0 hnorm1 hne0 hne1 hdiff havoid
  have hsub : closure U ⊆ range F := by
    rw [hFrange]
    exact fun x hx => disjoint_left.mp hdis hx
  obtain ⟨O,ho,hko,hsco,himage,hcl,hfo,_⟩ :=
    exists_region_pullback_of_compact_embedding F hFi hU hsc hsub
  refine ⟨O,ho,hko,hsco,?_,?_⟩
  · have hr (g : C(CY,Z)) : F '' range (fun y => (⟨g y,hZE (g y).property⟩ : End)) =
        range (FZ.comp g) := by
      rw [←Set.range_comp]
      rfl
    rcases hfront with hh | hh
    · exact Or.inl (Set.image_injective.mpr hFi (hfo.trans (hh.trans (hr gamma).symm)))
    · exact Or.inr (Set.image_injective.mpr hFi (hfo.trans (hh.trans (hr delta).symm)))

  · have hclavoid : closure
        ((QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) '' ball 0 (3/4)) ⊆ Uᶜ :=
      closure_minimal (fun x hx hu => disjoint_left.mp hdis (subset_closure hu) hx) hU.isClosed_compl
    apply disjoint_left.mpr
    rintro z hz ⟨y,rfl⟩
    have hval := hFB (y,1)
    norm_num at hval
    have hin : F ⟨H (y,1),hBE (H (y,1)).property⟩ ∈ U :=
      himage.subset (mem_image_of_mem F hz)
    rw [hval] at hin
    apply hclavoid ?_ hin
    apply mem_closure_image QuotientAddGroup.continuous_mk.continuousAt
    rw [closure_ball _ (by norm_num : (3/4 : ℝ) ≠ 0),mem_closedBall_zero_iff,
      norm_smul,Real.norm_eq_abs,hvn]
    norm_num

theorem ChartwisePLSphere.exists_selected_terminal_end_region
    {X α κ : Type*} [MetricSpace X] [Fintype κ]
    {e : α → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] (hk : Fintype.card κ = 2)
    {A qA W : Set P2} {f : P2 → X}
    (hA : IsFinitePLBallPair P2 A qA)
    (hf : ContinuousOn f A) (hfi : InjOn f A)
    (hWA : W ⊆ A) (hW : IsConnected W)
    (hcontact : f '' A ∩ S = f '' W)
    (q : C(X,(κ → ℝ) ⧸ L.toAddSubgroup))
    {End Z B : Set X} (hEnd : IsCompact End)
    (F : C(End,(κ → ℝ) ⧸ L.toAddSubgroup)) (hFi : Function.Injective F)
    (hFhom : F.Homotopic (q.comp ⟨Subtype.val,continuous_subtype_val⟩))
    (hFrange : range F = ((QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
      ball 0 (3/4))ᶜ)
    (hZE : Z ⊆ End) (hZS : Z ⊆ S ∪ f '' A)
    (H : (CY × unitInterval) ≃ₜ B) (hBE : B ⊆ End)
    (hcore : ∀ y, (H (y,1) : X) ∈ Z)
    (v : C(CY,κ → ℝ)) (hvn : ∀ y, ‖v y‖ = (3/2 : ℝ))
    (hFB : ∀ z, F ⟨H z,hBE (H z).property⟩ =
      QuotientAddGroup.mk ((1 - (z.2 : ℝ)/2) • v z.1))
    (gamma delta : C(CY,Z))
    (hgamma : Function.Injective gamma) (hdelta : Function.Injective delta)
    {W' C0 C1 : Set Z} (hg : range gamma = W' ∪ C0) (hd : range delta = W' ∪ C1)
    (hC0 : C0 ⊆ range (fun y => (⟨H (y,1),hcore y⟩ : Z)))
    (hC1 : C1 ⊆ range (fun y => (⟨H (y,1),hcore y⟩ : Z)))
    (hne0 : C0.Nonempty) (hne1 : C1.Nonempty)
    (hdiff : range gamma ≠ range delta) :
    ∃ O : Set End, IsOpen O ∧ IsCompact (closure O) ∧ IsSimplyConnected O ∧
      (frontier O = range (fun y => (⟨gamma y,hZE (gamma y).property⟩ : End)) ∨
       frontier O = range (fun y => (⟨delta y,hZE (delta y).property⟩ : End))) := by
  obtain ⟨O,ho,hko,hsco,hfront,_⟩ :=
    s.exists_selected_terminal_end_region_with_core_avoidance L hk hA hf hfi hWA hW hcontact
      q hEnd F hFi hFhom hFrange hZE hZS H hBE hcore v hvn hFB gamma delta hgamma hdelta
      hg hd hC0 hC1 hne0 hne1 hdiff
  exact ⟨O,ho,hko,hsco,hfront⟩

end PoincareConjecture.M76
