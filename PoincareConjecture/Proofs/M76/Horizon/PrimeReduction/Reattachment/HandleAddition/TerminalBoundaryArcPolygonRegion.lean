import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcPhysicalRegion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalPolygonArcLoops



set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "CY" => sphere (0 : Fin 2 → ℝ) 1

theorem ChartwisePLSphere.exists_selected_terminal_polygon_region_with_core_avoidance
    {X α κ : Type*} [MetricSpace X] [Fintype κ]
    {e : α → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] (hk : Fintype.card κ = 2)
    {A qA W0 : Set P2} {f : P2 → X}
    (hA : IsFinitePLBallPair P2 A qA)
    (hf : ContinuousOn f A) (hfi : InjOn f A)
    (hWA : W0 ⊆ A) (hW : IsConnected W0) (hcontact : f '' A ∩ S = f '' W0)
    (q : C(X,(κ → ℝ) ⧸ L.toAddSubgroup))
    {End B : Set X} (hEnd : IsCompact End)
    (F : C(End,(κ → ℝ) ⧸ L.toAddSubgroup)) (hFi : Function.Injective F)
    (hFhom : F.Homotopic (q.comp ⟨Subtype.val,continuous_subtype_val⟩))
    (hFrange : range F = ((QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
      ball 0 (3/4))ᶜ)
    (H : (CY × unitInterval) ≃ₜ B) (hBE : B ⊆ End)
    (v : C(CY,κ → ℝ)) (hvn : ∀ y, ‖v y‖ = (3/2 : ℝ))
    (hFB : ∀ z, F ⟨H z,hBE (H z).property⟩ =
      QuotientAddGroup.mk ((1 - (z.2 : ℝ)/2) • v z.1))
    {U : Set P2} {a b c d : P2} (hU : IsFinitePLBallPair ℝ U {a,b})
    (hab : a ≠ b) (hUA : U ⊆ A) (hUE : f '' U ⊆ End)
    {n : ℕ} (P : Polygon P2 (n+3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) (hc : c ∈ P.boundary ℝ) (hd : d ∈ P.boundary ℝ)
    (hcd : c ≠ d) {g : P2 → X}
    (hg : ContinuousOn g (P.boundary ℝ)) (hgi : InjOn g (P.boundary ℝ))
    (h0 : f a = g c) (h1 : f b = g d)
    (hinter : f '' U ∩ g '' P.boundary ℝ = {f a,f b})
    (hPS : g '' P.boundary ℝ ⊆ S)
    (hcore : range (fun y => (H (y,1) : X)) = g '' P.boundary ℝ) :
    ∃ V W : Set P2, IsFinitePLBallPair ℝ V {c,d} ∧ IsFinitePLBallPair ℝ W {c,d} ∧
      V ∪ W = P.boundary ℝ ∧ V ∩ W = {c,d} ∧
      ∃ O : Set End, IsOpen O ∧ IsCompact (closure O) ∧ IsSimplyConnected O ∧
        ((Subtype.val : End → X) '' frontier O = f '' U ∪ g '' V ∨
         (Subtype.val : End → X) '' frontier O = f '' U ∪ g '' W) ∧ Disjoint (Subtype.val '' O) (g '' P.boundary ℝ) := by
  obtain ⟨V,W,hV,hW',hVW,hint,gamma,delta,hgamma,hdelta,hgr,hdr,hinterloops⟩ :=
    exists_terminal_polygon_arc_loops hU hab P hP hPi hc hd hcd
      (hf.mono hUA) hg (hfi.mono hUA) hgi h0 h1 hinter
  have hVP : V ⊆ P.boundary ℝ := subset_union_left.trans hVW.subset
  have hWP : W ⊆ P.boundary ℝ := subset_union_right.trans hVW.subset
  let Z := f '' U ∪ g '' P.boundary ℝ
  have hZE : Z ⊆ End := union_subset hUE (by
    rw [←hcore]
    rintro _ ⟨y,rfl⟩
    exact hBE (H (y,1)).property)
  have hZS : Z ⊆ S ∪ f '' A := union_subset
    ((image_mono hUA).trans subset_union_right) (hPS.trans subset_union_left)
  have hcoreZ (y : CY) : (H (y,1) : X) ∈ Z := Or.inr (hcore.subset (mem_range_self y))
  have hgZ : range gamma ⊆ Z := hgr.subset.trans
    (union_subset_union_right _ (image_mono hVP))
  have hdZ : range delta ⊆ Z := hdr.subset.trans
    (union_subset_union_right _ (image_mono hWP))
  let gamma' : C(CY,Z) := ⟨fun y => ⟨gamma y,hgZ (mem_range_self y)⟩,
    gamma.continuous.subtype_mk _⟩
  let delta' : C(CY,Z) := ⟨fun y => ⟨delta y,hdZ (mem_range_self y)⟩,
    delta.continuous.subtype_mk _⟩
  let W' : Set Z := Subtype.val ⁻¹' (f '' U)
  let C0 : Set Z := Subtype.val ⁻¹' (g '' V)
  let C1 : Set Z := Subtype.val ⁻¹' (g '' W)
  have hgr' : range gamma' = W' ∪ C0 := by
    ext z
    constructor
    · rintro ⟨y,rfl⟩
      exact hgr.subset (mem_range_self y)
    · intro hz
      obtain ⟨y,hy⟩ := hgr.symm.subset hz
      exact ⟨y,Subtype.ext hy⟩
  have hdr' : range delta' = W' ∪ C1 := by
    ext z
    constructor
    · rintro ⟨y,rfl⟩
      exact hdr.subset (mem_range_self y)
    · intro hz
      obtain ⟨y,hy⟩ := hdr.symm.subset hz
      exact ⟨y,Subtype.ext hy⟩
  have hC {T : Set P2} (hTP : T ⊆ P.boundary ℝ) :
      (Subtype.val ⁻¹' (g '' T) : Set Z) ⊆
        range (fun y => (⟨H (y,1),hcoreZ y⟩ : Z)) := by
    intro z hz
    obtain ⟨y,hy⟩ := hcore.symm.subset ((image_mono hTP) hz)
    exact ⟨y,Subtype.ext hy⟩
  have hne0 : C0.Nonempty := ⟨⟨g c,Or.inr (mem_image_of_mem g hc)⟩,
    mem_image_of_mem g (hV.1 (Or.inl rfl))⟩
  have hne1 : C1.Nonempty := ⟨⟨g c,Or.inr (mem_image_of_mem g hc)⟩,
    mem_image_of_mem g (hW'.1 (Or.inl rfl))⟩
  have hdiff : range gamma ≠ range delta := by
    intro hh
    obtain ⟨p,_,hp0,hp1⟩ := hV.exists_unitInterval_chart_with_endpoints hcd
    let m : unitInterval := ⟨1/2,by norm_num,by norm_num⟩
    have hmg : g (p m) ∈ range gamma := hgr.symm.subset (Or.inr (mem_image_of_mem g (p m).property))
    have hmU := hinterloops.subset ⟨hmg,hh ▸ hmg⟩
    have hends := hinter.subset ⟨hmU,mem_image_of_mem g (hVP (p m).property)⟩
    rcases hends with heq | heq
    · have hmc : (p m : P2) = c := hgi (hVP (p m).property) hc (heq.trans h0)
      have hm0 : m = 0 := p.injective (Subtype.ext (hmc.trans hp0.symm))
      have hm := congrArg (fun t : unitInterval => (t : ℝ)) hm0
      norm_num [m] at hm
    · have hmd : (p m : P2) = d := hgi (hVP (p m).property) hd (heq.trans h1)
      have hm1 : m = 1 := p.injective (Subtype.ext (hmd.trans hp1.symm))
      have hm := congrArg (fun t : unitInterval => (t : ℝ)) hm1
      norm_num [m] at hm
  have hdiff' : range gamma' ≠ range delta' := by
    intro hh
    apply hdiff
    have hv := congrArg ((Subtype.val : Z → X) '' ·) hh
    rw [←Set.range_comp,←Set.range_comp] at hv
    exact hv
  obtain ⟨O,ho,hko,hsco,hfo,hdiscore⟩ := s.exists_selected_terminal_end_region_with_core_avoidance L hk
    hA hf hfi hWA hW hcontact q hEnd F hFi hFhom hFrange hZE hZS H hBE hcoreZ v hvn hFB
    gamma' delta' (fun _ _ hh => hgamma (congrArg Subtype.val hh))
    (fun _ _ hh => hdelta (congrArg Subtype.val hh)) hgr' hdr' (hC hVP) (hC hWP)
    hne0 hne1 hdiff'
  refine ⟨V,W,hV,hW',hVW,hint,O,ho,hko,hsco,?_,?_⟩
  · rcases hfo with hh | hh
    · left
      rw [hh,←Set.range_comp]
      exact hgr
    · right
      rw [hh,←Set.range_comp]
      exact hdr

  · apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hzp
    obtain ⟨y,hy⟩ := hcore.symm.subset hzp
    exact disjoint_left.mp hdiscore hz ⟨y,Subtype.ext hy⟩

theorem ChartwisePLSphere.exists_selected_terminal_polygon_region
    {X α κ : Type*} [MetricSpace X] [Fintype κ]
    {e : α → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] (hk : Fintype.card κ = 2)
    {A qA W0 : Set P2} {f : P2 → X}
    (hA : IsFinitePLBallPair P2 A qA)
    (hf : ContinuousOn f A) (hfi : InjOn f A)
    (hWA : W0 ⊆ A) (hW : IsConnected W0) (hcontact : f '' A ∩ S = f '' W0)
    (q : C(X,(κ → ℝ) ⧸ L.toAddSubgroup))
    {End B : Set X} (hEnd : IsCompact End)
    (F : C(End,(κ → ℝ) ⧸ L.toAddSubgroup)) (hFi : Function.Injective F)
    (hFhom : F.Homotopic (q.comp ⟨Subtype.val,continuous_subtype_val⟩))
    (hFrange : range F = ((QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
      ball 0 (3/4))ᶜ)
    (H : (CY × unitInterval) ≃ₜ B) (hBE : B ⊆ End)
    (v : C(CY,κ → ℝ)) (hvn : ∀ y, ‖v y‖ = (3/2 : ℝ))
    (hFB : ∀ z, F ⟨H z,hBE (H z).property⟩ =
      QuotientAddGroup.mk ((1 - (z.2 : ℝ)/2) • v z.1))
    {U : Set P2} {a b c d : P2} (hU : IsFinitePLBallPair ℝ U {a,b})
    (hab : a ≠ b) (hUA : U ⊆ A) (hUE : f '' U ⊆ End)
    {n : ℕ} (P : Polygon P2 (n+3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) (hc : c ∈ P.boundary ℝ) (hd : d ∈ P.boundary ℝ)
    (hcd : c ≠ d) {g : P2 → X}
    (hg : ContinuousOn g (P.boundary ℝ)) (hgi : InjOn g (P.boundary ℝ))
    (h0 : f a = g c) (h1 : f b = g d)
    (hinter : f '' U ∩ g '' P.boundary ℝ = {f a,f b})
    (hPS : g '' P.boundary ℝ ⊆ S)
    (hcore : range (fun y => (H (y,1) : X)) = g '' P.boundary ℝ) :
    ∃ V W : Set P2, IsFinitePLBallPair ℝ V {c,d} ∧ IsFinitePLBallPair ℝ W {c,d} ∧
      V ∪ W = P.boundary ℝ ∧ V ∩ W = {c,d} ∧
      ∃ O : Set End, IsOpen O ∧ IsCompact (closure O) ∧ IsSimplyConnected O ∧
        ((Subtype.val : End → X) '' frontier O = f '' U ∪ g '' V ∨
         (Subtype.val : End → X) '' frontier O = f '' U ∪ g '' W) := by
  obtain ⟨V,W,hV,hW',hVW,hint,O,ho,hko,hsco,hfront,_⟩ :=
    s.exists_selected_terminal_polygon_region_with_core_avoidance L hk hA hf hfi hWA hW hcontact
      q hEnd F hFi hFhom hFrange H hBE v hvn hFB hU hab hUA hUE P hP hPi hc hd hcd
      hg hgi h0 h1 hinter hPS hcore
  exact ⟨V,W,hV,hW',hVW,hint,O,ho,hko,hsco,hfront⟩

end PoincareConjecture.M76
