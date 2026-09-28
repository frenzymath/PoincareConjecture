import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.SourceAnnularMark
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Groups.FiniteIndexBasepoint
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.FrontierComponents.BoundaryLocalConnectedness
import PoincareConjecture.Proofs.M76.Wall.PLDomainLocalPathConnected
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.ComponentBoundaryGroups
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.SpanningAnnulus.MarkedSlope
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.SpanningAnnulus.Construction










set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.PeriodicSquare

open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "P2" => (ℝ × ℝ)
local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

theorem SourceSquareMap.exists_essential_annulus_in_original_mark
    {E X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E}
    (M : SourceSquareMap p K)
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) (hcompactR : IsCompact R) (hR : IsConnected R)
    {S₀ S₁ : Set X} (hS₀ : S₀ ⊆ frontier R) (hS₁ : S₁ ⊆ frontier R)
    (hdis : Disjoint S₀ S₁)
    (x₀ : S₀) (x₁ : S₁)
    (hcomponent₀ : connectedComponentIn (frontier R) (x₀ : X) = S₀)
    (hcomponent₁ : connectedComponentIn (frontier R) (x₁ : X) = S₁)
    (hinj : ∀ x : S₀, Function.Injective (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)) x))
    (hindex₀ : (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)) x₀).range.FiniteIndex)
    (hindex₁ : (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₁.trans he.closed.frontier_subset)) x₁).range.FiniteIndex)
    (H : K.space ≃ₜ S₀) (F : E → X)
    (hF : PolyhedralPLInCharts e F K.space) (hFval : ∀ x : K.space, F x = (H x : X)) :
    ∃ h : (AddCircle p × AddCircle p) ≃ₜ S₀,
      (∀ z : Square p, h (projection p z) = H (M.map z)) ∧
    ∃ (B : Set X) (hBS : B ⊆ S₀) (A : Ann ≃ₜ B) (j : P2 → X),
      IsCompact B ∧ IsClosed B ∧
      PolyhedralPLInCharts e j Ann ∧ (∀ z : Ann, j z = (A z : X)) ∧
      IsOpen ((Subtype.val : frontier R → X) ⁻¹' originalAnnulusOpenMark A) ∧
      (∀ z : Circle, (A (annulusCoreCircle z) : X) =
        (h (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
          (Fact.out : (0 : ℝ) < p).ne' z, ((p / 2 : ℝ) : AddCircle p)) : X)) ∧
      ∃ retract : C(S₀, Circle), (∀ z, retract (sourceAnnularCore A hBS z) = z) ∧
      let marks : Bool → Set X := fun b => if b then S₁ else originalAnnulusOpenMark A
      let core := sourceAnnularCore A hBS
      let alpha := (AddCircle.periodLoop (4 * (8 : ℝ))).map core.continuous
      ∃ (g : (V1 × V2) → X) (f : C(source, R)),
        PolyhedralPLInCharts e g source ∧ (∀ x : source, g x = (f x : X)) ∧
        (∀ (b : Bool) (u : Q2), g (endpoint b, u) ∈ marks b) ∧
        (∀ b, ¬ (sourceAnnulusRim f b).Nullhomotopic) ∧
        ∃ n : ℕ, 0 < n ∧ ∃ (beta : Path x₁ x₁)
          (gamma gamma₀ : ∀ b, C(Q2, marks b)),
          (∀ (b : Bool) (u : Q2), g (endpoint b, u) = (gamma₀ b u : X)) ∧
          (∀ b, Nonempty ((gamma b).Homotopy (gamma₀ b))) ∧
          (∀ s : unitInterval, (gamma false (squareRimLoop s) : X) =
            (boundaryLoopIterate alpha n s : X)) ∧
          (∀ s : unitInterval, (gamma true (squareRimLoop s) : X) = (beta s : X)) := by
  have hp : 0 < p := Fact.out
  have hopen₀ := he.isOpen_preimage_frontier_component hcompactR
    (hS₀ x₀.property) hcomponent₀
  have hopen₁ := he.isOpen_preimage_frontier_component hcompactR
    (hS₁ x₁.property) hcomponent₁
  obtain ⟨h, B, hBS, A, j, hvalue, hcompact, hclosed, hj, hjval, hmark, hcore,
      ⟨retract, hret⟩, _⟩ :=
    M.exists_original_annular_mark e he.compatible H F hF hFval
      (r := p / 4) (by positivity) (by linarith)
  let : PathConnectedSpace S₀ := h.surjective.pathConnectedSpace h.continuous
  let : ConnectedSpace R := isConnected_iff_connectedSpace.mp hR
  let : LocallyPathConnectedSpace R := he.locallyPathConnectedSpace
  let : PathConnectedSpace R := PathConnectedSpace.of_locallyPathConnectedSpace
  let i₀ : C(S₀, R) := ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)
  let i₁ : C(S₁, R) := ContinuousMap.inclusion (hS₁.trans he.closed.frontier_subset)
  let core := sourceAnnularCore A hBS
  let scale := AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num) hp.ne'
  let retract₀ : C(S₀, Circle) := ⟨fun x => scale.symm (retract x),
    scale.symm.continuous.comp retract.continuous⟩
  have hret₀ (z : Circle) : retract₀ (core z) = z := by
    change scale.symm (retract _) = z
    exact (congrArg scale.symm (hret z)).trans (scale.symm_apply_apply z)
  let alpha := (AddCircle.periodLoop (4 * (8 : ℝ))).map core.continuous
  have hindex : (FundamentalGroup.map i₀ (core 0)).range.FiniteIndex :=
    FundamentalGroup.finiteIndex_range_map_all_basepoints i₀ x₀ hindex₀ (core 0)
  let k := PathConnectedSpace.somePath (i₀ (core 0)) (i₁ x₁)
  have hcomm := boundary_groups_commensurable_of_finiteIndex
    i₀ i₁ (core 0) x₁ hindex hindex₁ k
  have hmarkFrontier : IsOpen ((Subtype.val : frontier R → X) ⁻¹'
      originalAnnulusOpenMark A) := by
    obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hmark
    have heq : (Subtype.val : frontier R → X) ⁻¹' originalAnnulusOpenMark A =
        (Subtype.val : frontier R → X) ⁻¹' S₀ ∩ (Subtype.val : frontier R → X) ⁻¹' U := by
      ext x
      constructor
      · intro hx
        have hxS := hBS (originalAnnulusOpenMark_subset A hx)
        exact ⟨hxS, show (⟨x, hxS⟩ : S₀) ∈ (Subtype.val : S₀ → X) ⁻¹' U by
          rw [hUeq]; exact hx⟩
      · rintro ⟨hxS, hxU⟩
        have : (⟨x, hxS⟩ : S₀) ∈ (Subtype.val : S₀ → X) ⁻¹' U := hxU
        rwa [hUeq] at this
    rw [heq]
    exact hopen₀.inter (hU.preimage continuous_subtype_val)
  let marks : Bool → Set X := fun b => if b then S₁ else originalAnnulusOpenMark A
  have hmarks : ∀ b, marks b ⊆ frontier R := by
    intro b
    cases b
    · exact (originalAnnulusOpenMark_subset A).trans (hBS.trans hS₀)
    · exact hS₁
  have hmarksOpen : ∀ b, IsOpen ((Subtype.val : frontier R → X) ⁻¹' marks b) := by
    intro b
    cases b
    · exact hmarkFrontier
    · exact hopen₁
  have hmarksDis : Disjoint (marks false) (marks true) :=
    hdis.mono_left ((originalAnnulusOpenMark_subset A).trans hBS)
  have ha : orderOf (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk alpha)) = 0 :=
    orderOf_eq_zero_iff.mpr (sourceAnnularCore_periodLoop_not_isOfFinOrder A hBS retract hret)
  obtain ⟨g, f, hg, hgf, hrim, hessential, hn⟩ :=
    exists_essential_marked_PL_annulus_of_commensurable_open_marks he marks hmarks
      hmarksOpen hmarksDis i₀ i₁ (fun x => x.property) (core 0) x₁ k hcomm
      (hinj (core 0)) alpha (fun t => sourceAnnularCore_mem_mark A hBS _) ha
  exact ⟨h, hvalue, B, hBS, A, j, hcompact, hclosed, hj, hjval, hmarkFrontier, hcore,
    retract₀, hret₀, g, f, hg, hgf, hrim, hessential, hn⟩

theorem SourceSquareMap.exists_original_spanning_annulus_in_zero_ambient_of_commensurable
    {E : Type*} {ι : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E}
    (M : SourceSquareMap p K)
    {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    (he : PLDomain e R) (hcompactR : IsCompact R) (hR : IsConnected R)
    {S₀ S₁ : Set X0} (hS₀ : S₀ ⊆ frontier R) (hS₁ : S₁ ⊆ frontier R)
    (hdis : Disjoint S₀ S₁)
    (x₀ : S₀) (x₁ : S₁)
    (hcomponent₀ : connectedComponentIn (frontier R) (x₀ : X0) = S₀)
    (hcomponent₁ : connectedComponentIn (frontier R) (x₁ : X0) = S₁)
    (hinj : ∀ x : S₀, Function.Injective (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)) x))
    (k₀ : Path
      ((ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)) x₀)
      ((ContinuousMap.inclusion (hS₁.trans he.closed.frontier_subset)) x₁))
    (hcomm : (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)) x₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k₀.symm).toMonoidHom.comp
        (FundamentalGroup.map
          (ContinuousMap.inclusion (hS₁.trans he.closed.frontier_subset)) x₁)).range))
    (H : K.space ≃ₜ S₀) (F : E → X0)
    (hF : PolyhedralPLInCharts e F K.space) (hFval : ∀ x : K.space, F x = (H x : X0)) :
    ∃ h : (AddCircle p × AddCircle p) ≃ₜ S₀,
      (∀ z : Square p, h (projection p z) = H (M.map z)) ∧
      ∃ (B : Set X0) (hBS : B ⊆ S₀) (A : Ann ≃ₜ B) (j : P2 → X0),
        IsCompact B ∧ IsClosed B ∧
        PolyhedralPLInCharts e j Ann ∧ (∀ z : Ann, j z = (A z : X0)) ∧
        IsOpen ((Subtype.val : frontier R → X0) ⁻¹' originalAnnulusOpenMark A) ∧
        (∀ z : Circle, (A (annulusCoreCircle z) : X0) =
          (h (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
            (Fact.out : (0 : ℝ) < p).ne' z, ((p / 2 : ℝ) : AddCircle p)) : X0)) ∧
        ∃ retract : C(S₀, Circle), (∀ z, retract (sourceAnnularCore A hBS z) = z) ∧
        let marks : Bool → Set X0 := fun b => if b then S₁ else originalAnnulusOpenMark A
        let core := sourceAnnularCore A hBS
        let alpha := (AddCircle.periodLoop (4 * (8 : ℝ))).map core.continuous
        ∃ (g : (V1 × V2) → X0) (f : C(source, R)),
          PolyhedralPLInCharts e g source ∧ IsEmbedding (fun x : source => g x) ∧
          (∀ x : source, g x = (f x : X0)) ∧
          (∀ x : source, g x ∈ frontier R ↔ (x : V1 × V2).1 ∈ sphere (0 : V1) 1) ∧
          (∀ (b : Bool) (u : Q2), g (endpoint b, u) ∈ marks b) ∧
          ∀ b, ¬ (sourceAnnulusRim f b).Nullhomotopic := by
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  have hp : 0 < p := Fact.out
  have hopen₀ := he.isOpen_preimage_frontier_component hcompactR
    (hS₀ x₀.property) hcomponent₀
  have hopen₁ := he.isOpen_preimage_frontier_component hcompactR
    (hS₁ x₁.property) hcomponent₁
  obtain ⟨h, B, hBS, A, j, hvalue, hcompact, hclosed, hj, hjval, hmark, hcore,
      ⟨retract, hret⟩, _⟩ :=
    M.exists_original_annular_mark e he.compatible H F hF hFval
      (r := p / 4) (by positivity) (by linarith)
  let : PathConnectedSpace S₀ := h.surjective.pathConnectedSpace h.continuous
  let : ConnectedSpace R := isConnected_iff_connectedSpace.mp hR
  let : LocallyPathConnectedSpace R := he.locallyPathConnectedSpace
  let : PathConnectedSpace R := PathConnectedSpace.of_locallyPathConnectedSpace
  let i₀ : C(S₀, R) := ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)
  let i₁ : C(S₁, R) := ContinuousMap.inclusion (hS₁.trans he.closed.frontier_subset)
  let core := sourceAnnularCore A hBS
  let scale := AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num) hp.ne'
  let retract₀ : C(S₀, Circle) := ⟨fun x => scale.symm (retract x),
    scale.symm.continuous.comp retract.continuous⟩
  have hret₀ (z : Circle) : retract₀ (core z) = z := by
    change scale.symm (retract _) = z
    exact (congrArg scale.symm (hret z)).trans (scale.symm_apply_apply z)
  let alpha := (AddCircle.periodLoop (4 * (8 : ℝ))).map core.continuous
  let l := PathConnectedSpace.somePath x₀ (core 0)
  let k := (l.map i₀.continuous).symm.trans k₀
  have hcomm' := _root_.FundamentalGroup.range_map_commensurable_of_source_path
    i₀ i₁ x₀ x₁ k₀ hcomm l
  have hcomm'' : (FundamentalGroup.map i₀ (core 0)).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom.comp
        (FundamentalGroup.map i₁ x₁)).range) := by
    simpa [k] using hcomm'
  have hmarkFrontier : IsOpen ((Subtype.val : frontier R → X0) ⁻¹'
      originalAnnulusOpenMark A) := by
    obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hmark
    have heq : (Subtype.val : frontier R → X0) ⁻¹' originalAnnulusOpenMark A =
        (Subtype.val : frontier R → X0) ⁻¹' S₀ ∩ (Subtype.val : frontier R → X0) ⁻¹' U := by
      ext x
      constructor
      · intro hx
        have hxS := hBS (originalAnnulusOpenMark_subset A hx)
        exact ⟨hxS, show (⟨x, hxS⟩ : S₀) ∈ (Subtype.val : S₀ → X0) ⁻¹' U by
          rw [hUeq]
          exact hx⟩
      · rintro ⟨hxS, hxU⟩
        have : (⟨x, hxS⟩ : S₀) ∈ (Subtype.val : S₀ → X0) ⁻¹' U := hxU
        rwa [hUeq] at this
    rw [heq]
    exact hopen₀.inter (hU.preimage continuous_subtype_val)
  let marks : Bool → Set X0 := fun b => if b then S₁ else originalAnnulusOpenMark A
  have hmarks : ∀ b, marks b ⊆ frontier R := by
    intro b
    cases b
    · exact (originalAnnulusOpenMark_subset A).trans (hBS.trans hS₀)
    · exact hS₁
  have hmarksOpen : ∀ b, IsOpen ((Subtype.val : frontier R → X0) ⁻¹' marks b) := by
    intro b
    cases b
    · exact hmarkFrontier
    · exact hopen₁
  have hmarksDis : Disjoint (marks false) (marks true) :=
    hdis.mono_left ((originalAnnulusOpenMark_subset A).trans hBS)
  have ha : orderOf (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk alpha)) = 0 :=
    orderOf_eq_zero_iff.mpr (sourceAnnularCore_periodLoop_not_isOfFinOrder A hBS retract hret)
  obtain ⟨g, f, hg, hemb, hgf, hproper, hmark', hessential⟩ :=
    exists_commensurable_original_spanning_annulus_in_open_marks he marks hmarks
      hmarksOpen hmarksDis i₀ i₁ (fun x => x.property) (core 0) x₁ k hcomm''
      (hinj (core 0)) alpha (fun t => sourceAnnularCore_mem_mark A hBS _) ha
  exact ⟨h, hvalue, B, hBS, A, j, hcompact, hclosed, hj, hjval, hmarkFrontier,
    hcore, retract₀, hret₀, g, f, hg, hemb, hgf, hproper, hmark', hessential⟩

theorem SourceSquareMap.exists_essential_annulus_in_original_mark_of_commensurable
    {E X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E}
    (M : SourceSquareMap p K)
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) (hcompactR : IsCompact R) (hR : IsConnected R)
    {S₀ S₁ : Set X} (hS₀ : S₀ ⊆ frontier R) (hS₁ : S₁ ⊆ frontier R)
    (hdis : Disjoint S₀ S₁)
    (x₀ : S₀) (x₁ : S₁)
    (hcomponent₀ : connectedComponentIn (frontier R) (x₀ : X) = S₀)
    (hcomponent₁ : connectedComponentIn (frontier R) (x₁ : X) = S₁)
    (hinj : ∀ x : S₀, Function.Injective (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)) x))
    (k₀ : Path
      ((ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)) x₀)
      ((ContinuousMap.inclusion (hS₁.trans he.closed.frontier_subset)) x₁))
    (hcomm : (FundamentalGroup.map
      (ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)) x₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k₀.symm).toMonoidHom.comp
        (FundamentalGroup.map
          (ContinuousMap.inclusion (hS₁.trans he.closed.frontier_subset)) x₁)).range))
    (H : K.space ≃ₜ S₀) (F : E → X)
    (hF : PolyhedralPLInCharts e F K.space) (hFval : ∀ x : K.space, F x = (H x : X)) :
    ∃ h : (AddCircle p × AddCircle p) ≃ₜ S₀,
      (∀ z : Square p, h (projection p z) = H (M.map z)) ∧
    ∃ (B : Set X) (hBS : B ⊆ S₀) (A : Ann ≃ₜ B) (j : P2 → X),
      IsCompact B ∧ IsClosed B ∧
      PolyhedralPLInCharts e j Ann ∧ (∀ z : Ann, j z = (A z : X)) ∧
      IsOpen ((Subtype.val : frontier R → X) ⁻¹' originalAnnulusOpenMark A) ∧
      (∀ z : Circle, (A (annulusCoreCircle z) : X) =
        (h (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
          (Fact.out : (0 : ℝ) < p).ne' z, ((p / 2 : ℝ) : AddCircle p)) : X)) ∧
      ∃ retract : C(S₀, Circle), (∀ z, retract (sourceAnnularCore A hBS z) = z) ∧
      let marks : Bool → Set X := fun b => if b then S₁ else originalAnnulusOpenMark A
      let core := sourceAnnularCore A hBS
      let alpha := (AddCircle.periodLoop (4 * (8 : ℝ))).map core.continuous
      ∃ (g : (V1 × V2) → X) (f : C(source, R)),
        PolyhedralPLInCharts e g source ∧ (∀ x : source, g x = (f x : X)) ∧
        (∀ (b : Bool) (u : Q2), g (endpoint b, u) ∈ marks b) ∧
        (∀ b, ¬ (sourceAnnulusRim f b).Nullhomotopic) ∧
        ∃ n : ℕ, 0 < n ∧ ∃ (beta : Path x₁ x₁)
          (gamma gamma₀ : ∀ b, C(Q2, marks b)),
          (∀ (b : Bool) (u : Q2), g (endpoint b, u) = (gamma₀ b u : X)) ∧
          (∀ b, Nonempty ((gamma b).Homotopy (gamma₀ b))) ∧
          (∀ s : unitInterval, (gamma false (squareRimLoop s) : X) =
            (boundaryLoopIterate alpha n s : X)) ∧
          (∀ s : unitInterval, (gamma true (squareRimLoop s) : X) = (beta s : X)) := by
  have hp : 0 < p := Fact.out
  have hopen₀ := he.isOpen_preimage_frontier_component hcompactR
    (hS₀ x₀.property) hcomponent₀
  have hopen₁ := he.isOpen_preimage_frontier_component hcompactR
    (hS₁ x₁.property) hcomponent₁
  obtain ⟨h, B, hBS, A, j, hvalue, hcompact, hclosed, hj, hjval, hmark, hcore,
      ⟨retract, hret⟩, _⟩ :=
    M.exists_original_annular_mark e he.compatible H F hF hFval
      (r := p / 4) (by positivity) (by linarith)
  let : PathConnectedSpace S₀ := h.surjective.pathConnectedSpace h.continuous
  let : ConnectedSpace R := isConnected_iff_connectedSpace.mp hR
  let : LocallyPathConnectedSpace R := he.locallyPathConnectedSpace
  let : PathConnectedSpace R := PathConnectedSpace.of_locallyPathConnectedSpace
  let i₀ : C(S₀, R) := ContinuousMap.inclusion (hS₀.trans he.closed.frontier_subset)
  let i₁ : C(S₁, R) := ContinuousMap.inclusion (hS₁.trans he.closed.frontier_subset)
  let core := sourceAnnularCore A hBS
  let scale := AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num) hp.ne'
  let retract₀ : C(S₀, Circle) := ⟨fun x => scale.symm (retract x),
    scale.symm.continuous.comp retract.continuous⟩
  have hret₀ (z : Circle) : retract₀ (core z) = z := by
    change scale.symm (retract _) = z
    exact (congrArg scale.symm (hret z)).trans (scale.symm_apply_apply z)
  let alpha := (AddCircle.periodLoop (4 * (8 : ℝ))).map core.continuous
  let l := PathConnectedSpace.somePath x₀ (core 0)
  let k := (l.map i₀.continuous).symm.trans k₀
  have hcomm' := _root_.FundamentalGroup.range_map_commensurable_of_source_path
    i₀ i₁ x₀ x₁ k₀ hcomm l
  have hcomm'' : (FundamentalGroup.map i₀ (core 0)).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom.comp
        (FundamentalGroup.map i₁ x₁)).range) := by
    simpa [k] using hcomm'
  have hmarkFrontier : IsOpen ((Subtype.val : frontier R → X) ⁻¹'
      originalAnnulusOpenMark A) := by
    obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hmark
    have heq : (Subtype.val : frontier R → X) ⁻¹' originalAnnulusOpenMark A =
        (Subtype.val : frontier R → X) ⁻¹' S₀ ∩ (Subtype.val : frontier R → X) ⁻¹' U := by
      ext x
      constructor
      · intro hx
        have hxS := hBS (originalAnnulusOpenMark_subset A hx)
        exact ⟨hxS, show (⟨x, hxS⟩ : S₀) ∈ (Subtype.val : S₀ → X) ⁻¹' U by
          rw [hUeq]; exact hx⟩
      · rintro ⟨hxS, hxU⟩
        have : (⟨x, hxS⟩ : S₀) ∈ (Subtype.val : S₀ → X) ⁻¹' U := hxU
        rwa [hUeq] at this
    rw [heq]
    exact hopen₀.inter (hU.preimage continuous_subtype_val)
  let marks : Bool → Set X := fun b => if b then S₁ else originalAnnulusOpenMark A
  have hmarks : ∀ b, marks b ⊆ frontier R := by
    intro b
    cases b
    · exact (originalAnnulusOpenMark_subset A).trans (hBS.trans hS₀)
    · exact hS₁
  have hmarksOpen : ∀ b, IsOpen ((Subtype.val : frontier R → X) ⁻¹' marks b) := by
    intro b
    cases b
    · exact hmarkFrontier
    · exact hopen₁
  have hmarksDis : Disjoint (marks false) (marks true) :=
    hdis.mono_left ((originalAnnulusOpenMark_subset A).trans hBS)
  have ha : orderOf (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk alpha)) = 0 :=
    orderOf_eq_zero_iff.mpr (sourceAnnularCore_periodLoop_not_isOfFinOrder A hBS retract hret)
  obtain ⟨g, f, hg, hgf, hrim, hessential, hn⟩ :=
    exists_essential_marked_PL_annulus_of_commensurable_open_marks he marks hmarks
      hmarksOpen hmarksDis i₀ i₁ (fun x => x.property) (core 0) x₁ k hcomm''
      (hinj (core 0)) alpha (fun t => sourceAnnularCore_mem_mark A hBS _) ha
  exact ⟨h, hvalue, B, hBS, A, j, hcompact, hclosed, hj, hjval, hmarkFrontier, hcore,
    retract₀, hret₀, g, f, hg, hgf, hrim, hessential, hn⟩

end PoincareConjecture.M76.PeriodicSquare
