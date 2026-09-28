import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.CommensurableAnnularMark

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

theorem SourceSquareMap.exists_two_essential_annuli_in_original_marks
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
      ∀ side : Bool,
      ∃ (B : Set X) (hBS : B ⊆ S₀) (A : Ann ≃ₜ B) (j : P2 → X),
        IsCompact B ∧ IsClosed B ∧
        PolyhedralPLInCharts e j Ann ∧ (∀ z : Ann, j z = (A z : X)) ∧
        IsOpen ((Subtype.val : frontier R → X) ⁻¹' originalAnnulusOpenMark A) ∧
        (∀ z : Circle, (A (annulusCoreCircle z) : X) =
          (h (if side then (((p / 2 : ℝ) : AddCircle p),
            AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
              (Fact.out : (0 : ℝ) < p).ne' z)
          else (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
            (Fact.out : (0 : ℝ) < p).ne' z, ((p / 2 : ℝ) : AddCircle p))) : X)) ∧
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
  obtain ⟨h₀, h₀value⟩ := exists_homeomorph_of_sourceSquareMap p M
  let h := h₀.trans H
  have hvalue (z : Square p) : h (projection p z) = H (M.map z) :=
    congrArg H (h₀value z)
  refine ⟨h, hvalue, ?_⟩
  intro side
  cases side
  · obtain ⟨hf, hfvalue, B, hBS, A, j, hc, hclosed, hj, hjv, hopen, hcore, hrest⟩ :=
      M.exists_essential_annulus_in_original_mark he hcompactR hR hS₀ hS₁ hdis
        x₀ x₁ hcomponent₀ hcomponent₁ hinj hindex₀ hindex₁ H F hF hFval
    have heq : hf = h := by
      apply Homeomorph.ext
      intro x
      obtain ⟨z, rfl⟩ := surjective_projection p x
      exact (hfvalue z).trans (hvalue z).symm
    rw [heq] at hcore
    dsimp at hrest
    obtain ⟨retract, hret, g, f, hg, hemb, hgf, hproper, hmark, hessential⟩ := hrest
    exact ⟨B, hBS, A, j, hc, hclosed, hj, hjv, hopen, hcore,
      retract, hret, g, f, hg, hemb, hgf, hproper, hmark, hessential⟩
  · obtain ⟨hs, hsvalue, B, hBS, A, j, hc, hclosed, hj, hjv, hopen, hcore, hrest⟩ :=
      M.swap.exists_essential_annulus_in_original_mark he hcompactR hR hS₀ hS₁ hdis
        x₀ x₁ hcomponent₀ hcomponent₁ hinj hindex₀ hindex₁ H F hF hFval
    have heq : hs = (Homeomorph.prodComm _ _).trans h := by
      apply Homeomorph.ext
      intro x
      obtain ⟨z, rfl⟩ := surjective_projection p x
      rw [hsvalue]
      exact (hvalue (squareSwap p z)).symm
    rw [heq] at hcore
    dsimp at hrest
    obtain ⟨retract, hret, g, f, hg, hemb, hgf, hproper, hmark, hessential⟩ := hrest
    exact ⟨B, hBS, A, j, hc, hclosed, hj, hjv, hopen, hcore,
      retract, hret, g, f, hg, hemb, hgf, hproper, hmark, hessential⟩

theorem SourceSquareMap.exists_two_essential_annuli_in_original_marks_of_commensurable
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
      ∀ side : Bool,
      ∃ (B : Set X) (hBS : B ⊆ S₀) (A : Ann ≃ₜ B) (j : P2 → X),
        IsCompact B ∧ IsClosed B ∧
        PolyhedralPLInCharts e j Ann ∧ (∀ z : Ann, j z = (A z : X)) ∧
        IsOpen ((Subtype.val : frontier R → X) ⁻¹' originalAnnulusOpenMark A) ∧
        (∀ z : Circle, (A (annulusCoreCircle z) : X) =
          (h (if side then (((p / 2 : ℝ) : AddCircle p),
            AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
              (Fact.out : (0 : ℝ) < p).ne' z)
          else (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
            (Fact.out : (0 : ℝ) < p).ne' z, ((p / 2 : ℝ) : AddCircle p))) : X)) ∧
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
  obtain ⟨h₀, h₀value⟩ := exists_homeomorph_of_sourceSquareMap p M
  let h := h₀.trans H
  have hvalue (z : Square p) : h (projection p z) = H (M.map z) :=
    congrArg H (h₀value z)
  refine ⟨h, hvalue, ?_⟩
  intro side
  cases side
  · obtain ⟨hf, hfvalue, B, hBS, A, j, hc, hclosed, hj, hjv, hopen, hcore, hrest⟩ :=
      M.exists_essential_annulus_in_original_mark_of_commensurable he hcompactR hR
        hS₀ hS₁ hdis x₀ x₁ hcomponent₀ hcomponent₁ hinj k₀ hcomm H F hF hFval
    have heq : hf = h := by
      apply Homeomorph.ext
      intro x
      obtain ⟨z, rfl⟩ := surjective_projection p x
      exact (hfvalue z).trans (hvalue z).symm
    rw [heq] at hcore
    exact ⟨B, hBS, A, j, hc, hclosed, hj, hjv, hopen, hcore, hrest⟩
  · obtain ⟨hs, hsvalue, B, hBS, A, j, hc, hclosed, hj, hjv, hopen, hcore, hrest⟩ :=
      M.swap.exists_essential_annulus_in_original_mark_of_commensurable he hcompactR hR
        hS₀ hS₁ hdis x₀ x₁ hcomponent₀ hcomponent₁ hinj k₀ hcomm H F hF hFval
    have heq : hs = (Homeomorph.prodComm _ _).trans h := by
      apply Homeomorph.ext
      intro x
      obtain ⟨z, rfl⟩ := surjective_projection p x
      rw [hsvalue]
      exact (hvalue (squareSwap p z)).symm
    rw [heq] at hcore
    exact ⟨B, hBS, A, j, hc, hclosed, hj, hjv, hopen, hcore, hrest⟩

end PoincareConjecture.M76.PeriodicSquare
