import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.OriginalTorusAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.OriginalAnnulusMark
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.SwappedSquareMap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.CoordinateGenerator

set_option autoImplicit false
open Set Metric Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.PeriodicSquare

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

theorem SourceSquareMap.exists_original_annular_mark
    {E V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] [T2Space X]
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E}
    (M : SourceSquareMap p K)
    (e : ι → OpenPartialHomeomorph X V)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {S : Set X} (H : K.space ≃ₜ S) (F : E → X)
    (hF : PolyhedralPLInCharts e F K.space) (hFval : ∀ x : K.space, F x = (H x : X))
    {r : ℝ} (hr : 0 < r) (hwidth : r < p / 2) :
    ∃ (h : (AddCircle p × AddCircle p) ≃ₜ S)
      (B : Set X) (hBS : B ⊆ S) (A : Ann ≃ₜ B) (j : P2 → X),
      (∀ z : Square p, h (projection p z) = H (M.map z)) ∧
      IsCompact B ∧ IsClosed B ∧
      PolyhedralPLInCharts e j Ann ∧ (∀ z : Ann, j z = (A z : X)) ∧
      IsOpen ((Subtype.val : S → X) ⁻¹' Dehn.originalAnnulusOpenMark A) ∧
      (∀ z : Circle, (A (Dehn.annulusCoreCircle z) : X) =
        (h (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
          (Fact.out : (0 : ℝ) < p).ne' z, ((p / 2 : ℝ) : AddCircle p)) : X)) ∧
      (∃ retract : C(S, AddCircle p), ∀ z : Circle,
        retract ⟨A (Dehn.annulusCoreCircle z), hBS (A (Dehn.annulusCoreCircle z)).property⟩ =
          AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
            (Fact.out : (0 : ℝ) < p).ne' z) ∧
      ∀ {R : Set X} (hSR : S ⊆ R)
      (gamma : C(Q2, Dehn.originalAnnulusOpenMark A)), Function.Injective gamma →
      ∀ (g : V2 → X), PolyhedralPLInCharts e g Q2 →
      (∀ x : Q2, g x = (gamma x : X)) →
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map
        (((ContinuousMap.inclusion
          ((Dehn.originalAnnulusOpenMark_subset A).trans
            (hBS.trans hSR))).comp gamma).continuous))) ≠ 1 →
      ∃ q : Q2 ≃ₜ Circle,
        Nonempty (((ContinuousMap.inclusion (Dehn.originalAnnulusOpenMark_subset A)).comp gamma).Homotopy
          ((⟨A, A.continuous⟩ : C(Ann, B)).comp
            (Dehn.annulusCoreCircle.comp ⟨q, q.continuous⟩))) := by
  obtain ⟨h, b, B, hBS, A, j, N, hvalue, _, _, _, hcompact, hclosed,
    hj, hjvalue, _, hNopen, hNsub, hmark, hcore, _⟩ :=
    M.exists_original_coordinate_annulus e H F hF hFval hr hwidth
  have hN : (Subtype.val : S → X) ⁻¹' Dehn.originalAnnulusOpenMark A = N := by
    ext x
    constructor
    · intro hx
      have hxB := Dehn.originalAnnulusOpenMark_subset A hx
      let y : B := ⟨x, hxB⟩
      have hd := (Dehn.mem_originalAnnulusOpenMark_iff A y).mp hx
      have hm := (hmark (A.symm y)).mpr hd
      simpa only [A.apply_symm_apply] using hm
    · intro hx
      let y : B := ⟨x, hNsub hx⟩
      apply (Dehn.mem_originalAnnulusOpenMark_iff A y).mpr
      apply (hmark (A.symm y)).mp
      simpa only [A.apply_symm_apply] using hx
  refine ⟨h, B, hBS, A, j, hvalue, hcompact, hclosed, hj, hjvalue,
    hN.symm ▸ hNopen, hcore, ?_, ?_⟩
  · refine ⟨⟨fun x => (h.symm x).1, h.symm.continuous.fst⟩, ?_⟩
    intro z
    have heq : (⟨A (Dehn.annulusCoreCircle z),
        hBS (A (Dehn.annulusCoreCircle z)).property⟩ : S) =
        h (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
          (Fact.out : (0 : ℝ) < p).ne' z, ((p / 2 : ℝ) : AddCircle p)) :=
      Subtype.ext (hcore z)
    change (h.symm _).1 = _
    rw [heq, h.symm_apply_apply]
  intro R hSR gamma hinj g hg hgvalue hessential
  exact Dehn.exists_originalPL_annular_mark_core_homotopy e hcompat A j hj hjvalue
    (Dehn.originalAnnulusOpenMark_subset A) (hBS.trans hSR)
    (fun x => (Dehn.mem_originalAnnulusOpenMark_iff A
      ⟨x, Dehn.originalAnnulusOpenMark_subset A x.property⟩).mp x.property)
    gamma hinj g hg hgvalue hessential

theorem SourceSquareMap.exists_two_original_annular_marks
    {E V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] [T2Space X]
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E}
    (M : SourceSquareMap p K)
    (e : ι → OpenPartialHomeomorph X V)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {S : Set X} (H : K.space ≃ₜ S) (F : E → X)
    (hF : PolyhedralPLInCharts e F K.space) (hFval : ∀ x : K.space, F x = (H x : X))
    {r : ℝ} (hr : 0 < r) (hwidth : r < p / 2) :
    ∃ h : (AddCircle p × AddCircle p) ≃ₜ S,
      (∀ z : Square p, h (projection p z) = H (M.map z)) ∧
      ∀ side : Bool,
      ∃ (B : Set X) (hBS : B ⊆ S) (A : Ann ≃ₜ B) (j : P2 → X),
        IsCompact B ∧ IsClosed B ∧
        PolyhedralPLInCharts e j Ann ∧ (∀ z : Ann, j z = (A z : X)) ∧
        IsOpen ((Subtype.val : S → X) ⁻¹' Dehn.originalAnnulusOpenMark A) ∧
        (∀ z : Circle, (A (Dehn.annulusCoreCircle z) : X) =
          (h (if side then
            (((p / 2 : ℝ) : AddCircle p),
              AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
                (Fact.out : (0 : ℝ) < p).ne' z)
            else (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
              (Fact.out : (0 : ℝ) < p).ne' z, ((p / 2 : ℝ) : AddCircle p))) : X)) ∧
        (∃ retract : C(S, AddCircle p), ∀ z : Circle,
          retract ⟨A (Dehn.annulusCoreCircle z), hBS (A (Dehn.annulusCoreCircle z)).property⟩ =
            AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
              (Fact.out : (0 : ℝ) < p).ne' z) ∧
        ∀ {R : Set X} (hSR : S ⊆ R)
        (gamma : C(Q2, Dehn.originalAnnulusOpenMark A)), Function.Injective gamma →
        ∀ (g : V2 → X), PolyhedralPLInCharts e g Q2 →
        (∀ x : Q2, g x = (gamma x : X)) →
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map
          (((ContinuousMap.inclusion
            ((Dehn.originalAnnulusOpenMark_subset A).trans
              (hBS.trans hSR))).comp gamma).continuous))) ≠ 1 →
        ∃ q : Q2 ≃ₜ Circle,
          Nonempty (((ContinuousMap.inclusion (Dehn.originalAnnulusOpenMark_subset A)).comp gamma).Homotopy
            ((⟨A, A.continuous⟩ : C(Ann, B)).comp
              (Dehn.annulusCoreCircle.comp ⟨q, q.continuous⟩))) := by
  obtain ⟨h0, h0value⟩ := exists_homeomorph_of_sourceSquareMap p M
  let h := h0.trans H
  have hvalue (z : Square p) : h (projection p z) = H (M.map z) :=
    congrArg H (h0value z)
  refine ⟨h, hvalue, ?_⟩
  intro side
  cases side
  · obtain ⟨hf, B, hBS, A, j, hfvalue, hc, hclosed, hj, hjv, hopen, hcore, hret, hcurves⟩ :=
      M.exists_original_annular_mark e hcompat H F hF hFval hr hwidth
    have heq : hf = h := by
      apply Homeomorph.ext
      intro x
      obtain ⟨z, rfl⟩ := surjective_projection p x
      exact (hfvalue z).trans (hvalue z).symm
    rw [heq] at hcore
    exact ⟨B, hBS, A, j, hc, hclosed, hj, hjv, hopen, hcore, hret, hcurves⟩
  · obtain ⟨hs, B, hBS, A, j, hsvalue, hc, hclosed, hj, hjv, hopen, hcore, hret, hcurves⟩ :=
      M.swap.exists_original_annular_mark e hcompat H F hF hFval hr hwidth
    have heq : hs = (Homeomorph.prodComm _ _).trans h := by
      apply Homeomorph.ext
      intro x
      obtain ⟨z, rfl⟩ := surjective_projection p x
      rw [hsvalue]
      exact (hvalue (squareSwap p z)).symm
    rw [heq] at hcore
    exact ⟨B, hBS, A, j, hc, hclosed, hj, hjv, hopen, hcore, hret, hcurves⟩

noncomputable def sourceAnnularCore {X : Type*} [TopologicalSpace X]
    {B S : Set X} (A : Ann ≃ₜ B) (hBS : B ⊆ S) : C(Circle, S) :=
  (ContinuousMap.inclusion hBS).comp
    ((⟨A, A.continuous⟩ : C(Ann, B)).comp Dehn.annulusCoreCircle)

theorem sourceAnnularCore_mem_mark {X : Type*} [TopologicalSpace X]
    {B S : Set X} (A : Ann ≃ₜ B) (hBS : B ⊆ S) (z : Circle) :
    (sourceAnnularCore A hBS z : X) ∈ Dehn.originalAnnulusOpenMark A :=
  Dehn.originalAnnulusOpenMark_contains_core A z

theorem sourceAnnularCore_periodLoop_not_isOfFinOrder
    {X : Type*} [TopologicalSpace X] {p : ℝ} [Fact (0 < p)]
    {B S : Set X} (A : Ann ≃ₜ B) (hBS : B ⊆ S)
    (retract : C(S, AddCircle p))
    (hret : ∀ z : Circle,
      retract ⟨A (Dehn.annulusCoreCircle z), hBS (A (Dehn.annulusCoreCircle z)).property⟩ =
        AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
          (Fact.out : (0 : ℝ) < p).ne' z) :
    ¬ IsOfFinOrder (G := FundamentalGroup S (sourceAnnularCore A hBS 0))
      (Path.Homotopic.Quotient.mk ((AddCircle.periodLoop (4 * (8 : ℝ))).map
        (sourceAnnularCore A hBS).continuous)) := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let scale := AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p (by norm_num)
    (Fact.out : (0 : ℝ) < p).ne'
  let r : C(S, Circle) := ⟨fun x => scale.symm (retract x),
    scale.symm.continuous.comp retract.continuous⟩
  apply coordinate_periodLoop_not_isOfFinOrder (sourceAnnularCore A hBS) r
  intro z
  change scale.symm (retract _) = z
  exact (congrArg scale.symm (hret z)).trans (scale.symm_apply_apply z)

end PoincareConjecture.M76.PeriodicSquare
