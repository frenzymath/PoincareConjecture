import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.OriginalAnnulusCoordinates










set_option autoImplicit false

open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))


def originalAnnulusOpenMark {X : Type*} [TopologicalSpace X]
    {B : Set X} (H : Ann ≃ₜ B) : Set X :=
  Subtype.val '' {x : B | -1 < depth 8 (H.symm x : ℝ × ℝ) ∧
    depth 8 (H.symm x : ℝ × ℝ) < 1}

theorem originalAnnulusOpenMark_subset {X : Type*} [TopologicalSpace X]
    {B : Set X} (H : Ann ≃ₜ B) : originalAnnulusOpenMark H ⊆ B := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem mem_originalAnnulusOpenMark_iff {X : Type*} [TopologicalSpace X]
    {B : Set X} (H : Ann ≃ₜ B) (x : B) :
    (x : X) ∈ originalAnnulusOpenMark H ↔
      -1 < depth 8 (H.symm x : ℝ × ℝ) ∧ depth 8 (H.symm x : ℝ × ℝ) < 1 := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have heq : y = x := Subtype.ext hxy
    exact heq ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem isOpen_originalAnnulusOpenMark {X : Type*} [TopologicalSpace X]
    {B : Set X} (H : Ann ≃ₜ B) :
    IsOpen ((Subtype.val : B → X) ⁻¹' originalAnnulusOpenMark H) := by
  have heq : (Subtype.val : B → X) ⁻¹' originalAnnulusOpenMark H =
      (fun x : B => depth 8 (H.symm x : ℝ × ℝ)) ⁻¹' Ioo (-1) 1 := by
    ext x
    exact mem_originalAnnulusOpenMark_iff H x
  rw [heq]
  exact isOpen_Ioo.preimage ((continuous_depth 8).comp
    (continuous_subtype_val.comp H.symm.continuous))

theorem originalAnnulusOpenMark_contains_core {X : Type*} [TopologicalSpace X]
    {B : Set X} (H : Ann ≃ₜ B) (z : Circle) :
    (H (annulusCoreCircle z) : X) ∈ originalAnnulusOpenMark H := by
  rw [mem_originalAnnulusOpenMark_iff, H.symm_apply_apply, annulusCoreCircle_apply]
  have hd : depth 8 (annulusMap 8 (by norm_num) (z, 0)) = 0 :=
    depth_annulusMap (by norm_num) (by norm_num) z
  rw [hd]
  norm_num





theorem exists_originalPL_annular_mark_core_homotopy
    {X V ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (e : ι → OpenPartialHomeomorph X V)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {N B R : Set X} (H : Ann ≃ₜ B)
    (F : (ℝ × ℝ) → X) (hF : PolyhedralPLInCharts e F Ann)
    (hFval : ∀ x : Ann, F x = (H x : X))
    (hNB : N ⊆ B) (hBR : B ⊆ R)
    (hdepth : ∀ x : N, -1 < depth 8 (H.symm ⟨x, hNB x.property⟩ : ℝ × ℝ) ∧
      depth 8 (H.symm ⟨x, hNB x.property⟩ : ℝ × ℝ) < 1)
    (gamma : C(Q2, N)) (hinj : Function.Injective gamma)
    (g : V2 → X) (hg : PolyhedralPLInCharts e g Q2)
    (hgval : ∀ x : Q2, g x = (gamma x : X))
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map
        (((ContinuousMap.inclusion (hNB.trans hBR)).comp gamma).continuous))) ≠ 1) :
    ∃ q : Q2 ≃ₜ Circle,
      Nonempty (((ContinuousMap.inclusion hNB).comp gamma).Homotopy
        ((⟨H, H.continuous⟩ : C(Ann, B)).comp
          (annulusCoreCircle.comp ⟨q, q.continuous⟩))) := by
  let gammaB : C(Q2, B) := (ContinuousMap.inclusion hNB).comp gamma
  have hiB : Function.Injective gammaB := by
    intro x y h
    apply hinj
    exact Subtype.ext (congrArg (fun z : B => (z : X)) h)
  have heB : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gammaB.continuous)) ≠ 1 := by
    intro hn
    have h := congrArg
      (FundamentalGroup.map (ContinuousMap.inclusion hBR) (gammaB squareRimBase)) hn
    rw [map_one] at h
    exact hessential h
  exact exists_originalPL_annulus_core_homotopy e hcompat H F hF hFval
    gammaB hiB g hg hgval (fun x => hdepth (gamma x)) heB

end PoincareConjecture.M76.Dehn
