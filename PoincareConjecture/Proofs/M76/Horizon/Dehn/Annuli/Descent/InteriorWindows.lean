import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.ProtectedBoundary
import PoincareConjecture.Proofs.M76.Dehn.OriginalTwoBranchWindows











set_option autoImplicit false

open Set Geometry Topology Metric
open PoincareConjecture.M76.Dehn

namespace Topology.TwoBranchWindow

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {r : X → Y}


def restrictTarget (w : TwoBranchWindow r) (V : Set Y) (hV : IsOpen V) :
    TwoBranchWindow r where
  left := (w.left.symm.restrOpen V hV).symm
  right := (w.right.symm.restrOpen V hV).symm
  target := w.target ∩ V
  open_target := w.open_target.inter hV
  left_target := by change w.left.target ∩ V = _; rw [w.left_target]
  right_target := by change w.right.target ∩ V = _; rw [w.right_target]
  left_eq := w.left_eq
  right_eq := w.right_eq
  disjoint := w.disjoint.mono inter_subset_left inter_subset_left
  whole_preimage := by
    change r ⁻¹' (w.target ∩ V) =
      (w.left.source ∩ w.left ⁻¹' V) ∪ (w.right.source ∩ w.right ⁻¹' V)
    rw [w.left_eq, w.right_eq, preimage_inter, w.whole_preimage,
      union_inter_distrib_right]

theorem mem_restrictTarget_left (w : TwoBranchWindow r) {V : Set Y} (hV : IsOpen V)
    {x : X} (hx : x ∈ w.left.source) (hxr : r x ∈ V) :
    x ∈ (w.restrictTarget V hV).left.source := by
  change x ∈ w.left.source ∩ w.left ⁻¹' V
  rw [w.left_eq]
  exact ⟨hx, hxr⟩

theorem mem_restrictTarget_right (w : TwoBranchWindow r) {V : Set Y} (hV : IsOpen V)
    {x : X} (hx : x ∈ w.right.source) (hxr : r x ∈ V) :
    x ∈ (w.restrictTarget V hV).right.source := by
  change x ∈ w.right.source ∩ w.right ⁻¹' V
  rw [w.right_eq]
  exact ⟨hx, hxr⟩



theorem sources_disjoint_image (w : TwoBranchWindow r) {Z : Type*}
    (j : Z → X) (A : Set Z) (havoid : Disjoint w.target ((r ∘ j) '' A)) :
    Disjoint w.left.source (j '' A) ∧ Disjoint w.right.source (j '' A) := by
  constructor
  · apply disjoint_left.mpr
    rintro x hx ⟨z, hz, rfl⟩
    have hy := w.left.map_source hx
    rw [w.left_target, w.left_eq] at hy
    exact disjoint_left.mp havoid hy ⟨z, hz, rfl⟩
  · apply disjoint_left.mpr
    rintro x hx ⟨z, hz, rfl⟩
    have hy := w.right.map_source hx
    rw [w.right_target, w.right_eq] at hy
    exact disjoint_left.mp havoid hy ⟨z, hz, rfl⟩

end Topology.TwoBranchWindow

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C}



theorem Step.window_sources_interior (step : Step s t)
    (w : TwoBranchWindow (step.projection ∘ step.inclusion)) (R : Set M)
    (hinside : w.target ⊆ interior (s.projection ⁻¹' R)) :
    w.left.source ⊆ interior (t.projection ⁻¹' R) ∧
      w.right.source ⊆ interior (t.projection ⁻¹' R) := by
  have hpre : (step.projection ∘ step.inclusion) ⁻¹' interior (s.projection ⁻¹' R) ⊆
      interior (t.projection ⁻¹' R) := by
    rw [step.region_preimage R]
    exact preimage_interior_subset_interior_preimage
      (step.projection.continuous.comp step.inclusion.continuous)
  constructor
  · intro x hx
    apply hpre
    have hy := w.left.map_source hx
    rw [w.left_target, w.left_eq] at hy
    exact hinside hy
  · intro x hx
    apply hpre
    have hy := w.right.map_source hx
    rw [w.right_target, w.right_eq] at hy
    exact hinside hy




theorem Step.exists_protected_interior_windows (step : Step s t)
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hji : IsEmbedding (fun x : K.space ↦ j x))
    (Q : Set V) (hQ : IsCompact Q) (hQK : Q ⊆ K.space) (R : Set M)
    (hin : MapsTo j K.space (t.projection ⁻¹' R))
    (hproper : ∀ x ∈ K.space, j x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ Q)
    (hrim : InjOn (t.projection ∘ j) Q) :
    let p := (step.projection ∘ step.inclusion) ∘ j
    ∃ (ε : ℝ) (W : Finset (TwoBranchWindow (step.projection ∘ step.inclusion))),
      0 < ε ∧ IsCompact (K.space ∩ cthickening ε Q) ∧
      (∀ w ∈ W, w.target ⊆ interior (s.projection ⁻¹' R) ∧
        Disjoint w.target (p '' (K.space ∩ cthickening ε Q)) ∧
        ∀ k l,
          (t.charts k).symm.trans (w.left.trans (s.charts l)) ∈ piecewiseAffineGroupoid E ∧
          (t.charts k).symm.trans (w.right.trans (s.charts l)) ∈ piecewiseAffineGroupoid E) ∧
      (∀ x ∈ K.space, ∀ y ∈ K.space, p x = p y → x ≠ y →
        ∃ w ∈ W, j x ∈ w.left.source ∧ j y ∈ w.right.source) := by
  classical
  dsimp only
  let p := (step.projection ∘ step.inclusion) ∘ j
  obtain ⟨D, _, ε, _, hDs, _, hDK, hDQ, _, _, hε, hεD, _, _, hsingle⟩ :=
    step.exists_protected_boundary_projection K hK hj hji Q hQ hQK R hproper hrim
  have hp : PolyhedralPLInCharts s.charts p K.space :=
    hj.project step.chartIndex (step.projection.continuous.comp step.inclusion.continuous)
      step.chart_source (fun k x _ ↦ congrFun (step.chart_forward k) x)
  let A := K.space ∩ cthickening ε Q
  have hAc : IsCompact A := (K.isCompact_space_of_finite hK).inter_right isClosed_cthickening
  let O := interior (s.projection ⁻¹' R) ∩ (p '' A)ᶜ
  have hO : IsOpen O := isOpen_interior.inter
    (hAc.image_of_continuousOn (hp.continuousOn.mono inter_subset_left)).isClosed.isOpen_compl
  have hDO : MapsTo p D.space O := by
    intro x hx
    have hxK := hDK hx
    have hxQ : x ∉ Q := fun hxQ ↦ disjoint_left.mp hDQ hx hxQ
    have hpR : p x ∈ s.projection ⁻¹' R := (step.region_preimage R).subset (hin hxK)
    refine ⟨(mem_interior_iff_notMem_frontier hpR).mpr ?_, ?_⟩
    · intro hfront
      apply hxQ
      apply (hproper x hxK).mp
      rw [step.frontier_preimage R]
      exact hfront
    · rintro ⟨y, hy, hyx⟩
      have hyEq : y = x := hsingle y hy.1 hy.2 x hxK hyx
      exact hεD hy.2 (hyEq.symm ▸ hx)
  let : CompactSpace K.space :=
    isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  obtain ⟨W, _, hW⟩ := step.exists_finite_PL_twoBranchWindows hji
  refine ⟨ε, W.image (fun w ↦ w.restrictTarget O hO), hε, hAc, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨fun _ hx ↦ hx.2.1, ?_, ?_⟩
    · exact disjoint_left.mpr fun _ hx hA ↦ hx.2.2 hA
    · intro k l
      exact ⟨step.branch_chart_PL _ (fun x _ ↦ congrFun (v.restrictTarget O hO).left_eq x) k l,
        step.branch_chart_PL _ (fun x _ ↦ congrFun (v.restrictTarget O hO).right_eq x) k l⟩
  · intro x hx y hy hxy hne
    have hxD : x ∈ D.space := hDs.symm.subset ⟨hx, y, hy, hxy, hne⟩
    have hyD : y ∈ D.space := hDs.symm.subset ⟨hy, x, hx, hxy.symm, hne.symm⟩
    obtain ⟨w, hw, hxw, hyw⟩ := hW ⟨x, hx⟩ ⟨y, hy⟩ hxy
      (fun heq ↦ hne (congrArg Subtype.val heq))
    exact ⟨w.restrictTarget O hO, Finset.mem_image.mpr ⟨w, hw, rfl⟩,
      w.mem_restrictTarget_left hO hxw (hDO hxD),
      w.mem_restrictTarget_right hO hyw (hDO hyD)⟩

end Geometry.OriginalPLTower
