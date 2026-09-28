import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.ProjectedDiskCrossing









set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D2" => closedBall (0 : V2) 1

def crossingCoordinates : C3 ≃L[ℝ] V3 where
  toFun := fun z ↦ ![z.1.1, z.1.2, z.2]
  invFun := fun z ↦ ((z 0, z 1), z 2)
  left_inv := fun _ ↦ rfl
  right_inv := by intro z; ext i; fin_cases i <;> rfl
  map_add' := by intros; ext i; fin_cases i <;> rfl
  map_smul' := by intros; ext i; fin_cases i <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def crossingCoordinatesLeftLast : C3 ≃L[ℝ] V3 where
  toFun := fun z ↦ ![z.2, z.1.1, z.1.2]
  invFun := fun z ↦ ((z 1, z 2), z 0)
  left_inv := fun _ ↦ rfl
  right_inv := by intro z; ext i; fin_cases i <;> rfl
  map_add' := by intros; ext i; fin_cases i <;> rfl
  map_smul' := by intros; ext i; fin_cases i <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def crossingCoordinatesRightLast : C3 ≃L[ℝ] V3 where
  toFun := fun z ↦ ![z.1.1, z.2, z.1.2]
  invFun := fun z ↦ ((z 0, z 2), z 1)
  left_inv := fun _ ↦ rfl
  right_inv := by intro z; ext i; fin_cases i <;> rfl
  map_add' := by intros; ext i; fin_cases i <;> rfl
  map_smul' := by intros; ext i; fin_cases i <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem twoBranchWindow_labels
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : X → Y} (w : TwoBranchWindow p) {x y : X}
    (hne : x ≠ y) (hpair : p x = p y) (hx : p x ∈ w.target) :
    (x ∈ w.left.source ∧ y ∈ w.right.source) ∨
      (x ∈ w.right.source ∧ y ∈ w.left.source) := by
  have hy : p y ∈ w.target := hpair ▸ hx
  rcases w.whole_preimage.subset hx with hxl | hxr <;>
    rcases w.whole_preimage.subset hy with hyl | hyr
  · exact False.elim (hne (w.left.injOn hxl hyl (by simpa only [w.left_eq] using hpair)))
  · exact Or.inl ⟨hxl, hyr⟩
  · exact Or.inr ⟨hxr, hyl⟩
  · exact False.elim (hne (w.right.injOn hxr hyr (by simpa only [w.right_eq] using hpair)))

theorem twoBranchWindow_double_images
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : X → Y} (w : TwoBranchWindow p) {A : Set X} {x y : X}
    (hxA : x ∈ A) (hyA : y ∈ A) (hne : x ≠ y)
    (hpair : p x = p y) (hx : p x ∈ w.target) :
    p x ∈ p '' (A ∩ w.left.source) ∧ p x ∈ p '' (A ∩ w.right.source) := by
  rcases twoBranchWindow_labels w hne hpair hx with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · exact ⟨⟨x, ⟨hxA, hl⟩, rfl⟩, ⟨y, ⟨hyA, hr⟩, hpair.symm⟩⟩
  · exact ⟨⟨y, ⟨hyA, hl⟩, hpair.symm⟩, ⟨x, ⟨hxA, hr⟩, rfl⟩⟩

theorem exists_projected_crossing_of_linear_coordinates
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ι → OpenPartialHomeomorph Y V3) (p : X → Y) (d : V2 → X)
    (R : Set Y) (x y : V2) (w : TwoBranchWindow p)
    (T : OpenPartialHomeomorph Y V3) (L : V3 ≃L[ℝ] V3)
    (hne : d x ≠ d y) (hpair : p (d x) = p (d y))
    (hpoint : p (d x) ∈ T.source) (hsource : T.source ⊆ w.target)
    (hPL : ∀ k, (e k).symm.trans T ∈ piecewiseAffineGroupoid V3)
    (hleft : ∀ z ∈ T.source, z ∈ p '' (d '' D2 ∩ w.left.source) ↔
      L (T z) 0 = 0 ∧ z ∈ R)
    (hright : ∀ z ∈ T.source, z ∈ p '' (d '' D2 ∩ w.right.source) ↔
      L (T z) 1 = 0 ∧ z ∈ R)
    (hregion : T.source ⊆ interior R ∨
      ((∀ z ∈ T.source, z ∈ R ↔ 0 ≤ L (T z) 2) ∧
        ∀ z ∈ T.source, z ∈ frontier R ↔ L (T z) 2 = 0)) :
    ∃ B : ProjectedDiskCrossing e p d R x y, B.chart.source = T.source := by
  let Q := T.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hQs : Q.source = T.source := by ext z; simp [Q]
  have hQPL : ∀ k, (e k).symm.trans Q ∈ piecewiseAffineGroupoid V3 := by
    intro k
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have h := (locallyPiecewiseAffineOn_affine
      L.toContinuousLinearMap.toContinuousAffineMap isOpen_univ).comp (hPL k).1
    exact h.mono ((e k).symm.trans Q).open_source
      (fun z hz ↦ ⟨⟨hz.1, hz.2.1⟩, mem_univ _⟩)
  refine ⟨{
    window := w
    chart := Q
    labels := twoBranchWindow_labels w hne hpair (hsource hpoint)
    point := hQs.symm ▸ hpoint
    source := hQs ▸ hsource
    compatible := hQPL
    left_image := ?_
    right_image := ?_
    region := ?_ }, hQs⟩
  · intro z hz
    exact hleft z (hQs ▸ hz)
  · intro z hz
    exact hright z (hQs ▸ hz)
  · rcases hregion with h | ⟨hR, hF⟩
    · exact Or.inl (hQs.symm ▸ h)
    · exact Or.inr ⟨fun z hz ↦ hR z (hQs ▸ hz), fun z hz ↦ hF z (hQs ▸ hz)⟩

end PoincareConjecture.M76.Dehn
