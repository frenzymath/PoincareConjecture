import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.ProjectedCrossingCoordinates

set_option autoImplicit false

open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)

structure ProjectedSourceCrossing {E X Y ι : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : ι → OpenPartialHomeomorph Y V3) (p : X → Y) (d : E → X)
    (S : Set E) (R : Set Y) (x y : E) where
  window : TwoBranchWindow p
  chart : OpenPartialHomeomorph Y V3
  labels : (d x ∈ window.left.source ∧ d y ∈ window.right.source) ∨
    (d x ∈ window.right.source ∧ d y ∈ window.left.source)
  point : p (d x) ∈ chart.source
  source : chart.source ⊆ window.target
  compatible : ∀ k, (e k).symm.trans chart ∈ piecewiseAffineGroupoid V3
  left_image : ∀ z ∈ chart.source, z ∈ p '' (d '' S ∩ window.left.source) ↔
    chart z 0 = 0 ∧ z ∈ R
  right_image : ∀ z ∈ chart.source, z ∈ p '' (d '' S ∩ window.right.source) ↔
    chart z 1 = 0 ∧ z ∈ R
  region : chart.source ⊆ interior R ∨
    ((∀ z ∈ chart.source, z ∈ R ↔ 0 ≤ chart z 2) ∧
      ∀ z ∈ chart.source, z ∈ frontier R ↔ chart z 2 = 0)

namespace ProjectedSourceCrossing

variable {E X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {e : ι → OpenPartialHomeomorph Y V3} {p : X → Y} {d g : E → X}
  {S : Set E} {R : Set Y} {x y : E}

def transport (B : ProjectedSourceCrossing e p d S R x y)
    (hx : g x = d x) (hy : g y = d y)
    (himage : ∀ A : Set X, ∀ z ∈ B.chart.source,
      z ∈ p '' (g '' S ∩ A) ↔ z ∈ p '' (d '' S ∩ A)) :
    ProjectedSourceCrossing e p g S R x y where
  window := B.window
  chart := B.chart
  labels := by simpa only [hx, hy] using B.labels
  point := hx.symm ▸ B.point
  source := B.source
  compatible := B.compatible
  left_image := fun z hz ↦ (himage B.window.left.source z hz).trans (B.left_image z hz)
  right_image := fun z hz ↦ (himage B.window.right.source z hz).trans (B.right_image z hz)
  region := B.region

def restrOpen (B : ProjectedSourceCrossing e p d S R x y)
    (W : Set Y) (hW : IsOpen W) (hx : p (d x) ∈ W) :
    ProjectedSourceCrossing e p d S R x y where
  window := B.window
  chart := B.chart.restrOpen W hW
  labels := B.labels
  point := ⟨B.point, hx⟩
  source := fun _ hz ↦ B.source hz.1
  compatible := fun k ↦ (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    ((B.compatible k).1.mono ((e k).symm.trans (B.chart.restrOpen W hW)).open_source
      (fun _ hz ↦ ⟨hz.1, hz.2.1⟩))
  left_image := fun z hz ↦ B.left_image z hz.1
  right_image := fun z hz ↦ B.right_image z hz.1
  region := B.region.elim (fun h ↦ Or.inl (fun _ hz ↦ h hz.1))
    (fun h ↦ Or.inr ⟨fun z hz ↦ h.1 z hz.1, fun z hz ↦ h.2 z hz.1⟩)

theorem exists_of_linear_coordinates
    (e : ι → OpenPartialHomeomorph Y V3) (p : X → Y) (d : E → X)
    (S : Set E) (R : Set Y) (x y : E) (w : TwoBranchWindow p)
    (T : OpenPartialHomeomorph Y V3) (L : V3 ≃L[ℝ] V3)
    (hne : d x ≠ d y) (hpair : p (d x) = p (d y))
    (hpoint : p (d x) ∈ T.source) (hsource : T.source ⊆ w.target)
    (hPL : ∀ k, (e k).symm.trans T ∈ piecewiseAffineGroupoid V3)
    (hleft : ∀ z ∈ T.source, z ∈ p '' (d '' S ∩ w.left.source) ↔
      L (T z) 0 = 0 ∧ z ∈ R)
    (hright : ∀ z ∈ T.source, z ∈ p '' (d '' S ∩ w.right.source) ↔
      L (T z) 1 = 0 ∧ z ∈ R)
    (hregion : T.source ⊆ interior R ∨
      ((∀ z ∈ T.source, z ∈ R ↔ 0 ≤ L (T z) 2) ∧
        ∀ z ∈ T.source, z ∈ frontier R ↔ L (T z) 2 = 0)) :
    ∃ B : ProjectedSourceCrossing e p d S R x y, B.chart.source = T.source := by
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
    left_image := fun z hz ↦ hleft z (hQs ▸ hz)
    right_image := fun z hz ↦ hright z (hQs ▸ hz)
    region := ?_ }, hQs⟩
  rcases hregion with h | ⟨hR, hF⟩
  · exact Or.inl (hQs.symm ▸ h)
  · exact Or.inr ⟨fun z hz ↦ hR z (hQs ▸ hz), fun z hz ↦ hF z (hQs ▸ hz)⟩

end ProjectedSourceCrossing
end PoincareConjecture.M76.Dehn
