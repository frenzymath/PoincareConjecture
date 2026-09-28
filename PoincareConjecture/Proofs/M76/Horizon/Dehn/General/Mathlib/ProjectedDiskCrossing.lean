import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Crossings.RawCrossingCharts

set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

structure ProjectedDiskCrossing {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ι → OpenPartialHomeomorph Y V3) (p : X → Y) (d : V2 → X)
    (R : Set Y) (x y : V2) where
  window : TwoBranchWindow p
  chart : OpenPartialHomeomorph Y V3
  labels : (d x ∈ window.left.source ∧ d y ∈ window.right.source) ∨
    (d x ∈ window.right.source ∧ d y ∈ window.left.source)
  point : p (d x) ∈ chart.source
  source : chart.source ⊆ window.target
  compatible : ∀ k, (e k).symm.trans chart ∈ piecewiseAffineGroupoid V3
  left_image : ∀ z ∈ chart.source, z ∈ p '' (d '' D2 ∩ window.left.source) ↔
    chart z 0 = 0 ∧ z ∈ R
  right_image : ∀ z ∈ chart.source, z ∈ p '' (d '' D2 ∩ window.right.source) ↔
    chart z 1 = 0 ∧ z ∈ R
  region : chart.source ⊆ interior R ∨
    ((∀ z ∈ chart.source, z ∈ R ↔ 0 ≤ chart z 2) ∧
      ∀ z ∈ chart.source, z ∈ frontier R ↔ chart z 2 = 0)

def ProjectedDiskCrossing.transport
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph Y V3} {p : X → Y} {d g : V2 → X}
    {R : Set Y} {x y : V2} (B : ProjectedDiskCrossing e p d R x y)
    (hx : g x = d x) (hy : g y = d y)
    (himage : ∀ A : Set X, ∀ z ∈ B.chart.source,
      z ∈ p '' (g '' D2 ∩ A) ↔ z ∈ p '' (d '' D2 ∩ A)) :
    ProjectedDiskCrossing e p g R x y where
  window := B.window
  chart := B.chart
  labels := by simpa only [hx, hy] using B.labels
  point := hx.symm ▸ B.point
  source := B.source
  compatible := B.compatible
  left_image := fun z hz ↦ (himage B.window.left.source z hz).trans (B.left_image z hz)
  right_image := fun z hz ↦ (himage B.window.right.source z hz).trans (B.right_image z hz)
  region := B.region

theorem ProjectedDiskCrossing.nonempty_raw
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph Y V3} {p : X → Y} {d : V2 → X}
    {R : Set Y} {x y : V2} (B : ProjectedDiskCrossing e p d R x y)
    (hd : IsEmbedding (fun z : D2 ↦ d z)) (hx : x ∈ D2) (hy : y ∈ D2)
    (hxy : p (d x) = p (d y)) : Nonempty (RawCrossingChart e (p ∘ d) R x y) :=
  nonempty_rawCrossingChart_of_twoBranchWindow d p hd hx hy hxy B.window B.chart
    B.labels B.point B.source B.compatible B.left_image B.right_image B.region

end PoincareConjecture.M76.Dehn
