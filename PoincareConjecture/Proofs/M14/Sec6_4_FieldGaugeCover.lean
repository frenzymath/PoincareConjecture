import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift
import PoincareConjecture.Definitions.M14PathCalculus
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}

structure SquareFieldGaugePatch (R : M14SquareRootPath G p) where
  gauge : G.gaugeCover.index
  domain : Set G.Point
  lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval gauge)).Point ×
    G.gaugeCover.spatial gauge
  domain_open : IsOpen domain
  lift_smooth : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift domain
  right_inverse : ∀ q ∈ domain, (G.gaugeCover.cylinder gauge).toSpacetime (lift q) = q
  parameterSet : Set ℝ
  parameter_open : IsOpen parameterSet
  curve_mem : ∀ s ∈ M14SqrtParameterInterval a b ∩ parameterSet, R.curve s ∈ domain

theorem exists_squareFieldGaugePatch (R : M14SquareRootPath G p) {s : ℝ}
    (hs : s ∈ M14SqrtParameterInterval a b) :
    ∃ D : SquareFieldGaugePatch R, s ∈ D.parameterSet := by
  obtain ⟨j, U, lift, hU, hsU, hlift, hright, _⟩ := exists_smooth_gauge_lift G (R.curve s)
  have hpre : R.curve ⁻¹' U ∈ 𝓝[M14SqrtParameterInterval a b] s :=
    (R.smooth.continuousOn.mono R.interval_subset s hs).preimage_mem_nhdsWithin
      (hU.mem_nhds hsU)
  obtain ⟨N, hN, hsN, hsub⟩ := mem_nhdsWithin.mp hpre
  exact ⟨⟨j, U, lift, hU, hlift, hright, N, hN, fun _ hr => hsub ⟨hr.2, hr.1⟩⟩, hsN⟩

theorem exists_finite_squareFieldGaugeCover (R : M14SquareRootPath G p) :
    ∃ (m : ℕ) (D : Fin m → SquareFieldGaugePatch R),
      M14SqrtParameterInterval a b ⊆ ⋃ i, (D i).parameterSet := by
  classical
  let C := M14SqrtParameterInterval a b
  choose D hD using fun s : C => exists_squareFieldGaugePatch R s.property
  have hcover : C ⊆ ⋃ s : C, (D s).parameterSet := fun s hs =>
    mem_iUnion.mpr ⟨⟨s, hs⟩, hD ⟨s, hs⟩⟩
  obtain ⟨S, hS⟩ := (show IsCompact C from isCompact_Icc).elim_finite_subcover
    (fun s : C => (D s).parameterSet) (fun s => (D s).parameter_open) hcover
  let e := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun i => D (e i).val, ?_⟩
  intro s hs
  obtain ⟨t, htS, hst⟩ := mem_iUnion₂.mp (hS hs)
  obtain ⟨i, hi⟩ := e.surjective ⟨t, htS⟩
  exact mem_iUnion.mpr ⟨i, by simpa only [hi] using hst⟩

end PoincareConjecture.M14
