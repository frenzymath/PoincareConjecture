import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Hyperbola
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1



theorem negative_chart_coordinate_eq_levelArc
    {height : S2 → Real} {c t : Real}
    (e : OpenPartialHomeomorph E2 S2)
    (hform : ∀ u ∈ e.source, height (e u) = c - (u 0)^2 + (u 1)^2)
    {q : S2} (hq : q ∈ e.target) (hlevel : height q = c + t)
    (hnegative : e.symm q 0 < 0) :
    e.symm q = negativeLevelArc (-t) 1 (e.symm q 1) := by
  have hh := hform (e.symm q) (e.map_target hq)
  rw [e.right_inv hq, hlevel] at hh
  have hsq : -t + (e.symm q 1)^2 = (e.symm q 0)^2 := by linarith
  ext i
  fin_cases i
  · change e.symm q 0 = -Real.sqrt (-t + (e.symm q 1)^2)
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_neg hnegative, neg_neg]
  · rfl


def anchorLongitudinalCoordinate
    (e : OpenPartialHomeomorph E2 S2) (α : S1 → S2) (q : S1) : Real :=
  e.symm (α q) 1




theorem negative_anchor_longitudinal_geometry
    {height : S2 → Real} {c t : Real} (ht : t < 0)
    (α : S1 → S2) (hα : ContMDiff (𝓡 1) (𝓡 2) ∞ α)
    (hαinj : Injective α)
    (hαder : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) α q))
    (hlevel : ∀ q, height (α q) = c + t)
    (e : OpenPartialHomeomorph E2 S2)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ u ∈ e.source, height (e u) = c - (u 0)^2 + (u 1)^2)
    {U : Set S2} (hU : IsOpen U) (hUtarget : U ⊆ e.target)
    (hnegative : ∀ q, α q ∈ U → e.symm (α q) 0 < 0) :
    ContMDiffOn (𝓡 1) 𝓘(Real, Real) ∞ (anchorLongitudinalCoordinate e α) (α ⁻¹' U) ∧
      InjOn (anchorLongitudinalCoordinate e α) (α ⁻¹' U) ∧
      ∀ q ∈ α ⁻¹' U,
        Injective (mfderiv (𝓡 1) 𝓘(Real, Real) (anchorLongitudinalCoordinate e α) q) := by
  let y := anchorLongitudinalCoordinate e α
  let arc := negativeLevelArc (-t) 1
  have hV : IsOpen (α ⁻¹' U) := hU.preimage hα.continuous
  have hcoords : ContMDiffOn (𝓡 1) (𝓡 2) ∞ (fun q => e.symm (α q)) (α ⁻¹' U) :=
    hei.comp hα.contMDiffOn (fun q hq => hUtarget hq)
  have hy : ContMDiffOn (𝓡 1) 𝓘(Real, Real) ∞ y (α ⁻¹' U) :=
    (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contMDiff.comp_contMDiffOn hcoords
  have hcoord (q : S1) (hq : q ∈ α ⁻¹' U) : e.symm (α q) = arc (y q) :=
    negative_chart_coordinate_eq_levelArc e hform (hUtarget hq) (hlevel q) (hnegative q hq)
  have hfactor (q : S1) (hq : q ∈ α ⁻¹' U) : e (arc (y q)) = α q := by
    rw [← hcoord q hq]
    exact e.right_inv (hUtarget hq)
  refine ⟨hy, ?_, ?_⟩
  · intro q hq z hz hqz
    apply hαinj
    calc
      α q = e (arc (y q)) := (hfactor q hq).symm
      _ = e (arc (y z)) := congrArg (fun x => e (arc x)) hqz
      _ = α z := hfactor z hz
  · intro q hq
    have hyq := hy.contMDiffAt (hV.mem_nhds hq)
    have harc : ContMDiff 𝓘(Real, Real) (𝓡 2) ∞ arc :=
      (contDiff_negativeLevelArc (neg_pos.mpr ht) 1).contMDiff
    have hsource : arc (y q) ∈ e.source := (hcoord q hq) ▸ e.map_target (hUtarget hq)
    have houter : ContMDiffAt 𝓘(Real, Real) (𝓡 2) ∞ (e ∘ arc) (y q) :=
      (he.contMDiffAt (e.open_source.mem_nhds hsource)).comp (y q) (harc (y q))
    have heq : α =ᶠ[𝓝 q] (e ∘ arc) ∘ y := by
      filter_upwards [hV.mem_nhds hq] with z hz
      exact (hfactor z hz).symm
    have hd := hαder q
    rw [heq.mfderiv_eq (I := 𝓡 1) (I' := 𝓡 2),
      mfderiv_comp q (houter.mdifferentiableAt (by simp))
        (hyq.mdifferentiableAt (by simp))] at hd
    intro u v huv
    apply hd
    exact congrArg (mfderiv 𝓘(Real, Real) (𝓡 2) (e ∘ arc) (y q)) huv

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior
