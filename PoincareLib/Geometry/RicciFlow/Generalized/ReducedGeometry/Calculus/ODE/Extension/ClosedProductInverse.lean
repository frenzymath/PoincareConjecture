import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ReducedLength
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Differential.TimePreservingRelativeInverse
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.TriangularBijective
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# A relative inverse from an invertible spatial slice

The derivative of a map with identity time component is triangular.
Its spatial block is the actual ordinary derivative of the fixed-time
slice, even at a closed time endpoint. Morgan-Tian Proposition 6.28,
p. 117; see tasks/M14/derivations/2026-09-21-relative-inverse.md.
-/

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareMT.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

set_option backward.isDefEq.respectTransparency false in
/-- A smooth spatial map on an open-by-convex time tube with an
invertible fixed-time derivative has a smooth time-preserving relative
inverse, including at closed time endpoints. The triangular algebra
is M09's proved generic lemma, used for Proposition 6.28, p. 117. -/
theorem exists_closedProduct_inverse {q : E × ℝ → F} {U : Set E} {C : Set ℝ}
    (hU : IsOpen U) (hUc : Convex ℝ U) (hC : Convex ℝ C) (hCd : UniqueDiffOn ℝ C)
    (hq : ContDiffOn ℝ ∞ q (U ×ˢ C)) {x : E} (hx : x ∈ U) {t : ℝ} (ht : t ∈ C)
    (hbij : Function.Bijective (fderiv ℝ (fun z => q (z, t)) x)) :
    ∃ V : Set (E × ℝ), IsOpen V ∧ (x, t) ∈ V ∧
      ∃ g : (E × ℝ) ≃ₜ (F × ℝ),
        EqOn (fun z => (q z, z.2)) g (V ∩ (U ×ˢ C)) ∧
        (∀ z, (g z).2 = z.2) ∧
        ContDiffOn ℝ ∞ g.symm (g '' (V ∩ (U ×ˢ C))) := by
  let S := U ×ˢ C
  have hS : UniqueDiffOn ℝ S := hU.uniqueDiffOn.prod hCd
  have hqs := (hq.differentiableOn (by simp) (x, t) ⟨hx, ht⟩).hasFDerivWithinAt
  let A := fderivWithin ℝ q S (x, t)
  let L : (E × ℝ) →L[ℝ] (F × ℝ) := A.prod (ContinuousLinearMap.snd ℝ E ℝ)
  have hder : HasFDerivWithinAt (fun z : E × ℝ => (q z, z.2)) L S (x, t) :=
    hqs.prodMk hasFDerivAt_snd.hasFDerivWithinAt
  have hpair : HasFDerivAt (fun z : E => (z, t))
      ((ContinuousLinearMap.id ℝ E).prod 0) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  have hslice : HasFDerivWithinAt (fun z => q (z, t))
      (A.comp ((ContinuousLinearMap.id ℝ E).prod 0)) U x :=
    hqs.comp x hpair.hasFDerivWithinAt
      (show MapsTo (fun z : E => (z, t)) U (U ×ˢ C) from fun _ hz => ⟨hz, ht⟩)
  have hspace (W : E) : (L (W, 0)).1 = fderiv ℝ (fun z => q (z, t)) x W := by
    rw [(hslice.hasFDerivAt (hU.mem_nhds hx)).fderiv]
    rfl
  have hbL : Function.Bijective L :=
    (Proofs.M09.triangular_bijective_iff L _ (fun _ => rfl) hspace).mpr hbij
  let e : (E × ℝ) ≃L[ℝ] (F × ℝ) :=
    (LinearEquiv.ofBijective L.toLinearMap hbL).toContinuousLinearEquiv
  have he : (e : (E × ℝ) →L[ℝ] (F × ℝ)) = L := ContinuousLinearMap.ext (fun _ => rfl)
  obtain ⟨V, hV, hxV, g, hgf, hgt, hgs, _⟩ := exists_timePreserving_relative_inverse
    (hUc.prod hC) hS (hq.prodMk contDiffOn_snd) (fun _ _ => rfl) ⟨hx, ht⟩ e
    (he.trans (hder.fderivWithin (hS (x, t) ⟨hx, ht⟩)).symm) (fun _ => rfl)
  exact ⟨V, hV, hxV, g, hgf, hgt, hgs⟩

end PoincareMT.M14
