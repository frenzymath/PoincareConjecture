import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.LocallyInjectiveFiberDescent
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Affine.ContinuousAffineMap
import Mathlib.Topology.Separation.Hausdorff

/-!

# Factoring original compact affine cell lifts

Every lift of a compact convex affine cell through a locally
injective Hausdorff projection factors through the exact
original affine image. Original source values and the whole
range are retained, including collapsed and empty cells.
See Hatcher, Theorem 3.1, p. 45 and the fixed finite marking
argument in M76 derivation 270.
-/

set_option autoImplicit false

open Set Topology

namespace IsLocallyInjective

/-- A continuous lift of an actual compact convex affine cell
factors through its unchanged affine image. Convex fibers give
constancy and the compact image quotient gives continuity.
The projection need only be locally injective. See Hatcher
Theorem 3.1, p. 45 and M76 derivation 270. -/
theorem exists_compact_affine_image_factorization
    {U V E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace E] [T2Space E]
    {p : E → V} (hp : IsLocallyInjective p)
    {s : Set U} (hs : IsCompact s) (hsconv : Convex ℝ s)
    (F : U →ᴬ[ℝ] V) (g : C(s, E)) (hg : ∀ u, p (g u) = F u) :
    ∃ k : C(F '' s, E), (∀ v, p (k v) = (v : V)) ∧
      (∀ u : s, k ⟨F u, ⟨u, u.property, rfl⟩⟩ = g u) ∧ range k = range g := by
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let a : C(s, F '' s) :=
    ⟨fun u => ⟨F u, ⟨u, u.property, rfl⟩⟩,
      (F.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hasurj : Function.Surjective a := by
    rintro ⟨v, u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩
  have hquot : IsQuotientMap a := .of_surjective_continuous hasurj a.continuous
  have hfiber (v : F '' s) : IsPreconnected (a ⁻¹' {v}) := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    have heq : ((↑) : s → U) '' (a ⁻¹' {v}) = s ∩ F ⁻¹' {(v : V)} := by
      ext u
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.property, congrArg Subtype.val (show a z = v from hz)⟩
      · rintro ⟨hu, hFu⟩
        exact ⟨⟨u, hu⟩, Subtype.ext hFu, rfl⟩
    rw [heq]
    exact (hsconv.inter ((convex_singleton (v : V)).affine_preimage F.toAffineMap)).isPreconnected
  exact hp.exists_factorization_of_preconnected_fibers a hquot hfiber
    (fun v : F '' s => (v : V)) g hg

end IsLocallyInjective
