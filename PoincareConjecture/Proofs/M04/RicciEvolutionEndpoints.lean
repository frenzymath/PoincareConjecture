import PoincareConjecture.Definitions.Ch03.RicciFlow
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv








set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
private theorem contDiffOn_metric_pairing_timeSlice (F : RicciFlow n M J)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    ContDiffOn ℝ ∞ (fun t ↦ (F.metric t).inner x u v) J := by
  let E := EuclideanSpace ℝ (Fin n)
  have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun t : ℝ ↦ (t, x)) := contMDiff_id.prodMk contMDiff_const
  have hfamily := F.smooth.comp hslice.contMDiffOn
    (show MapsTo (fun t : ℝ ↦ (t, x)) J (J ×ˢ univ) from
      fun _ ht ↦ ⟨ht, mem_univ x⟩)
  have hm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t ↦ (F.metric t).inner x u v) J := by
    intro t ht
    have he : ContMDiffWithinAt 𝓘(ℝ, ℝ) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (fun s ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
          x ((F.metric s).inner x u v)) J t :=
      (hfamily t ht).clm_bundle_apply₂
        (contMDiffWithinAt_const (c := Bundle.TotalSpace.mk' E x u))
        (contMDiffWithinAt_const (c := Bundle.TotalSpace.mk' E x v))
    simp only [Bundle.contMDiffWithinAt_totalSpace] at he
    exact he.2
  exact hm.contDiffOn

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency false in
theorem contDiffOn_ricci_timeSlice (F : RicciFlow n M J)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    ContDiffOn ℝ ∞ (fun t ↦ (F.connection t).ricci x u v) J := by
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex F.interval.convex
    (F.interval.convex.nontrivial_iff_nonempty_interior.mp F.nontrivial)
  have hm := contDiffOn_metric_pairing_timeSlice F x u v
  have hd : ContDiffOn ℝ ∞
      (derivWithin (fun t ↦ (F.metric t).inner x u v) J) J :=
    hm.derivWithin hJ (by simp)
  have hs : ContDiffOn ℝ ∞
      (fun t ↦ (-1 / 2 : ℝ) * derivWithin (fun s ↦ (F.metric s).inner x u v) J t) J :=
    contDiffOn_const.mul hd
  apply hs.congr
  intro t ht
  have he := (F.equation t ht x u v).derivWithin (hJ t ht)
  linarith

theorem ricci_timeDerivative_extend (F : RicciFlow n M J)
    (x : M) (u v : TangentSpace (𝓡 n) x) (w : ℝ → ℝ)
    (hw : ContinuousOn w J)
    (hi : ∀ t ∈ interior J,
      HasDerivAt (fun s ↦ (F.connection s).ricci x u v) (w t) t) :
    ∀ t ∈ J, HasDerivWithinAt (fun s ↦ (F.connection s).ricci x u v) (w t) J t := by
  let f := fun t ↦ (F.connection t).ricci x u v
  have hf : ContDiffOn ℝ ∞ f J := contDiffOn_ricci_timeSlice F x u v
  have hconv : Convex ℝ J := F.interval.convex
  have hne : (interior J).Nonempty := hconv.nontrivial_iff_nonempty_interior.mp F.nontrivial
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex hconv hne
  have hdense : J ⊆ closure (interior J) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure
  have hinside : EqOn (derivWithin f J) w (interior J) := by
    intro t ht
    exact (hi t ht).hasDerivWithinAt.derivWithin (hJ t (interior_subset ht))
  have heq : EqOn (derivWithin f J) w J := hinside.of_subset_closure
    (hf.continuousOn_derivWithin hJ (by simp)) hw interior_subset hdense
  intro t ht
  exact ((hf t ht).differentiableWithinAt (by simp)).hasDerivWithinAt.congr_deriv (heq ht)

end PoincareConjecture.M04

