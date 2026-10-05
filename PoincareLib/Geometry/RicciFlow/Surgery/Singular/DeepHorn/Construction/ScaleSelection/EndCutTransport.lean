import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.HeightSelection.Levels
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Supported transport of an actual horn end cut

Morgan--Tian Theorem 11.31, printed pp. 291-292, and Corollary 11.36,
printed p. 292, retain the escaping side of the selected sphere. A
homeomorphism supported in a compact high-curvature subset of the proper
horn transports every field of that end cut. Definition 11.25, p. 283,
supplies the proper-tail input. Proposition A.11(4), pp. 503-504, supplies
the sphere homeomorphism in the later nearby-neck application.

The proper-tail argument is the owned rederivation of the read-only donor
`StrongHorn.exists_tail_avoiding_compact` in DeepHorn `Geometry/Levels`.
The supported transport itself is derived in
`proof-work/tasks/M32/derivations/end-cut-topology.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M32

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon delta delta' rho : ℝ}
  {E : GeneralizedFlowExtension F T}
  (horn : StrongHorn E epsilon) (N : TerminalStrongNeck E delta)
  (N' : TerminalStrongNeck E delta')
  (e : (E.extended.slice T).carrier ≃ₜ (E.extended.slice T).carrier)
  (K : Set (E.extended.slice T).carrier) (hK : IsCompact K)
  (hKH : K ⊆ horn.carrier)
  (hKL : Disjoint K {x | (E.extended.connection T).scalarCurvature x ≤ rho⁻¹ ^ 2})
  (hfix : ∀ x, x ∉ K → e x = x)
  (hsphere : e '' N.central_sphere = N'.central_sphere)

/-- Changing the neck accuracy while preserving its actual central sphere
retains the same end cut (Corollary 11.36, printed p. 292). -/
def hornEndCut_of_centralSphere_eq (hsphere : N.central_sphere = N'.central_sphere)
    (cut : HornEndCut horn N rho) : HornEndCut horn N' rho where
  point := cut.point
  point_mem := hsphere ▸ cut.point_mem
  carrier := cut.carrier
  component_eq := hsphere ▸ cut.component_eq
  tail_level := cut.tail_level
  tail_level_nonneg := cut.tail_level_nonneg
  tail_level_lt_one := cut.tail_level_lt_one
  contains_tail := cut.contains_tail
  escapes_compact := cut.escapes_compact
  disjoint_low_curvature := cut.disjoint_low_curvature

include e K hK hKH hKL hfix hsphere

/-- Transport the actual escaping component through a homeomorphism fixed
outside a compact high-curvature part of the horn (Corollary 11.36, p. 292).
The source and target neck accuracies may differ. -/
noncomputable def hornEndCut_transport (cut : HornEndCut horn N rho) :
    HornEndCut horn N' rho := by
  have hsymmfix : ∀ x, x ∉ K → e.symm x = x := by
    intro x hx
    exact e.symm_apply_eq.mpr (hfix x hx).symm
  have hmaps (f : (E.extended.slice T).carrier ≃ₜ (E.extended.slice T).carrier)
      (hf : ∀ x, x ∉ K → f x = x) : MapsTo f horn.carrier horn.carrier := by
    intro x hx
    by_contra hnot
    have hfixed := hf (f x) (fun hk => hnot (hKH hk))
    have heq : f x = x := f.injective hfixed
    exact hnot (heq.symm ▸ hx)
  have hH : e '' horn.carrier = horn.carrier := by
    apply Subset.antisymm (image_subset_iff.mpr (hmaps e hfix))
    intro x hx
    exact ⟨e.symm x, hmaps e.symm hsymmfix hx, e.apply_symm_apply x⟩
  have hdiff : e '' (horn.carrier \ N.central_sphere) =
      horn.carrier \ N'.central_sphere := by
    rw [image_sdiff e.injective, hH, hsphere]
  let b := Classical.choose (horn_exists_tail_avoiding_compact horn K hK)
  have hb1 : b < 1 := (Classical.choose_spec (horn_exists_tail_avoiding_compact horn K hK)).2.1
  have hb : ∀ s : UnitTwoSphere, ∀ t : ℝ, b < t → t < 1 →
      horn.parameterization (s, t) ∉ K :=
    (Classical.choose_spec (horn_exists_tail_avoiding_compact horn K hK)).2.2
  exact {
    point := e cut.point
    point_mem := hdiff ▸ mem_image_of_mem e cut.point_mem
    carrier := e '' cut.carrier
    component_eq := by
      rw [cut.component_eq, e.image_connectedComponentIn cut.point_mem, hdiff]
    tail_level := max cut.tail_level b
    tail_level_nonneg := cut.tail_level_nonneg.trans (le_max_left _ _)
    tail_level_lt_one := max_lt cut.tail_level_lt_one hb1
    contains_tail := by
      rintro x ⟨⟨s, t⟩, ⟨_, ht, ht1⟩, rfl⟩
      have hcut := cut.contains_tail
        ⟨(s, t), ⟨mem_univ _, (le_max_left _ _).trans_lt ht, ht1⟩, rfl⟩
      exact ⟨horn.parameterization (s, t), hcut,
        hfix _ (hb s t ((le_max_right _ _).trans_lt ht) ht1)⟩
    escapes_compact := by
      intro A hA hsub
      apply cut.escapes_compact (e.symm '' A) (hA.image e.symm.continuous)
      intro x hx
      exact ⟨e x, hsub ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
    disjoint_low_curvature := disjoint_left.mpr (by
      rintro y ⟨x, hx, rfl⟩ hy
      have hfixed := hfix (e x) (fun hk => disjoint_left.mp hKL hk hy)
      have heq : e x = x := e.injective hfixed
      exact disjoint_left.mp cut.disjoint_low_curvature hx (heq ▸ hy)) }

/-- The transported cut uses exactly the image of the original carrier
(Corollary 11.36, printed p. 292). -/
@[simp] theorem hornEndCut_transport_carrier (cut : HornEndCut horn N rho) :
    (hornEndCut_transport horn N N' e K hK hKH hKL hfix hsphere cut).carrier =
      e '' cut.carrier := rfl

/-- Supported sphere transport preserves existence of the actual low-avoiding
end cut in both directions (Corollary 11.36, printed p. 292). -/
theorem hornEndCut_nonempty_iff_of_compact_transport :
    Nonempty (HornEndCut horn N rho) ↔ Nonempty (HornEndCut horn N' rho) := by
  constructor
  · rintro ⟨cut⟩
    exact ⟨hornEndCut_transport horn N N' e K hK hKH hKL hfix hsphere cut⟩
  · rintro ⟨cut⟩
    have hsymmfix : ∀ x, x ∉ K → e.symm x = x := by
      intro x hx
      exact e.symm_apply_eq.mpr (hfix x hx).symm
    have hsphere' : e.symm '' N'.central_sphere = N.central_sphere := by
      rw [← hsphere, e.image_symm, e.preimage_image]
    exact ⟨hornEndCut_transport horn N' N e.symm K hK hKH hKL hsymmfix hsphere' cut⟩

end PoincareMT.M32
