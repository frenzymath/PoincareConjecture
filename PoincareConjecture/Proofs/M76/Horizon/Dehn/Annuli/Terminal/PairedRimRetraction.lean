import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.PairedMarkedModel

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable {L : Submodule ℤ V2} {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  {retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h}
  {d : ProtectedAnnulusTerminalData L retained}

noncomputable def PairedMarkedBoundary.radial (P : PairedMarkedBoundary L retained d) :
    C(P.model.complex.space, Q2) where
  toFun z := chartShellRadial L retained (d.stage.projection (P.model.homeomorph.symm z))
  continuous_toFun := (chartShellRadial L retained).continuous.comp
    (d.stage.projection.continuous.comp
      (continuous_subtype_val.comp P.model.homeomorph.symm.continuous))

theorem PairedMarkedBoundary.radial_parametrization (P : PairedMarkedBoundary L retained d)
    (b : Bool) (u : Q2) :
    P.radial ⟨P.parametrization b u, SimplicialComplex.space_subset_of_le
      ((P.rim_le b).trans P.model.boundary_le) (P.parametrization b u).property⟩ = u := by
  let N := P.model
  let v := d.stage.annulusRim d.source_space b u
  have hvN : v ∈ N.region :=
    N.source_subset (d.stage.annulusRim_range_subset d.source_space b (mem_range_self u))
  have hinv : N.homeomorph.symm ⟨P.parametrization b u,
      SimplicialComplex.space_subset_of_le ((P.rim_le b).trans N.boundary_le)
        (P.parametrization b u).property⟩ = ⟨v, hvN⟩ := by
    apply N.homeomorph.injective
    rw [N.homeomorph.apply_symm_apply]
    apply Subtype.ext
    exact (P.parametrization_value b u).trans (N.homeomorph_value ⟨v, hvN⟩).symm
  change chartShellRadial L retained (d.stage.projection (N.homeomorph.symm _)) = u
  rw [hinv]
  exact stage_radial_rim L retained d.stage d.source_space d.boundary_values b u

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
