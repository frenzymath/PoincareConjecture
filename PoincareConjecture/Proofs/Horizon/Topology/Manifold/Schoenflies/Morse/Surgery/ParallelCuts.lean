import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.Clearance
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Hemisphere



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : EuclideanSpace Real (Fin 2)) 1
private abbrev S2 := sphere (0 : E3) 1



theorem exists_parallel_cutting_disks
    {f : S2 -> E3} (hf : Continuous f) (hinj : Function.Injective f)
    {v : E3} (hv : ‖v‖ = 1) (c : Real) {ε : Real} (hε : 0 < ε)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hsource : T.source = univ ×ˢ Ioo (-ε) ε)
    (γ : S1 -> Hemisphere.Plane v)
    (hcylinder : ∀ q t, t ∈ Ioo (-ε) ε ->
      f (T (q, t)) = (c + t) • v + (γ q : E3))
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hintersection :
      ((fun x : Hemisphere.Plane v => c • v + (A x : E3)) '' closedBall 0 1) ∩
        range f = f '' range (fun q : S1 => T (q, 0))) :
    ∃ δ : Real, 0 < δ ∧ δ < ε ∧ ∀ t ∈ Icc (-δ) δ,
      ((fun x : Hemisphere.Plane v => (c + t) • v + (A x : E3)) '' closedBall 0 1) ∩
        range f = f '' range (fun q : S1 => T (q, t)) := by
  let D := (fun x : Hemisphere.Plane v => c • v + (A x : E3)) '' closedBall 0 1
  have hD : IsCompact D := (isCompact_closedBall _ _).image
    (continuous_const.add (continuous_subtype_val.comp A.contMDiff.continuous))
  have hplane : D ⊆ {y : E3 | inner Real v y = c} := by
    rintro y ⟨x, _, rfl⟩
    simp [inner_add_right, inner_smul_right, hv,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (A x).property]
  obtain ⟨δ, hδ, hδε, W, _, hDW, hclear⟩ := exists_regular_tube_disk_clearance
    hf hinj hv (r := ε / 2) (by positivity) (by linarith) T hsource rfl hD hplane hintersection
  refine ⟨δ, hδ, by linarith, ?_⟩
  intro t ht
  have htε : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  ext y
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hyf⟩
    obtain ⟨z, hz, hzv⟩ := hDW (show c • v + (A x : E3) ∈ D from ⟨x, hx, rfl⟩)
    have hyclear : y ∈ ((fun w : {y : E3 | inner Real v y = c} × Real =>
        (w.1 : E3) + w.2 • v) '' (W ×ˢ Icc (-δ) δ)) ∩ range f := by
      refine ⟨⟨(z, t), ⟨hz, ht⟩, ?_⟩, hyf⟩
      change (z : E3) + t • v = y
      rw [hzv]
      calc
        c • v + (A x : E3) + t • v = (c + t) • v + (A x : E3) := by module
        _ = y := hxy
    obtain ⟨p, ⟨⟨q, u⟩, hu, hTp⟩, hpy⟩ := hclear hyclear
    have huε : u ∈ Ioo (-ε) ε := ⟨by linarith [hu.2.1], by linarith [hu.2.2]⟩
    have hTy : f (T (q, u)) = y := congrArg f hTp |>.trans hpy
    have hut : u = t := by
      have heq := congrArg (inner Real v) (hTy.trans hxy.symm)
      rw [hcylinder q u huε] at heq
      simpa [inner_add_right, inner_smul_right, hv,
        Submodule.mem_orthogonal_singleton_iff_inner_right.mp (γ q).property,
        Submodule.mem_orthogonal_singleton_iff_inner_right.mp (A x).property] using heq
    subst u
    exact ⟨T (q, t), mem_range_self q, hTy⟩
  · rintro ⟨p, ⟨q, rfl⟩, rfl⟩
    have hγ : γ q ∈ A '' sphere (0 : Hemisphere.Plane v) 1 :=
      hboundary.symm ▸ mem_range_self q
    obtain ⟨x, hx, hAx⟩ := hγ
    refine ⟨⟨x, sphere_subset_closedBall hx, ?_⟩, mem_range_self _⟩
    change (c + t) • v + (A x : E3) = f (T (q, t))
    rw [hAx, hcylinder q t htε]

end Poincare.Manifold.Schoenflies
