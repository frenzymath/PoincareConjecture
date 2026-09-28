import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneCoreExterior
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneCoverCoordinates
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneFilling
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneSquareCircle










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (ℝ × V2)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "Q" => sphere (0 : V2) 1
local notation "C8" => AddCircle (4 * (2 : ℝ))
local notation "Shell" => Set.prod (Icc (-1 : ℝ) 1)
  (Set.preimage (norm : V2 → ℝ) (Icc (1 : ℝ) 2))


noncomputable def meridianProductCoordinates : V ≃ᴬ[ℝ] W :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toContinuousAffineEquiv


theorem meridianProductCoordinates_apply (x : V) :
    meridianProductCoordinates x = (x.1, (x.2 0, x.2 1)) := rfl



theorem squareCircle_zero : (squareCircle (0 : C8) : V2) = ![-1, -1] := by
  have hm : PLAnnularStrip.annulusMap 2 (by norm_num) (0, 0) = (0, 0) := by
    change PLAnnularStrip.annulusMap 2 (by norm_num)
      (((0 : ℝ) : C8), (0 : ℝ)) = (0, 0)
    rw [PLAnnularStrip.annulusMap_coe (by norm_num : (0 : ℝ) < 2)
      (by norm_num : 4 * |(0 : ℝ)| < 2)
      (by norm_num : (0 : ℝ) ∈ Icc 0 (4 * 2))]
    have hb := PLAnnularStrip.wrappedStripMap_block
      (by norm_num : 4 * |(0 : ℝ)| < 2)
      (by norm_num : (0 : ℝ) ∈ Icc 0 2) (0 : Fin 4)
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, zero_add] at hb
    rw [hb]
    change (PLAnnularStrip.coordinate 2 0 0, 0) = (0, 0)
    rw [(PLAnnularStrip.coordinate_endpoints
      (by norm_num : 4 * |(0 : ℝ)| < 2)).1]
  rw [squareCircle_apply]
  change ![-1 + (PLAnnularStrip.annulusMap 2 (by norm_num) (0, 0)).1,
    -1 + (PLAnnularStrip.annulusMap 2 (by norm_num) (0, 0)).2] = ![-1, -1]
  rw [hm]
  norm_num





theorem exists_physical_retracted_disk_filling
    (A : W ≃ₜ W) (hAL : A '' squareBlock = squareBlock)
    (E1 : Set W) (hE1 : E1 ⊆ coreExterior (A '' squareUnitBlock))
    (r : C(coreExterior (A '' squareUnitBlock), E1))
    (hfix : ∀ x : coreExterior (A '' squareUnitBlock),
      (x : W) ∈ E1 → (r x : W) = x)
    (gamma : C(Q, E1)) (ell : C(Q, ℝ))
    (hangle : ∀ u : Q,
      (A.symm (gamma u : W)).2 = ‖(A.symm (gamma u : W)).2‖ •
        ((squareCircle ((ell u : ℝ) : C8) : V2) 0,
          (squareCircle ((ell u : ℝ) : C8) : V2) 1)) :
    ∃ F : C(closedBall (0 : V2) 1, E1),
      ∀ u : Q, F ⟨u, sphere_subset_closedBall u.property⟩ = gamma u := by
  let a := meridianProductCoordinates
  let c := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let A' := a.toHomeomorph.trans (A.trans a.symm.toHomeomorph)
  let D : Set V := a ⁻¹' E1
  have haShell (x : V) : a x ∈ squareCoreShell ↔ x ∈ Shell := by
    change (x.1 ∈ Icc (-1 : ℝ) 1 ∧ ‖(x.2 0, x.2 1)‖ ∈ Icc (1 : ℝ) 2) ↔ _
    rw [freeCoordinates_norm]
    rfl
  have himage : a '' (A' '' Shell) = coreExterior (A '' squareUnitBlock) := by
    rw [coreExterior_image_unit A hAL]
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨a x, (haShell x).mpr hx, ?_⟩
      change A (a x) = a (a.symm (A (a x)))
      rw [a.apply_symm_apply]
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨A' (a.symm x), ⟨a.symm x, ?_, rfl⟩, ?_⟩
      · exact (haShell _).mp ((a.apply_symm_apply x).symm ▸ hx)
      · change a (a.symm (A (a (a.symm x)))) = A x
        rw [a.apply_symm_apply, a.apply_symm_apply]
  let e0 : (A' '' Shell) ≃ₜ coreExterior (A '' squareUnitBlock) :=
    (a.toHomeomorph.image (A' '' Shell)).trans (Homeomorph.setCongr himage)
  let e1 : D ≃ₜ E1 := (a.toHomeomorph.image D).trans
    (Homeomorph.setCongr (a.toHomeomorph.image_preimage E1))
  have hD : D ⊆ A' '' Shell := by
    intro x hx
    have hy : a x ∈ a '' (A' '' Shell) := himage.symm ▸ hE1 hx
    exact a.injective.mem_set_image.mp hy
  let r' : C(A' '' Shell, D) :=
    (⟨e1.symm, e1.symm.continuous⟩ : C(E1, D)).comp
      (r.comp ⟨e0, e0.continuous⟩)
  have hr' (x : A' '' Shell) (hx : (x : V) ∈ D) : (r' x : V) = x := by
    apply a.injective
    change a (a.symm (r (e0 x) : W)) = a (x : V)
    rw [a.apply_symm_apply]
    exact hfix (e0 x) hx
  let gamma' : C(Q, D) := (⟨e1.symm, e1.symm.continuous⟩ : C(E1, D)).comp gamma
  let zeta : C(ℝ, Q) :=
    ⟨fun t => squareCircle ((t : ℝ) : C8),
      squareCircle.continuous.comp (AddCircle.continuous_mk' _)⟩
  have hnorm (w : ℝ × ℝ) : ‖c.symm w‖ = ‖w‖ := by
    have h := freeCoordinates_norm (c.symm w)
    change ‖c (c.symm w)‖ = ‖c.symm w‖ at h
    rw [c.apply_symm_apply] at h
    exact h.symm
  have hAinv (u : Q) : A'.symm (gamma' u : V) = a.symm (A.symm (gamma u : W)) := by
    change a.symm (A.symm (a (a.symm (gamma u : W)))) = _
    rw [a.apply_symm_apply]
  have hpolar (u : Q) : (A'.symm (gamma' u : V)).2 =
      ‖(A'.symm (gamma' u : V)).2‖ • (zeta (ell u) : V2) := by
    rw [hAinv]
    change c.symm (A.symm (gamma u : W)).2 =
      ‖c.symm (A.symm (gamma u : W)).2‖ • (squareCircle ((ell u : ℝ) : C8) : V2)
    rw [hnorm]
    have h := congrArg c.symm (hangle u)
    change c.symm (A.symm (gamma u : W)).2 =
      c.symm (‖(A.symm (gamma u : W)).2‖ •
        c (squareCircle ((ell u : ℝ) : C8) : V2)) at h
    simpa only [map_smul, c.symm_apply_apply] using h
  obtain ⟨F, hF⟩ := exists_retracted_disk_filling_of_real_angular_lift
    A' D hD r' hr' gamma' zeta ell hpolar
  refine ⟨(⟨e1, e1.continuous⟩ : C(D, E1)).comp F, ?_⟩
  intro u
  change e1 (F ⟨u, sphere_subset_closedBall u.property⟩) = gamma u
  rw [hF]
  exact e1.apply_symm_apply (gamma u)

end PoincareConjecture.M76.HamiltonIndexOne
