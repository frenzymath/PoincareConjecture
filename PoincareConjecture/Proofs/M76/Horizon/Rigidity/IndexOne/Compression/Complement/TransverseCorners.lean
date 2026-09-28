import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.Corners










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))


theorem exists_transverse_marked_corner_of_supported_map
    {α : Type*} (e : α → OpenPartialHomeomorph X V3)
    (phi psi : C(H, H)) {K : Set X} (hK : IsClosed K) (hKR : K ⊆ interior R)
    (hfixed : ∀ z : H,
      ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm z : X) ∉ K → psi z = phi z)
    (u v : ℝ) (theta : C) {x : X} (hx : x ∈ frontier R)
    (hchart : ∃ (ell lambda : V3 →ᴬ[ℝ] ℝ) (w t : V3)
        (G : OpenPartialHomeomorph X V3),
      ell.contLinear w = 1 ∧ ell.contLinear t = 0 ∧ lambda.contLinear t = 1 ∧
      x ∈ G.source ∧ ell (G x) = 0 ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ G.source, y ∈ sourceSlab phi u v ↔ 0 ≤ ell (G y)) ∧
      (∀ y ∈ G.source, y ∈ sourceSlab phi u v ∩ frontier R ↔
        ell (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
      ∀ y ∈ G.source, y ∈ sourceSurface phi theta ↔
        ell (G y) = 0 ∧ lambda (G y) ≤ 0) :
    ∃ (ell lambda : V3 →ᴬ[ℝ] ℝ) (w t : V3) (G : OpenPartialHomeomorph X V3),
      ell.contLinear w = 1 ∧ ell.contLinear t = 0 ∧ lambda.contLinear t = 1 ∧
      x ∈ G.source ∧ ell (G x) = 0 ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ G.source, y ∈ sourceSlab psi u v ↔ 0 ≤ ell (G y)) ∧
      (∀ y ∈ G.source, y ∈ sourceSlab psi u v ∩ frontier R ↔
        ell (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
      ∀ y ∈ G.source, y ∈ sourceSurface psi theta ↔
        ell (G y) = 0 ∧ lambda (G y) ≤ 0 := by
  have hxK : x ∈ Kᶜ := fun h => hx.2 (hKR h)
  obtain ⟨ell, lambda, w, t, G, hw, het, hlt, hxG, hz, hG, hslab, hold, hphase⟩ := hchart
  refine ⟨ell, lambda, w, t, G.restrOpen Kᶜ hK.isOpen_compl,
    hw, het, hlt, ⟨hxG, hxK⟩, hz, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (e i).piecewiseAffine_compatible_restrOpen_right G (hG i) hK.isOpen_compl
  · intro y hy
    exact (sourceSlab_agrees_off_support phi psi hfixed u v y hy.2).trans (hslab y hy.1)
  · intro y hy
    exact (and_congr_left (fun _ =>
      sourceSlab_agrees_off_support phi psi hfixed u v y hy.2)).trans (hold y hy.1)
  · intro y hy
    exact (sourceSurface_agrees_off_support phi psi hfixed theta y hy.2).trans
      (hphase y hy.1)

end PoincareConjecture.M76.HamiltonIntervalTorus
