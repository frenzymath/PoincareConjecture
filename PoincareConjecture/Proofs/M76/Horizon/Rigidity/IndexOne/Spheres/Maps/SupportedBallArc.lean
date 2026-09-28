import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Maps.BallArcHomotopy
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedProductPasting









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Q" => hamiltonOneHierarchyCoordinates



theorem exists_supported_ball_phase_clamp {ι : Type*}
    {e : ι → OpenPartialHomeomorph X V3} {D S : Set X}
    (b : ChartwisePLBall e D S) (f : C(X, H))
    (boundary : C({x : D | (x : X) ∈ S}, ℝ))
    (hboundary : ∀ x : {x : D | (x : X) ∈ S},
      (boundary x : C) = (Q (f x)).2)
    (lower upper : ℝ) (horder : lower ≤ upper)
    (hboundaryRange : ∀ x, boundary x ∈ Icc lower upper) :
    ∃ (g : C(X, H)) (T : f.HomotopyRel g (interior D)ᶜ),
      (∀ (t : unitInterval) (x : X), (Q (T (t, x))).1 = (Q (f x)).1) ∧
      (∀ x : X, g x = f x ∨ g x = handlePhaseRetraction lower (f x) ∨
        g x = handlePhaseRetraction upper (f x)) ∧
    ∀ x ∈ D, (Q (g x)).2 ∈ ((↑) : ℝ → C) '' Icc lower upper := by
  classical
  let h := (Homeomorph.refl (Fin 1 → ℝ)).prodCongr (hamiltonLowerLatticePiEquiv (Fin 2))
  let : T2Space X := h.isEmbedding.t2Space
  let u : C(D, H) := f.comp ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨v, W, hWcoord, hvchoice, hvrange⟩ :=
    exists_ball_phase_clamp b u boundary hboundary lower upper horder hboundaryRange
  let outer : C(unitInterval × X, H) := f.comp ⟨Prod.snd, continuous_snd⟩
  obtain ⟨G, hGin, hGout⟩ := ContinuousMap.exists_paste_of_eq_on_frontier
    b.isCompact.isClosed W.toHomotopy.toContinuousMap outer (by
      intro t x hx
      have hxS : (x : X) ∈ S := by rwa [b.frontier_eq] at hx
      exact W.eq_fst t hxS)
  let g : C(X, H) := ⟨fun x => G (1, x), G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hzero (x : X) : G (0, x) = f x := by
    by_cases hx : x ∈ D
    · exact (hGin 0 ⟨x, hx⟩).trans (W.apply_zero ⟨x, hx⟩)
    · exact hGout 0 x (fun h => hx (interior_subset h))
  let T : f.HomotopyRel g (interior D)ᶜ := {
    toFun := G
    continuous_toFun := G.continuous
    map_zero_left := hzero
    map_one_left := fun _ => rfl
    prop' := fun t x hx => hGout t x hx }
  have hg (x : D) : g x = v x := (hGin 1 x).trans (W.apply_one x)
  refine ⟨g, T, ?_, ?_, ?_⟩
  · intro t x
    change (Q (G (t, x))).1 = _
    by_cases hx : x ∈ D
    · rw [hGin t ⟨x, hx⟩]
      exact hWcoord t ⟨x, hx⟩
    · rw [hGout t x (fun h => hx (interior_subset h))]
      rfl
  · intro x
    by_cases hx : x ∈ D
    · rw [hg ⟨x, hx⟩]
      exact hvchoice ⟨x, hx⟩
    · exact Or.inl (hGout 1 x (fun h => hx (interior_subset h)))
  · intro x hx
    rw [hg ⟨x, hx⟩]
    exact hvrange ⟨x, hx⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
