import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false

open Set Metric Geometry

namespace Set

local notation "V3" => (Fin 3 → ℝ)

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

theorem IsFinitePLBallPair.exists_open_cube_interior_chart {A B T : Set E}
    (hA : IsFinitePLBallPair W A B) (c : W ≃L[ℝ] V3) (hAT : A ⊆ T)
    (hopen : IsOpen ((Subtype.val : T → E) ⁻¹' (A \ B))) :
    ∃ (e : OpenPartialHomeomorph T V3) (f : E → V3) (g : V3 → E),
      e.source = (Subtype.val : T → E) ⁻¹' (A \ B) ∧
      e.target = interior (closedBall (0 : V3) 1) ∧
      FinitePiecewiseAffineOn f A ∧
      FinitePiecewiseAffineOn g (closedBall (0 : V3) 1) ∧
      (∀ x : T, e x = f x) ∧
      (∀ y ∈ closedBall (0 : V3) 1, (e.symm y : E) = g y) ∧
      MapsTo g (closedBall (0 : V3) 1) A ∧
      LeftInvOn g f A ∧ RightInvOn g f (closedBall (0 : V3) 1) := by
  classical
  obtain ⟨d, hd, hdb⟩ := hA.exists_cube_chart c
  have hdi := hd.symm
  obtain ⟨f, hf, hdf⟩ := hd
  obtain ⟨g, hg, hdg⟩ := hdi
  have hfm : MapsTo f A (closedBall (0 : V3) 1) := by
    intro x hx
    rw [← hdf ⟨x, hx⟩]
    exact (d ⟨x, hx⟩).property
  have hgm : MapsTo g (closedBall (0 : V3) 1) A := by
    intro y hy
    rw [← hdg ⟨y, hy⟩]
    exact (d.symm ⟨y, hy⟩).property
  have hgf : LeftInvOn g f A := by
    intro x hx
    rw [← hdf ⟨x, hx⟩, ← hdg, d.symm_apply_apply]
  have hfg : RightInvOn g f (closedBall (0 : V3) 1) := by
    intro y hy
    rw [← hdg ⟨y, hy⟩, ← hdf, d.apply_symm_apply]
  have hb (x : E) (hx : x ∈ A) :
      x ∈ B ↔ f x ∈ frontier (closedBall (0 : V3) 1) := by
    rw [← hdf ⟨x, hx⟩]
    exact hdb ⟨x, hx⟩
  have hzero : (0 : V3) ∈ closedBall (0 : V3) 1 := mem_closedBall_self zero_le_one
  let x0 : T := ⟨g 0, hAT (hgm hzero)⟩
  let v : V3 → T := fun y =>
    if hy : y ∈ closedBall (0 : V3) 1 then ⟨g y, hAT (hgm hy)⟩ else x0
  have hv (y : V3) (hy : y ∈ closedBall (0 : V3) 1) : (v y : E) = g y := by
    dsimp only [v]
    rw [dif_pos hy]
  have hsource {x : T} (hx : x ∈ (Subtype.val : T → E) ⁻¹' (A \ B)) :
      f x ∈ interior (closedBall (0 : V3) 1) := by
    rw [← self_sdiff_frontier]
    exact ⟨hfm hx.1, fun h => hx.2 ((hb x hx.1).mpr h)⟩
  have htarget {y : V3} (hy : y ∈ interior (closedBall (0 : V3) 1)) :
      v y ∈ (Subtype.val : T → E) ⁻¹' (A \ B) := by
    change (v y : E) ∈ A \ B
    rw [hv y (interior_subset hy)]
    refine ⟨hgm (interior_subset hy), ?_⟩
    intro hB
    have hfront := (hb (g y) (hgm (interior_subset hy))).mp hB
    rw [hfg (interior_subset hy)] at hfront
    rw [← self_sdiff_frontier (closedBall (0 : V3) 1)] at hy
    exact hy.2 hfront
  let e : OpenPartialHomeomorph T V3 := {
    toFun := fun x => f x
    invFun := v
    source := (Subtype.val : T → E) ⁻¹' (A \ B)
    target := interior (closedBall (0 : V3) 1)
    map_source' := fun _ hx => hsource hx
    map_target' := fun _ hy => htarget hy
    left_inv' := by
      intro x hx
      apply Subtype.ext
      rw [hv _ (hfm hx.1), hgf hx.1]
    right_inv' := by
      intro y hy
      rw [hv _ (interior_subset hy), hfg (interior_subset hy)]
    continuousOn_toFun := hf.continuousOn.comp continuous_subtype_val.continuousOn
      (fun _ hx => hx.1)
    continuousOn_invFun := Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      ((hg.continuousOn.mono interior_subset).congr (fun y hy => hv y (interior_subset hy)))
    open_source := hopen
    open_target := isOpen_interior }
  exact ⟨e, f, g, rfl, rfl, hf, hg, fun _ => rfl, hv, hgm, hgf, hfg⟩

end Set
