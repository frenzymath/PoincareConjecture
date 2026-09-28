import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.OffsetRimEssentiality









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "Q2" => sphere (0 : Fin 2 → ℝ) 1
local notation "Ann" => squareAnnulus 1 (1 / 8 : ℝ)
local notation "J" => Icc (-1 : ℝ) 1

variable {E X : Type*} [NormedAddCommGroup E] [TopologicalSpace X]
  {W N S B : Set E}

theorem exists_offset_rim_projection_homotopy
    (c : Ann ≃ₜ N) (gamma : Q2 ≃ₜ S) (hSN : S ⊆ N) (hNW : N ⊆ W)
    (hcore : ∀ x : Ann, (c x : E) ∈ S ↔ depth 1 x = 0)
    (side : Bool) (hBN : B ⊆ N)
    (hlevel : ∀ x : Ann, (c x : E) ∈ B ↔
      depth 1 x = if side then (1 / 8 : ℝ) else -(1 / 8 : ℝ))
    (j : C(W, X)) :
    ∃ k : C(Q2, B),
      (j.comp ((ContinuousMap.inclusion (hBN.trans hNW)).comp k)).Homotopic
        (j.comp ((ContinuousMap.inclusion (hSN.trans hNW)).comp (gamma : C(Q2, S)))) := by
  obtain ⟨e, _, he⟩ := PoincareConjecture.M76.exists_finitePL_square_annulus_cylinder
  let g : C(Q2, N) := ⟨fun u ↦ ⟨gamma u, hSN (gamma u).property⟩,
    (continuous_subtype_val.comp gamma.continuous).subtype_mk _⟩
  let q : C(Q2, Q2 ×ˢ J) :=
    ⟨fun u ↦ e (c.symm (g u)), e.continuous.comp (c.symm.continuous.comp g.continuous)⟩
  have hqzero (u : Q2) : (q u : (Fin 2 → ℝ) × ℝ).2 = 0 := by
    change (e (c.symm (g u)) : (Fin 2 → ℝ) × ℝ).2 = 0
    rw [he, (hcore (c.symm (g u))).mp (by
      rw [c.apply_symm_apply]
      exact (gamma u).property), mul_zero]
  let a : ℝ := if side then 1 else -1
  have hta (t : unitInterval) : (t : ℝ) * a ∈ J := by
    cases side <;> simp only [a, Bool.false_eq_true, if_false, if_true, mul_one, mul_neg_one]
    all_goals constructor <;> linarith [t.property.1, t.property.2]
  let p : C(unitInterval × Q2, Q2 ×ˢ J) := {
    toFun := fun z ↦ ⟨((q z.2 : (Fin 2 → ℝ) × ℝ).1, (z.1 : ℝ) * a),
      (q z.2).property.1, hta z.1⟩
    continuous_toFun := by fun_prop }
  let m : C(unitInterval × Q2, N) :=
    ⟨fun z ↦ c (e.symm (p z)), c.continuous.comp (e.symm.continuous.comp p.continuous)⟩
  have hm0 (u : Q2) : m (0, u) = g u := by
    have hp : p (0, u) = q u := by
      apply Subtype.ext
      change ((q u : (Fin 2 → ℝ) × ℝ).1, (0 : ℝ) * a) = (q u).val
      apply Prod.ext
      · rfl
      · change (0 : ℝ) * a = (q u : (Fin 2 → ℝ) × ℝ).2
        rw [zero_mul, hqzero]
    change c (e.symm (p (0, u))) = g u
    rw [hp]
    exact (congrArg c (e.symm_apply_apply _)).trans (c.apply_symm_apply _)
  have hmB (u : Q2) : (m (1, u) : E) ∈ B := by
    apply (hlevel _).mpr
    have ht := he (e.symm (p (1, u)))
    rw [e.apply_symm_apply] at ht
    change (1 : ℝ) * a = 8 * depth 1 (e.symm (p (1, u))) at ht
    cases side <;> simp only [a, Bool.false_eq_true, if_false, if_true] at ht ⊢ <;> linarith
  let k : C(Q2, B) := ⟨fun u ↦ ⟨m (1, u), hmB u⟩,
    (continuous_subtype_val.comp
      (m.continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk _⟩
  refine ⟨k, ⟨?_⟩⟩
  exact {
    toFun := fun z ↦ j ⟨m (unitInterval.symm z.1, z.2),
      hNW (m (unitInterval.symm z.1, z.2)).property⟩
    continuous_toFun := j.continuous.comp ((continuous_subtype_val.comp
      (m.continuous.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk
        continuous_snd))).subtype_mk _)
    map_zero_left := by intro u; simp only [unitInterval.symm_zero]; rfl
    map_one_left := by
      intro u
      simp only [unitInterval.symm_one]
      exact (congrArg j (Subtype.ext (congrArg (fun x : N ↦ (x : E)) (hm0 u)))).trans
        (congrArg j (Subtype.ext rfl)) }

theorem offset_rim_not_contained_in_disk_of_essential
    [NormedSpace ℝ E]
    (c : Ann ≃ₜ N) (gamma : Q2 ≃ₜ S) (hSN : S ⊆ N) (hNW : N ⊆ W)
    (hcore : ∀ x : Ann, (c x : E) ∈ S ↔ depth 1 x = 0)
    (side : Bool) (hBN : B ⊆ N)
    (hlevel : ∀ x : Ann, (c x : E) ∈ B ↔
      depth 1 x = if side then (1 / 8 : ℝ) else -(1 / 8 : ℝ))
    (j : C(W, X))
    (hessential : ¬ (j.comp
      ((ContinuousMap.inclusion (hSN.trans hNW)).comp (gamma : C(Q2, S)))).Nullhomotopic)
    {T Q : Set E} (hTW : T ⊆ W) (hBT : B ⊆ T) :
    ¬ IsFinitePLBallPair (ℝ × ℝ) T Q := by
  intro hdisk
  obtain ⟨k, hk⟩ := exists_offset_rim_projection_homotopy c gamma hSN hNW hcore
    side hBN hlevel j
  obtain ⟨_, D, _, hcv, hne, H, _, _⟩ := hdisk
  let : ContractibleSpace D := hcv.contractibleSpace (hne.mono interior_subset)
  let : ContractibleSpace T := H.contractibleSpace
  let kT : C(Q2, T) := (ContinuousMap.inclusion hBT).comp k
  let jT : C(T, X) := j.comp (ContinuousMap.inclusion hTW)
  obtain ⟨x, hx⟩ := ((id_nullhomotopic T).comp_left kT).comp_right jT
  exact hessential ⟨x, hk.symm.trans hx⟩

end PoincareConjecture.M76.Dehn.Annuli
