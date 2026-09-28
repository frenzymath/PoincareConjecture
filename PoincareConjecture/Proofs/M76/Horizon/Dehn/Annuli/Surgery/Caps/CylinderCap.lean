import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Caps.OriginalRimObstruction



set_option autoImplicit false
open Set Metric Geometry Topology
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => Set.prod Q (Icc (-1 : ℝ) 1)

noncomputable def cylinderLevelPoint (u : Q) (t : unitInterval) : Cyl :=
  ⟨(u, 2 * (t : ℝ) - 1), u.property,
    by constructor <;> linarith [t.property.1, t.property.2]⟩

theorem continuous_cylinderLevelPoint :
    Continuous (fun z : unitInterval × Q ↦ cylinderLevelPoint z.2 z.1) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_snd).prodMk (by fun_prop)

theorem cylinder_maps_nullhomotopic_of_cap
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D B : Set E} (hD : IsFinitePLBallPair (ℝ × ℝ) D B)
    (F₀ F₁ : C(Cyl, X)) (q : Q ≃ₜ Q)
    (hseam : ∀ u, F₀ (cylinderLevelPoint u 1) = F₁ (cylinderLevelPoint (q u) 0))
    (cap : C(D, X)) (seam : C(Q, D))
    (hcap : ∀ u, F₁ (cylinderLevelPoint (q u) 1) = cap (seam u)) :
    (⟨fun u ↦ F₀ (cylinderLevelPoint u 0),
      F₀.continuous.comp (continuous_cylinderLevelPoint.comp
        (continuous_const.prodMk continuous_id))⟩ : C(Q, X)).Nullhomotopic := by
  let a : C(Q, X) := ⟨fun u ↦ F₀ (cylinderLevelPoint u 0),
    F₀.continuous.comp (continuous_cylinderLevelPoint.comp
      (continuous_const.prodMk continuous_id))⟩
  let b : C(Q, X) := ⟨fun u ↦ F₀ (cylinderLevelPoint u 1),
    F₀.continuous.comp (continuous_cylinderLevelPoint.comp
      (continuous_const.prodMk continuous_id))⟩
  let h₀ : a.Homotopy b := {
    toFun z := F₀ (cylinderLevelPoint z.2 z.1)
    continuous_toFun := F₀.continuous.comp continuous_cylinderLevelPoint
    map_zero_left := fun _ ↦ rfl
    map_one_left := fun _ ↦ rfl }
  let h₁ : b.Homotopy (cap.comp seam) := {
    toFun z := F₁ (cylinderLevelPoint (q z.2) z.1)
    continuous_toFun := F₁.continuous.comp (continuous_cylinderLevelPoint.comp
      (continuous_fst.prodMk (q.continuous.comp continuous_snd)))
    map_zero_left := fun u ↦ (hseam u).symm
    map_one_left := hcap }
  obtain ⟨_, K, _, hcv, hne, H, _, _⟩ := hD
  let : ContractibleSpace K := hcv.contractibleSpace (hne.mono interior_subset)
  let : ContractibleSpace D := H.contractibleSpace
  obtain ⟨x, hx⟩ := ((id_nullhomotopic D).comp_left seam).comp_right cap
  exact ⟨x, (show a.Homotopic (cap.comp seam) from ⟨h₀.trans h₁⟩).trans hx⟩

end PoincareConjecture.M76.Dehn.Annuli
