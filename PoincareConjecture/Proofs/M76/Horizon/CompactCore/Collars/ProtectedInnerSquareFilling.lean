import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.ProtectedSourceRimCollar










set_option autoImplicit false

open Set Metric unitInterval NormedSpace

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "D" => closedBall (0 : V2) 1


noncomputable def threeQuarterSquare : C(D, D) :=
  ⟨fun x => ⟨(3 / 4 : ℝ) • (x : V2), by
    have hx : ‖(x : V2)‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using x.property
    rw [mem_closedBall, dist_zero_right, norm_smul]
    norm_num
    linarith⟩,
    by fun_prop⟩





theorem PLDomain.exists_protected_inner_square_filling
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K Y F : Set X}
    (hK : PLDomain e K) (hY : IsOpen Y) (hF : IsCompact F)
    (hne : F.Nonempty) (hcut : Y ∩ frontier K = F)
    (gamma : C(Q, F)) (f : C(D, Y))
    (hf : ∀ u : Q, (f ⟨u, sphere_subset_closedBall u.property⟩ : X) = (gamma u : X)) :
    ∃ (H : C(I × D, Y)) (d : C(D, Y)),
      (∀ x : D, H (0, x) = f x) ∧
      (∀ (t : I) (u : Q),
        (H (t, ⟨u, sphere_subset_closedBall u.property⟩) : X) = (gamma u : X)) ∧
      (∀ x : D, (1 / 2 : ℝ) < ‖(x : V2)‖ → ‖(x : V2)‖ < 1 →
        (H (1, x) : X) ∈ interior K) ∧
      (∀ x : D, d x = H (1, threeQuarterSquare x)) ∧
      (∀ x : D, (3 / 4 : ℝ) ≤ ‖(x : V2)‖ → (d x : X) ∈ interior K) ∧
      ∃ A : C(I × Q, Y),
        (∀ u : Q, (A (0, u) : X) = (gamma u : X)) ∧
        (∀ u : Q, A (1, u) = d ⟨u, sphere_subset_closedBall u.property⟩) ∧
        ∀ (t : I) (u : Q), 0 < (t : ℝ) → (A (t, u) : X) ∈ interior K := by
  obtain ⟨H, hH0, hHr, hHann⟩ :=
    hK.exists_protected_source_rim_collar hY hF hne hcut gamma f hf
  let d : C(D, Y) :=
    H.comp ⟨fun x => (1, threeQuarterSquare x), continuous_const.prodMk threeQuarterSquare.continuous⟩
  refine ⟨H, d, hH0, hHr, hHann, fun _ => rfl, ?_, ?_⟩
  · intro x hx
    have hx1 : ‖(x : V2)‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using x.property
    have hn : ‖(threeQuarterSquare x : V2)‖ = (3 / 4 : ℝ) * ‖(x : V2)‖ := by
      change ‖(3 / 4 : ℝ) • (x : V2)‖ = _
      rw [norm_smul]
      norm_num
    exact hHann (threeQuarterSquare x) (by rw [hn]; linarith) (by rw [hn]; linarith)
  · let radius : I → I := fun t =>
      ⟨1 - (t : ℝ) / 4, by constructor <;> linarith [t.property.1, t.property.2]⟩
    have hradius : Continuous radius := by fun_prop
    let A : C(I × Q, Y) :=
      H.comp ⟨fun z => (1, unitSphereRadialMap V2 (radius z.1, z.2)),
        continuous_const.prodMk ((unitSphereRadialMap V2).continuous.comp
          ((hradius.comp continuous_fst).prodMk continuous_snd))⟩
    refine ⟨A, ?_, ?_, ?_⟩
    · intro u
      have hzero : unitSphereRadialMap V2 (radius 0, u) =
          ⟨u, sphere_subset_closedBall u.property⟩ := by
        apply Subtype.ext
        change (1 - (0 : ℝ) / 4) • (u : V2) = (u : V2)
        simp
      change (H (1, unitSphereRadialMap V2 (radius 0, u)) : X) = _
      rw [hzero]
      exact hHr 1 u
    · intro u
      change H (1, unitSphereRadialMap V2 (radius 1, u)) =
        H (1, threeQuarterSquare ⟨u, sphere_subset_closedBall u.property⟩)
      congr 2
      apply Subtype.ext
      change (1 - (1 : ℝ) / 4) • (u : V2) = (3 / 4 : ℝ) • (u : V2)
      norm_num
    · intro t u ht
      apply hHann (unitSphereRadialMap V2 (radius t, u))
      · rw [norm_unitSphereRadialMap]
        change (1 / 2 : ℝ) < 1 - (t : ℝ) / 4
        linarith [t.property.2]
      · rw [norm_unitSphereRadialMap]
        change 1 - (t : ℝ) / 4 < 1
        linarith

end PoincareConjecture.M76
