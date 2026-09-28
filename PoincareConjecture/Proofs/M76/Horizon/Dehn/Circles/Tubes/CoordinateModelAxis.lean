import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.CoordinateModelPlanes
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPreimages

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)

theorem finitePL_coordinate_model_axis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (W rim : Set E) (f : E → V3)
    (C0 : Set V3) (hC : IsCompact C0) (hcv : Convex ℝ C0)
    (hC0 : (0 : V3) ∈ interior C0) (L : (Fin 3 ⊕ Fin 3) → V3 →ₗ[ℝ] ℝ)
    (hrep : C0 = {x | ∀ j, L j x ≤ 1})
    (theta : W ≃ₜ C0) (htheta : theta.IsFinitePL)
    (hlink : ∀ z : W, (z : E) ∈ rim ↔ (theta z : V3) ∈ frontier C0)
    (hmarks : ∀ j (z : W), ((theta z : V3) j = 0 ↔ f z j = 0) ∧
      (0 ≤ (theta z : V3) j ↔ 0 ≤ f z j)) :
    IsFinitePLBallPair ℝ {z | z ∈ W ∧ f z 0 = 0 ∧ f z 1 = 0}
      {z | z ∈ W ∧ f z 0 = 0 ∧ f z 1 = 0 ∧ z ∈ rim} := by
  classical
  let ax : ℝ →ᴬ[ℝ] V3 := (ContinuousLinearMap.pi fun j : Fin 3 =>
    if j = 2 then ContinuousLinearMap.id ℝ ℝ else 0).toContinuousAffineMap
  let az : V3 →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj (2 : Fin 3)).toContinuousAffineMap
  have hleft : Function.LeftInverse az ax := by intro t; simp [ax, az]
  have ha0 : ax 0 = 0 := by ext j; fin_cases j <;> simp [ax]
  have hax (x : V3) : ax (az x) = x ↔ x 0 = 0 ∧ x 1 = 0 := by
    simp [ax, az, funext_iff, Fin.forall_fin_succ, eq_comm]
  have hsection := isFinitePLBallPair_convex_coordinate_section C0 hC hcv hC0 L hrep
    ax az hleft ha0 (fun e : Empty => nomatch e) ⟨0, fun e => nomatch e⟩
  have hb : IsFinitePLBallPair ℝ {t | ax t ∈ C0} {t | ax t ∈ C0 ∧ ax t ∈ frontier C0} := by
    simpa using hsection
  have himage (A : Set V3) : ax '' {t | ax t ∈ A} = {x | x ∈ A ∧ x 0 = 0 ∧ x 1 = 0} := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨ht, (hax _).mp (by rw [hleft])⟩
    · rintro ⟨hx, h0, h1⟩
      exact ⟨az x, by change ax (az x) ∈ A; rwa [(hax x).mpr ⟨h0, h1⟩],
        (hax x).mpr ⟨h0, h1⟩⟩
  have hrimimage : ax '' {t | ax t ∈ C0 ∧ ax t ∈ frontier C0} =
      {x | x ∈ C0 ∧ x 0 = 0 ∧ x 1 = 0 ∧ x ∈ frontier C0} := by
    have h := himage (C0 ∩ frontier C0)
    convert h using 1 <;> ext x <;> simp only [mem_ofPred_eq, mem_inter_iff] <;> tauto
  have haxis : IsFinitePLBallPair ℝ {x | x ∈ C0 ∧ x 0 = 0 ∧ x 1 = 0}
      {x | x ∈ C0 ∧ x 0 = 0 ∧ x 1 = 0 ∧ x ∈ frontier C0} := by
    simpa only [himage, hrimimage] using hb.affine_image ax hleft.injective.injOn
  obtain ⟨t, ht, htval⟩ := htheta
  have hpre := (show theta.IsFinitePL from ⟨t, ht, htval⟩).preimage_ballPair haxis
    (fun _ hz => hz.1) htval
  have hbody : W ∩ t ⁻¹' {x | x ∈ C0 ∧ x 0 = 0 ∧ x 1 = 0} =
      {z | z ∈ W ∧ f z 0 = 0 ∧ f z 1 = 0} := by
    ext z
    by_cases hz : z ∈ W
    · have htz : t z ∈ C0 := htval ⟨z, hz⟩ ▸ (theta ⟨z, hz⟩).property
      have h0 := (hmarks 0 ⟨z, hz⟩).1
      have h1 := (hmarks 1 ⟨z, hz⟩).1
      simp only [htval] at h0 h1
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, hz, htz, true_and, h0, h1]
    · simp [hz]
  have hrim : W ∩ t ⁻¹' {x | x ∈ C0 ∧ x 0 = 0 ∧ x 1 = 0 ∧ x ∈ frontier C0} =
      {z | z ∈ W ∧ f z 0 = 0 ∧ f z 1 = 0 ∧ z ∈ rim} := by
    ext z
    by_cases hz : z ∈ W
    · have htz : t z ∈ C0 := htval ⟨z, hz⟩ ▸ (theta ⟨z, hz⟩).property
      have h0 := (hmarks 0 ⟨z, hz⟩).1
      have h1 := (hmarks 1 ⟨z, hz⟩).1
      have hl := hlink ⟨z, hz⟩
      simp only [htval] at h0 h1 hl
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, hz, htz, true_and, h0, h1, ← hl]
    · simp [hz]
  simpa only [hbody, hrim] using hpre

end PoincareConjecture.M76.Dehn
