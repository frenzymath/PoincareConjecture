import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.CapAttachmentLocalBalls
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Charts.FinitePLBallInteriorChart

set_option autoImplicit false

open Set Metric Geometry

namespace Set.IsFinitePLBallPair

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem exists_chart_of_attachment_product
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D B U W : Set E} (hD : IsFinitePLBallPair V3 D B)
    (H : (B ×ˢ J : Set (E × ℝ)) ≃ₜ U) (hH : H.IsFinitePL) (hUW : U ⊆ W)
    (hbase : ∀ x (hx : x ∈ B),
      (H ⟨(x, 0), ⟨hx, by norm_num, zero_le_one⟩⟩ : E) = x)
    (σ : E × ℝ → E) (hσval : ∀ z, (H z : E) = σ z)
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1)
    (hopen : ∀ ε : ℝ, 0 < ε → ε ≤ η →
      IsOpen ((Subtype.val : W → E) ⁻¹' (σ '' (B ×ˢ Ioo (-ε) ε))))
    {p : E} (hp : p ∈ B) :
    ∃ (A q : Set E) (_hAW : A ⊆ W) (Q : OpenPartialHomeomorph W V3)
      (f : E → V3) (g : V3 → E),
      IsFinitePLBallPair (V2 × ℝ) A q ∧ p ∈ A \ q ∧
      Q.source = (Subtype.val : W → E) ⁻¹' (A \ q) ∧
      Q.target = interior (closedBall (0 : V3) 1) ∧
      FinitePiecewiseAffineOn f A ∧ FinitePiecewiseAffineOn g (closedBall (0 : V3) 1) ∧
      (∀ x : W, Q x = f x) ∧
      (∀ y ∈ closedBall (0 : V3) 1, (Q.symm y : E) = g y) ∧
      MapsTo g (closedBall (0 : V3) 1) A ∧
      LeftInvOn g f A ∧ RightInvOn g f (closedBall (0 : V3) 1) := by
  obtain ⟨A, q, hA, hAW, hpA, hopenA⟩ :=
    hD.exists_local_ball_of_attachment_product H hH hUW hbase σ hσval hη hηsmall hopen hp
  let c : (V2 × ℝ) ≃L[ℝ] V3 := ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨Q, f, g, hQs, hQt, hf, hg, hQf, hQg, hgm, hleft, hright⟩ :=
    hA.exists_open_cube_interior_chart c hAW hopenA
  exact ⟨A, q, hAW, Q, f, g, hA, hpA, hQs, hQt, hf, hg, hQf, hQg, hgm, hleft, hright⟩

theorem exists_attachment_point_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P D B : Set E} (hD : IsFinitePLBallPair V3 D B) (hP : IsClosed P)
    (hPD : P ∩ D = B) (c : E × ℝ → E)
    (C : (B ×ˢ I : Set (E × ℝ)) ≃ₜ c '' (B ×ˢ I))
    (hC : C.IsFinitePL) (hCval : ∀ z, (C z : E) = c z)
    (hcP : MapsTo c (B ×ˢ I) P)
    (hc0 : ∀ x ∈ B, c (x, 0) = x)
    (hcB : ∀ z ∈ B ×ˢ I, c z ∈ B ↔ z.2 = 0)
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 2)
    (hopen : ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      IsOpen ((Subtype.val : P → E) ⁻¹' (c '' (B ×ˢ Ico 0 ε))))
    {p : E} (hp : p ∈ B) :
    ∃ (A q : Set E) (_hAW : A ⊆ P ∪ D) (Q : OpenPartialHomeomorph ↥(P ∪ D) V3)
      (f : E → V3) (g : V3 → E),
      IsFinitePLBallPair (V2 × ℝ) A q ∧ p ∈ A \ q ∧
      Q.source = (Subtype.val : ↥(P ∪ D) → E) ⁻¹' (A \ q) ∧
      Q.target = interior (closedBall (0 : V3) 1) ∧
      FinitePiecewiseAffineOn f A ∧ FinitePiecewiseAffineOn g (closedBall (0 : V3) 1) ∧
      (∀ x : ↥(P ∪ D), Q x = f x) ∧
      (∀ y ∈ closedBall (0 : V3) 1, (Q.symm y : E) = g y) ∧
      MapsTo g (closedBall (0 : V3) 1) A ∧
      LeftInvOn g f A ∧ RightInvOn g f (closedBall (0 : V3) 1) := by
  obtain ⟨d, σ, H, hH, hσval, _, hdD, _, _, _, _, hσ0, _, η, hη, hηδ, hopenH⟩ :=
    hD.exists_attachment_product hP hPD c C hC hCval hcP hc0 hcB hδ hδsmall hopen
  have hUW : (c '' (B ×ˢ I)) ∪ d '' (B ×ˢ I) ⊆ P ∪ D := by
    rintro x (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact Or.inl (hcP hz)
    · exact Or.inr (hdD hz)
  have hbase (x : E) (hx : x ∈ B) :
      (H ⟨(x, 0), ⟨hx, by norm_num, zero_le_one⟩⟩ : E) = x :=
    (hσval _).trans (hσ0 x hx)
  exact hD.exists_chart_of_attachment_product H hH hUW hbase σ hσval hη
    (by linarith) hopenH hp

end Set.IsFinitePLBallPair
