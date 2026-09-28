import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargePairedCapContinuation
import PoincareConjecture.Proofs.M76.Triangulation.TerminalHeightCapExterior
import PoincareConjecture.Proofs.M76.Mathlib.PlanarPLDiskUniqueness

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem regionBalls_of_paired_steps_and_unique_extrema
    {S : Set E} {T : Set F} {e : S ≃ₜ frontier T} (he : e.IsFinitePL)
    (hT : IsCompact T) (hTcv : Convex ℝ T) (hTne : (interior T).Nonempty)
    (hdimF : Module.finrank ℝ F = 3) (hdimE : Module.finrank ℝ E = 3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set E} (hC : IsCompact C) (hCcv : Convex ℝ C)
    (hKC : K.space = C) (hSC : S ⊆ interior C)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    {p q : E} (hp : p ∈ S) (hq : q ∈ S) (hpA : A p = 0) (hqA : 0 < A q)
    (hmin : ∀ x ∈ S, 0 ≤ A x) (hmax : ∀ x ∈ S, A x ≤ A q)
    (hzero : S ∩ {x | A x = 0} = {p})
    (hmaxfiber : S ∩ {x | A x = A q} = {q})
    (d : ℝ → Set E)
    (hd : ∀ c ∈ Ioo (0 : ℝ) (A q),
      IsFinitePLBallPair (ℝ × ℝ) (d c) (S ∩ {x | A x = c}))
    (hdplane : ∀ c ∈ Ioo (0 : ℝ) (A q), d c ⊆ {x | A x = c})
    (hlocal : ∀ c ∈ Ioo (0 : ℝ) (A q), ∃ ε : ℝ, 0 < ε ∧
      ∀ u v : ℝ, u ∈ Ioo (0 : ℝ) (A q) → v ∈ Ioo (0 : ℝ) (A q) →
        |u - c| ≤ ε → |v - c| ≤ ε → u ≤ v →
        HasPairedHeightCap S C (d u) A u → HasPairedHeightCap S C (d v) A v) :
    HasAlexanderRegionBalls S C := by
  have hwidth : 0 < A q / 3 := by positivity
  obtain ⟨a, ha, d₀, hd₀, hd₀plane, _, hB, _, hBband, _, hBC, hBE⟩ :=
    he.exists_first_height_cap_ball_with_exterior hT hTcv hTne hdimF hdimE
      K hK hC hCcv hKC (hSC hp) hp A hA hpA hmin hzero hwidth
  have ha' : a ∈ Ioo (0 : ℝ) (A q) := ⟨ha.1, by linarith [ha.2]⟩
  have hd₀eq : d₀ = d a := hd₀.eq_of_same_rim_in_affine_plane (hd a ha')
    A hA hdimE (fun x hx => hd₀plane x hx) (hdplane a ha')
  rw [hd₀eq] at hB hBband hBC hBE
  have hstart : HasPairedHeightCap S C (d a) A a := by
    refine ⟨convexJoin ℝ {p} (d a), hB, hBC, ?_, hBE⟩
    intro x hx
    exact (hBband hx).2
  obtain ⟨b, hb, d₁, hd₁, hd₁plane, hd₁contact, hU, _, hUband,
      hUcut, _, _, hUC, hUE⟩ :=
    he.exists_terminal_height_cap_ball_with_exterior hT hTcv hTne hdimF hdimE
      K hK hC hCcv hKC (hSC hq) hq A hA hmax hmaxfiber hwidth
  have hb' : b ∈ Ioo (0 : ℝ) (A q) := ⟨by linarith [hb.1], hb.2⟩
  have hab : a ≤ b := by linarith [ha.2, hb.1]
  have hd₁eq : d₁ = d b := hd₁.eq_of_same_rim_in_affine_plane (hd b hb')
    A hA hdimE (fun x hx => hd₁plane x hx) (hdplane b hb')
  rw [hd₁eq] at hd₁contact hU hUband hUcut hUC hUE
  have hinterval : Icc a b ⊆ Ioo (0 : ℝ) (A q) := by
    intro c hc
    exact ⟨ha.1.trans_le hc.1, hc.2.trans_lt hb.2⟩
  have hsteps : ∀ c ∈ Icc a b, ∃ ε : ℝ, 0 < ε ∧
      ∀ u v : ℝ, u ∈ Icc a b → v ∈ Icc a b →
        |u - c| ≤ ε → |v - c| ≤ ε → u ≤ v →
        HasPairedHeightCap S C (d u) A u → HasPairedHeightCap S C (d v) A v := by
    intro c hc
    obtain ⟨ε, hε, hstep⟩ := hlocal c (hinterval hc)
    exact ⟨ε, hε, fun u v hu hv => hstep u v (hinterval hu) (hinterval hv)⟩
  have hlower : (S ∩ {x | A x < b}).Nonempty :=
    ⟨p, hp, by change A p < b; simpa only [hpA] using hb'.1⟩
  have hupper : (S ∩ {x | b < A x}).Nonempty := ⟨q, hq, hb.2⟩
  exact regionBalls_of_paired_local_steps A d hab hsteps hstart hdimE
    hU hUE (hd b hb') (hdplane b hb') hd₁contact
    (fun _ hx => (hUband hx).1) hUcut hlower hupper hUC
    K hK hC hCcv ⟨p, hSC hp⟩ hKC

end PoincareConjecture.M76.ZeroChargeJoint
