import PoincareConjecture.Proofs.M76.Triangulation.AffineFirstCapExterior
import PoincareConjecture.Proofs.M76.Mathlib.AffineConeEndpointSections











set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]





theorem IsFinitePL.exists_terminal_height_cap_ball_with_exterior
    {s : Set E} {T : Set F} {e : s ≃ₜ frontier T} (he : e.IsFinitePL)
    (hT : IsCompact T) (hTcv : Convex ℝ T) (hTne : (interior T).Nonempty)
    (hdimF : Module.finrank ℝ F = 3) (hdimE : Module.finrank ℝ E = 3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set E} (hC : IsCompact C) (hCcv : Convex ℝ C) (hKC : K.space = C)
    {p : E} (hpC : p ∈ interior C) (hps : p ∈ s)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (hmax : ∀ x ∈ s, A x ≤ A p) (hmaxfiber : s ∩ {x | A x = A p} = {p})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c ∈ Ioo (A p - ε) (A p), ∃ d : Set E,
      IsFinitePLBallPair (ℝ × ℝ) d (s ∩ {x | A x = c}) ∧
      (∀ x ∈ d, A x = c) ∧ d ∩ s = s ∩ {x | A x = c} ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (convexJoin ℝ {p} d)
        (d ∪ (s ∩ {x | c ≤ A x})) ∧
      convexJoin ℝ {p} d ∩ s = s ∩ {x | c ≤ A x} ∧
      convexJoin ℝ {p} d ⊆ {x | A x ∈ Icc c (A p)} ∧
      convexJoin ℝ {p} d ∩ {x | A x = c} = d ∧
      convexJoin ℝ {p} d ∩ {x | A x = A p} = {p} ∧
      d ⊆ interior C ∧ convexJoin ℝ {p} d ⊆ interior C ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
        (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior (convexJoin ℝ {p} d) ×ˢ {1})
        ((d ∪ (s ∩ {x | c ≤ A x})) ×ˢ {(1 : ℝ)}) := by
  let B := AffineMap.const ℝ E (A p) - A
  have hB : B.linear ≠ 0 := by simpa [B] using hA
  have hpB : B p = 0 := by simp [B]
  have hminB : ∀ x ∈ s, 0 ≤ B x := by
    intro x hx
    change 0 ≤ A p - A x
    exact sub_nonneg.mpr (hmax x hx)
  have hzeroB : s ∩ {x | B x = 0} = {p} := by
    have hset : {x | B x = 0} = {x | A x = A p} := by
      ext x
      change A p - A x = 0 ↔ A x = A p
      rw [sub_eq_zero, eq_comm]
    rw [hset, hmaxfiber]
  obtain ⟨β, hβ, d, hd, hdplane, hdcontact, hball, hcontact, hband, hdC, hconeC,
      hexterior⟩ :=
    he.exists_first_height_cap_ball_with_exterior hT hTcv hTne hdimF hdimE K hK
      hC hCcv hKC hpC hps B hB hpB hminB hzeroB hε
  let c := A p - β
  have hc : c ∈ Ioo (A p - ε) (A p) := by
    constructor <;> dsimp [c] <;> linarith [hβ.1, hβ.2]
  have hlevel : {x | B x = β} = {x | A x = c} := by
    ext x
    change A p - A x = β ↔ A x = A p - β
    constructor <;> intro h <;> linarith
  have hsub : {x | B x ≤ β} = {x | c ≤ A x} := by
    ext x
    change A p - A x ≤ β ↔ A p - β ≤ A x
    constructor <;> intro h <;> linarith
  have hbandset : {x | B x ∈ Icc 0 β} = {x | A x ∈ Icc c (A p)} := by
    ext x
    change (0 ≤ A p - A x ∧ A p - A x ≤ β) ↔
      (A p - β ≤ A x ∧ A x ≤ A p)
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hlevel] at hd hdcontact
  rw [hsub] at hball hcontact hexterior
  rw [hbandset] at hband
  have hdA : ∀ x ∈ d, A x = c := by
    intro x hx
    have h := hdplane x hx
    change A p - A x = β at h
    change A x = A p - β
    linarith
  have hbase : convexJoin ℝ {p} d ∩ {x | A x = c} = d :=
    A.convexJoin_inter_base_level hc.2.ne' hdA
  have hapex : convexJoin ℝ {p} d ∩ {x | A x = A p} = {p} :=
    A.convexJoin_inter_apex_level hc.2.ne' hdA (hd.sdiff_nonempty.mono sdiff_subset)
  exact ⟨c, hc, d, hd, hdA, hdcontact, hball, hcontact, hband, hbase, hapex,
    hdC, hconeC, hexterior⟩

end Homeomorph
