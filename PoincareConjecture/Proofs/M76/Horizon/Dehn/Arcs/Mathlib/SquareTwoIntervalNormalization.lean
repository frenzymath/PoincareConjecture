import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.SquareRimHalves
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.PrescribedTwoIntervalCircle









set_option autoImplicit false

open Set Metric Geometry
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1


def intervalChartPath {E : Type*} [TopologicalSpace E] {U : Set E}
    (p : I01 ≃ₜ U) : Path (p (0 : unitInterval) : E) (p (1 : unitInterval) : E) where
  toFun t := p t
  continuous_toFun := continuous_subtype_val.comp p.continuous
  source' := rfl
  target' := rfl




theorem exists_squareRim_two_interval_normalization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U V : Set E} {a b : E} (_hab : a ≠ b) (hUV : U ∩ V = {a, b})
    (p0 : I01 ≃ₜ U) (p1 : I01 ≃ₜ V)
    (hp0 : p0.IsFinitePL) (hp1 : p1.IsFinitePL)
    (hp00 : (p0 (0 : unitInterval) : E) = a)
    (hp01 : (p0 (1 : unitInterval) : E) = b)
    (hp10 : (p1 (0 : unitInterval) : E) = a)
    (hp11 : (p1 (1 : unitInterval) : E) = b) :
    ∃ H : Q ≃ₜ (U ∪ V : Set E), H.IsFinitePL ∧
      (∀ t : I01, (H (squareRimLoop (squareRimHalfTime false t)) : E) = p0 t) ∧
      (∀ t : I01, (H (squareRimLoop (squareRimHalfTime true t)) : E) = p1 t) ∧
      ∃ hbase : (H squareRimBase : E) = a,
        ((squareRimLoop.map (continuous_subtype_val.comp H.continuous)).cast
          hbase.symm hbase.symm) =
          ((intervalChartPath p0).cast hp00.symm hp01.symm).trans
            ((intervalChartPath p1).cast hp10.symm hp11.symm).symm := by
  obtain ⟨G, hG, hG0, hG1⟩ := exists_prescribed_two_interval_homeomorph
    squareRimHalfCarrier_inter hUV (squareRimHalfChart false) (squareRimHalfChart true)
    p0 p1 (squareRimHalfChart_finitePL false) (squareRimHalfChart_finitePL true) hp0 hp1
    (by simp) (by simp) (by simp) (by simp) hp00 hp01 hp10 hp11
  let H := (Homeomorph.setCongr squareRimHalfCarrier_union.symm).trans G
  have hH : H.IsFinitePL := by
    obtain ⟨f, hf, hGf⟩ := hG
    refine ⟨f, ?_, fun x ↦ hGf _⟩
    simpa only [squareRimHalfCarrier_union] using hf
  have h0 (t : I01) :
      (H (squareRimLoop (squareRimHalfTime false t)) : E) = p0 t := hG0 t
  have h1 (t : I01) :
      (H (squareRimLoop (squareRimHalfTime true t)) : E) = p1 t := hG1 t
  have hbase : (H squareRimBase : E) = a := by
    have heq : squareRimLoop (squareRimHalfTime false 0) = squareRimBase :=
      Subtype.ext (squareRimHalf_zero false)
    simpa only [heq, hp00] using h0 0
  refine ⟨H, hH, h0, h1, hbase, ?_⟩
  apply Path.ext
  funext t
  change (H (squareRimLoop t) : E) =
    (((intervalChartPath p0).cast hp00.symm hp01.symm).trans
      ((intervalChartPath p1).cast hp10.symm hp11.symm).symm) t
  rw [Path.trans_apply]
  split_ifs with ht
  · let s : I01 := ⟨2 * (t : ℝ), ⟨by linarith [t.property.1], by linarith⟩⟩
    have hs : squareRimHalfTime false s = t := by
      apply Subtype.ext
      change (2 * (t : ℝ)) / 2 = (t : ℝ)
      ring
    change (H (squareRimLoop t) : E) = p0 s
    rw [← hs]
    exact h0 s
  · let s : I01 := ⟨1 - (2 * (t : ℝ) - 1),
      ⟨by linarith [t.property.2], by linarith⟩⟩
    have hs : squareRimHalfTime true s = t := by
      apply Subtype.ext
      change 1 - (1 - (2 * (t : ℝ) - 1)) / 2 = (t : ℝ)
      ring
    change (H (squareRimLoop t) : E) = p1 s
    rw [← hs]
    exact h1 s

end PoincareConjecture.M76.Dehn
