import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.StripEndCharts









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)


def originalStripEndParameter (sign : Bool) (s : unitInterval) : ℝ :=
  (1 - (s : ℝ)) * farArmParameter (!sign) + (s : ℝ) * farArmParameter sign

theorem originalStripEndParameter_mem (sign : Bool) (s : unitInterval) :
    originalStripEndParameter sign s ∈ Icc (-1 : ℝ) 1 := by
  cases sign <;> simp only [originalStripEndParameter, farArmParameter, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, mul_one, mul_neg, mul_one] <;>
    constructor <;> linarith [s.property.1, s.property.2]

@[simp] theorem originalStripEndParameter_zero (sign : Bool) :
    originalStripEndParameter sign 0 = farArmParameter (!sign) := by
  simp [originalStripEndParameter]

@[simp] theorem originalStripEndParameter_one (sign : Bool) :
    originalStripEndParameter sign 1 = farArmParameter sign := by
  simp [originalStripEndParameter]


def originalStripEndPath {E : Type*} [TopologicalSpace E]
    (c : P2 → E) (hc : ContinuousOn c source) (t : unitInterval) (sign : Bool) :
    Path (c (t, farArmParameter (!sign))) (c (t, farArmParameter sign)) where
  toFun s := c (t, originalStripEndParameter sign s)
  continuous_toFun := hc.comp_continuous (by
    dsimp [originalStripEndParameter]
    fun_prop) (fun s ↦ ⟨t.property, originalStripEndParameter_mem sign s⟩)
  source' := by simp
  target' := by simp

theorem originalStripEndPath_val {E : Type*} [TopologicalSpace E]
    (c : P2 → E) (hc : ContinuousOn c source) (t : unitInterval) (sign : Bool)
    (s : unitInterval) :
    originalStripEndPath c hc t sign s = c (t, originalStripEndParameter sign s) := rfl

theorem originalStripEndPath_mem {E : Type*} [TopologicalSpace E]
    (c : P2 → E) (hc : ContinuousOn c source) (t : unitInterval) (sign : Bool)
    (s : unitInterval) :
    originalStripEndPath c hc t sign s ∈ c '' stripEnd t :=
  ⟨(t, originalStripEndParameter sign s),
    ⟨rfl, originalStripEndParameter_mem sign s⟩, rfl⟩

theorem originalStripEndPath_mem_ends {E : Type*} [TopologicalSpace E]
    (c : P2 → E) (hc : ContinuousOn c source) (t : unitInterval) (sign : Bool)
    (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) (s : unitInterval) :
    originalStripEndPath c hc t sign s ∈ c '' stripEnds :=
  ⟨(t, originalStripEndParameter sign s),
    ⟨ht, originalStripEndParameter_mem sign s⟩, rfl⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
