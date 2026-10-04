import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.Geometry.SourceFamilySelection

/-!
# Diverging curvature scales of the retained source necks

Morgan--Tian Claims 10.3-10.6, printed pp. 248-252. The actual regional
selection preserves both the diverging base scalar and the diverging
high-to-low ratio after endpoint recentering and trimming. Any neck chosen
on the retained segment has diverging source scalar. See M28 derivation 30.
-/

set_option autoImplicit false

open Set Filter

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

/-- The original base scalar stays positive after the finite selection;
Theorem 10.2 counterexamples, printed pp. 246-247. -/
theorem base_scalar_pos (H : CounterexampleNeckFamily E) (k : ℕ) :
    0 < (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩ :=
  lt_of_lt_of_le (by positivity) (E (k + H.shift)).base_lower

/-- The finite shift preserves divergence of the original base scalars;
Theorem 10.2 counterexamples, printed pp. 246-247. -/
theorem base_scalar_tendsto_atTop (H : CounterexampleNeckFamily E) :
    Tendsto (fun k => (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩) atTop atTop :=
  (counterexampleBlowupSequence E).scalar_diverges.comp
    H.sourceIndex_strictMono.tendsto_atTop

/-- The actual retained low endpoint has positive scalar;
Claims 10.3-10.4, printed pp. 248-250. -/
theorem lower_scalar_pos (H : CounterexampleNeckFamily E) (k : ℕ) :
    0 < (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).lower⟩ := by
  rw [(H.segment k).lower_scalar]
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hB)) (H.base_scalar_pos k)

/-- Exact retained low-scalar normalization preserves divergence;
Claims 10.3-10.6, printed pp. 248-252. -/
theorem lower_scalar_tendsto_atTop (H : CounterexampleNeckFamily E) :
    Tendsto (fun k => (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).lower⟩)
      atTop atTop := by
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  have h := (tendsto_const_mul_atTop_of_pos
    (mul_pos (by norm_num : (0 : ℝ) < 16) (sq_pos_of_pos hB))).2
      H.base_scalar_tendsto_atTop
  convert h using 1
  funext k
  exact (H.segment k).lower_scalar

/-- The original violating ratio survives recentering and both scalar
cuts with the explicit factor `32 * B^4`; Claims 10.3-10.4, pp. 248-250. -/
theorem retained_ratio_lower (H : CounterexampleNeckFamily E) (k : ℕ) :
    (((k + H.shift : ℕ) : ℝ) + 1) / (32 * (max C 2) ^ 4) <
      (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).upper⟩ /
        (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).lower⟩ := by
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  apply (div_lt_div_iff₀ (by positivity : 0 < 32 * (max C 2) ^ 4)
    (H.lower_scalar_pos k)).2
  rw [(H.segment k).lower_scalar]
  have h := mul_lt_mul_of_pos_left (H.segment k).upper_scalar
    (mul_pos (by norm_num : (0 : ℝ) < 16) (sq_pos_of_pos hB))
  nlinarith only [h]

/-- The high-to-low scalar ratio on the retained source segment tends
to infinity, with fixed epsilon and C; Claims 10.3-10.6, pp. 248-252. -/
theorem retained_ratio_tendsto_atTop (H : CounterexampleNeckFamily E) :
    Tendsto (fun k =>
      (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).upper⟩ /
        (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).lower⟩)
      atTop atTop := by
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  have hindex : Tendsto (fun k : ℕ => ((k + H.shift : ℕ) : ℝ) + 1)
      atTop atTop := by
    apply tendsto_atTop_mono (f := fun k : ℕ => (k : ℝ)) _ tendsto_natCast_atTop_atTop
    intro k
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) H.shift]
  exact tendsto_atTop_mono (fun k => (H.retained_ratio_lower k).le)
    ((tendsto_div_const_atTop_of_pos
      (by positivity : 0 < 32 * (max C 2) ^ 4)).2 hindex)

/-- Any indexed choice on the retained segments has diverging scalar
at its literal original strong-neck centers; Claims 10.6-10.11, pp. 252-255. -/
theorem neck_center_scalar_tendsto_atTop (H : CounterexampleNeckFamily E)
    (v : ℕ → ℝ) (hv : ∀ k, v k ∈ Icc (H.segment k).lower (H.segment k).upper) :
    Tendsto (fun k => (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, ((H.segment k).neckAt (v k) (hv k)).center⟩)
      atTop atTop := by
  apply tendsto_atTop_mono (f := fun k => (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).lower⟩)
      _ H.lower_scalar_tendsto_atTop
  intro k
  rw [(H.segment k).neckAt_center, (H.segment k).lower_scalar]
  exact ((H.segment k).scalar_band (v k) (hv k)).1

end PoincareMT.M28.CounterexampleNeckFamily
