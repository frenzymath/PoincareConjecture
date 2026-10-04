import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsSourceInitialNormalization

/-!
# Own-scalar interval at an actual joining point

The old cylinder is reparameterized by the scalar at the same joining
point.  The ratio may be below one, so the raw interval is buffered on the
left.  The original neck carrier, coordinate maps, inverse and connection
are retained as input fields; this helper constructs no older carrier and
does not invoke M45 gluing.
Morgan--Tian Definition 2.16 and Lemma 17.7, pp. 30 and 405-406.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

/-- The exact own-scalar clock and buffered raw interval at the same old
joining point.  The supplied `hscalar` is the existing physical readout
for that point; no tested-point scalar or gluing input is substituted. -/
theorem source_initial_own_scalar_data
    (N : EpsilonNeck g) {T q R_join s delta omega : ℝ}
    (hqpos : 0 < q) (hq : q = N.scale⁻¹ ^ 2)
    (hscalar : |R_join / q - 1 / (1 - s)| ≤ (16 / 5 : ℝ) * delta)
    (hs : s ∈ Icc (-omega / 4) 0)
    (homega : 0 < omega) (homegaHalf : omega ≤ 1 / 2)
    (hdelta : (16 / 5 : ℝ) * delta ≤ omega / 4)
    (_hdeltaQuarter : (16 / 5 : ℝ) * delta ≤ 1 / 4) :
    ∃ k : ℝ,
      k = R_join / q ∧ k ∈ Icc (3 / 4 : ℝ) (5 / 4) ∧
      MapsTo (fun u : ℝ => u / k) (Icc (-1 : ℝ) 0) (Icc (-1 - omega) 0) ∧
      q = N.scale⁻¹ ^ 2 ∧ 0 < q * k ∧
      ∀ u : ℝ, T + (u / k) / q = T + u / (q * k) := by
  let k : ℝ := R_join / q
  have hden : 0 < 1 - s := by
    linarith only [hs.2]
  have hsign : s / (1 - s) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hs.2 hden.le
  have hunit : |1 / (1 - s) - 1| ≤ omega / 4 := by
    have hrewrite : 1 / (1 - s) - 1 = s / (1 - s) := by
      field_simp [hden.ne']
      ring
    rw [hrewrite, abs_of_nonpos hsign]
    have hsabs : -s ≤ omega / 4 := by
      linarith only [hs.1]
    have hdenOne : 1 ≤ 1 - s := by linarith only [hs.2]
    have hmul : -s ≤ (omega / 4) * (1 - s) := by
      have h := mul_le_mul_of_nonneg_left hdenOne (by positivity : 0 ≤ omega / 4)
      linarith only [h, hsabs]
    have hdiv : (-s) / (1 - s) ≤ omega / 4 :=
      (div_le_iff₀ hden).2 hmul
    simpa only [neg_div] using hdiv
  have hkerror : |k - 1| ≤ omega / 2 := by
    dsimp only [k]
    calc
      |R_join / q - 1| ≤
          |R_join / q - 1 / (1 - s)| + |1 / (1 - s) - 1| :=
        abs_sub_le _ _ _
      _ ≤ (16 / 5 : ℝ) * delta + omega / 4 :=
        add_le_add hscalar hunit
      _ ≤ omega / 2 := by linarith only [hdelta]
  have homegaNonneg : 0 ≤ omega := homega.le
  have homegaOne : omega ≤ 1 := by linarith only [homegaHalf]
  have hσSmall : omega / 2 ≤ 1 / 4 := by linarith only [homegaHalf]
  obtain ⟨hkBounds, hmap⟩ := source_initial_own_scalar_interval
    (k := k) (sigma := omega / 2) (omega := omega)
    homegaNonneg homegaOne le_rfl hσSmall hkerror
  have hkpos : 0 < k := by linarith only [hkBounds.1]
  have hclockPos : 0 < q * k :=
    (source_initial_own_scalar_clock hqpos hkpos T 0).1
  have hclockEq : ∀ u : ℝ, T + (u / k) / q = T + u / (q * k) := by
    intro u
    exact (source_initial_own_scalar_clock hqpos hkpos T u).2
  refine ⟨k, rfl, hkBounds, hmap, hq, hclockPos, hclockEq⟩

end PoincareMT.M47
