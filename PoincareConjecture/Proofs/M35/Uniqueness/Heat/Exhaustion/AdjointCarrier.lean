import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.RawAdjoint








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "e" => fun i : Fin n => EuclideanSpace.single i (1 : ℝ)

def rawTestAdjointField {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (f : Fin n → 𝓢(V, ℝ)) (x : V) : V :=
  WithLp.toLp 2 (fun j => rawTestAdjoint D f j x)

private theorem carrier_fderiv_zero {E : Set V} (hE : IsClosed E) {f : V → ℝ}
    (hf : ∀ x ∉ E, f x = 0) {x : V} (hx : x ∉ E) : fderiv ℝ f x = 0 := by
  apply fderiv_of_notMem_tsupport
  apply fun h => hx ((closure_minimal ?_ hE) h)
  intro y hy
  by_contra hn
  exact hy (hf y hn)

theorem rawTestAdjoint_zero_off {E : Set V} (hE : IsClosed E)
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (f : Fin n → supportedTests E) (j : Fin n) {x : V} (hx : x ∉ E) :
    rawTestAdjoint D (fun k => (f k : 𝓢(V, ℝ))) j x = 0 := by
  have hp (i l : Fin n) : fderiv ℝ (fun y => (rawCoordinateGram g y)⁻¹ i l *
      fderiv ℝ (f j : 𝓢(V, ℝ)) y (e l)) x = 0 := by
    apply carrier_fderiv_zero hE ?_ hx
    intro y hy
    have hz : fderiv ℝ (f j : 𝓢(V, ℝ)) y (e l) = 0 :=
      (testPartial hE l (f j)).property y hy
    rw [hz, mul_zero]
  have hb (k i : Fin n) : fderiv ℝ (fun y => rawFirstComponent D k j i y *
      (f k : 𝓢(V, ℝ)) y) x = 0 := by
    apply carrier_fderiv_zero hE ?_ hx
    intro y hy
    rw [(f k).property y hy, mul_zero]
  simp only [rawTestAdjoint, hp, hb, zero_apply,
    (fun k => (f k).property x hx), mul_zero, Finset.sum_const_zero, sub_zero, add_zero]

theorem rawTestAdjointField_zero_off {E : Set V} (hE : IsClosed E)
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (f : Fin n → supportedTests E) {x : V} (hx : x ∉ E) :
    rawTestAdjointField D (fun k => (f k : 𝓢(V, ℝ))) x = 0 := by
  apply PiLp.ext
  exact fun j => rawTestAdjoint_zero_off hE D f j hx

theorem rawTestAdjointField_family_continuousOn {J : Set ℝ} (F : RicciFlow n V J)
    (f : Fin n → 𝓢(V, ℝ)) :
    ContinuousOn (fun p : ℝ × V => rawTestAdjointField (F.connection p.1) f p.2)
      (J ×ˢ univ) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp_continuousOn
  exact continuousOn_pi.mpr fun j => (rawTestAdjoint_family_contDiffOn F f j).continuousOn

theorem exists_raw_adjoint_carrier_bound {J I : Set ℝ} (F : RicciFlow n V J)
    (hI : IsCompact I) (hIJ : I ⊆ J) {E : Set V} (hE : IsCompact E)
    (f : Fin n → supportedTests E) :
    ∃ M : ℝ, 0 < M ∧ ∀ t ∈ I, ∀ x ∈ E,
      ‖rawTestAdjointField (F.connection t) (fun j => (f j : 𝓢(V, ℝ))) x‖ ≤ M := by
  have hc := (rawTestAdjointField_family_continuousOn F
    (fun j => (f j : 𝓢(V, ℝ)))).mono (prod_mono hIJ (subset_univ E))
  obtain ⟨M, hM, hb⟩ := ((hI.prod hE).image_of_continuousOn hc).isBounded.exists_pos_norm_le
  exact ⟨M, hM, fun t ht x hx => hb _ ⟨(t, x), ⟨ht, hx⟩, rfl⟩⟩

end PoincareConjecture.M35.Uniqueness.Heat
