import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.EMetricSpace.Basic










set_option autoImplicit false

open Set
open scoped Manifold ENNReal ContDiff Topology

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)]
  {Y : Type*} [PseudoEMetricSpace Y]




theorem edist_le_mul_pathELength_of_open_cover
    {ι : Sort*} (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (f : M → Y) (C : ℝ≥0∞)
    (hlocal : ∀ i, ∀ (γ : ℝ → M) (a b : ℝ), a ≤ b →
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b) →
      MapsTo γ (Icc a b) (U i) →
      edist (f (γ a)) (f (γ b)) ≤ C * pathELength I γ a b)
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1)) :
    edist (f (γ 0)) (f (γ 1)) ≤ C * pathELength I γ 0 1 := by
  let V : ι → Set unitInterval := fun i => (fun t => γ t) ⁻¹' U i
  have hV (i : ι) : IsOpen (V i) :=
    (hU i).preimage hγ.continuousOn.domRestrict
  have hVcover : univ ⊆ ⋃ i, V i := by
    intro t _
    obtain ⟨i, hi⟩ := hcover (γ t)
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hpiece⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hV hVcover
  have hbound : ∀ k, edist (f (γ 0)) (f (γ (t k))) ≤
      C * pathELength I γ 0 (t k) := by
    intro k
    induction k with
    | zero => simp [ht0]
    | succ k ih =>
      obtain ⟨i, hi⟩ := hpiece k
      have hstep : (t k : ℝ) ≤ t (k + 1) := hmono (Nat.le_succ k)
      have hsub : Icc (t k : ℝ) (t (k + 1)) ⊆ Icc (0 : ℝ) 1 :=
        Icc_subset_Icc (t k).property.1 (t (k + 1)).property.2
      have himage : MapsTo γ (Icc (t k : ℝ) (t (k + 1))) (U i) := by
        intro s hs
        exact hi (show (⟨s, hsub hs⟩ : unitInterval) ∈ Icc (t k) (t (k + 1))
          from hs)
      calc
        edist (f (γ 0)) (f (γ (t (k + 1)))) ≤
            edist (f (γ 0)) (f (γ (t k))) +
              edist (f (γ (t k))) (f (γ (t (k + 1)))) := edist_triangle _ _ _
        _ ≤ C * pathELength I γ 0 (t k) +
            C * pathELength I γ (t k) (t (k + 1)) :=
          add_le_add ih (hlocal i γ _ _ hstep (hγ.mono hsub) himage)
        _ = C * pathELength I γ 0 (t (k + 1)) := by
          rw [← mul_add, pathELength_add (t k).property.1 hstep]
  simpa [hn n le_rfl] using hbound n




theorem edist_le_mul_riemannianEDist_of_open_cover
    {ι : Sort*} (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (f : M → Y)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hlocal : ∀ i, ∀ (γ : ℝ → M) (a b : ℝ), a ≤ b →
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b) →
      MapsTo γ (Icc a b) (U i) →
      edist (f (γ a)) (f (γ b)) ≤ C * pathELength I γ a b)
    (x y : M) : edist (f x) (f y) ≤ C * riemannianEDist I x y := by
  by_contra h
  have hlt : riemannianEDist I x y < edist (f x) (f y) / C :=
    (ENNReal.lt_div_iff_mul_lt (.inl hC0) (.inl hCtop)).mpr
      (by simpa [mul_comm] using lt_of_not_ge h)
  obtain ⟨γ, hx, hy, hγ, hlength⟩ := exists_lt_of_riemannianEDist_lt hlt
  have hb := edist_le_mul_pathELength_of_open_cover U hU hcover f C hlocal hγ
  rw [hx, hy] at hb
  exact (not_lt_of_ge hb) (ENNReal.mul_lt_of_lt_div' hlength)

end Manifold
