import PoincareLib.Geometry.RicciFlow.Compactness.Pointed
import PoincareLib.Geometry.RicciFlow.Compactness.Convergence
import PoincareLib.Geometry.RicciFlow.Harnack.Regularity

/-! Finite-window based flows retain the exact metric and connection
representatives of a source Ricci flow on a larger time domain. -/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT

/-- A compact subset of an ancient time interval lies in a bounded interior
window which also contains the base time zero. -/
theorem exists_ancient_window_of_isCompact {T : ℝ} (hT : 0 < T)
    {K : Set ℝ} (hK : IsCompact K) (hKT : K ⊆ Iio T) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧ b < T ∧ K ⊆ Ioo a b := by
  obtain ⟨l, hl⟩ := (hK.insert 0).exists_isLeast (insert_nonempty 0 K)
  obtain ⟨u, hu⟩ := (hK.insert 0).exists_isGreatest (insert_nonempty 0 K)
  have hl0 : l ≤ 0 := hl.2 (mem_insert 0 K)
  have hu0 : 0 ≤ u := hu.2 (mem_insert 0 K)
  have huT : u < T := by
    rcases hu.1 with rfl | huK
    · exact hT
    · exact hKT huK
  refine ⟨l - 1, (u + T) / 2, by linarith, by linarith, by linarith, ?_⟩
  intro t ht
  have hlt := hl.2 (mem_insert_of_mem 0 ht)
  have htu := hu.2 (mem_insert_of_mem 0 ht)
  constructor <;> linarith

/-- Eventual inclusion of a closed time window gives a source tail defined
on its open interior. -/
theorem exists_source_window_tail {J : ℕ → Set ℝ} {a b : ℝ}
    (h : ∀ᶠ k in Filter.atTop, Icc a b ⊆ J k) :
    ∃ N : ℕ, ∀ k, Ioo a b ⊆ J (k + N) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  exact ⟨N, fun k ↦ Ioo_subset_Icc_self.trans (hN (k + N) (by omega))⟩

/-- View a time restriction as a based flow using its canonical volume and
ordinary product spacetime vector field. -/
noncomputable def FlowCarrier.basedWindow {n : ℕ} (C : FlowCarrier n)
    {J : Set ℝ} {a b : ℝ}
    (F : @RicciFlow n C.carrier C.topologicalSpace C.chartedSpace C.isManifold J)
    (p : C.carrier) (hsub : Ioo a b ⊆ J) (hab : a < b) : BasedFlow n a b C := by
  letI := C.topologicalSpace
  letI := C.chartedSpace
  letI := C.isManifold
  exact {
    base := p
    flow := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F hsub ordConnected_Ioo (by
      refine ⟨(2 * a + b) / 3, ⟨?_, ?_⟩, (a + 2 * b) / 3, ⟨?_, ?_⟩, ?_⟩ <;> linarith)
    volumeMeasure := C.metricHausdorffVolume (F.metric 0)
    spacetimeVectorField := fun _ _ ↦ (1, 0)
    spacetimeVectorField_time := fun _ _ ↦ rfl
    spacetimeVectorField_spatial_zero := fun _ _ ↦ rfl }

/-- Restrict a tail of expanding-domain source flows to a common finite
interval, retaining their source carriers and points. -/
noncomputable def sourceWindowSequence {n : ℕ} (C : ℕ → FlowCarrier n)
    {J : ℕ → Set ℝ} {a b : ℝ}
    (F : ∀ k, @RicciFlow n (C k).carrier (C k).topologicalSpace
      (C k).chartedSpace (C k).isManifold (J k))
    (p : ∀ k, (C k).carrier) (N : ℕ)
    (hsub : ∀ k, Ioo a b ⊆ J (k + N)) (hab : a < b) :
    PointedFlowSequence n a b where
  carrier := fun k ↦ C (k + N)
  flow := fun k ↦ (C (k + N)).basedWindow (F (k + N)) (p (k + N)) (hsub k) hab

end PoincareMT
