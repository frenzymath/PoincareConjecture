import PoincareConjecture.Proofs.M25.AppA_1_Necks.Coordinates
import Mathlib.Topology.Connected.LocallyPathConnected

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem NeckOnlyCover.exists_complementary_path_finite_middle_cover
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (H : NeckOnlyCover g) (hwhole : H.X = Set.univ)
    (N : EpsilonNeck g) (hN : N ∈ H.necks)
    (hnonsep : N.IsNonseparating) (q : UnitTwoSphere) :
    ∃ γ : Path
        (N.coordinate_map (q, -N.epsilon⁻¹ / 2))
        (N.coordinate_map (q, N.epsilon⁻¹ / 2)),
      ∃ F : Set (EpsilonNeck g),
        F.Finite ∧ F ⊆ H.necks ∧
        (∀ t, γ t ∈ connectedComponent N.center \ N.central_sphere) ∧
        Set.range γ ⊆ ⋃ R ∈ F,
          R.region (-H.epsilon⁻¹ / 2) (H.epsilon⁻¹ / 2) := by
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let U : Set M := connectedComponent N.center \ N.central_sphere
  have hUopen : IsOpen U :=
    IsOpen.sdiff (isOpen_connectedComponent (x := N.center)) N.isClosed_central_sphere
  have hUpath : IsPathConnected U :=
    hUopen.isConnected_iff_isPathConnected.mp hnonsep
  have hL : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hLH : 0 < H.epsilon⁻¹ := by
    rw [← H.neck_epsilon N hN]
    exact hL
  have hpoint {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
      (hs0 : s ≠ 0) : N.coordinate_map (q, s) ∈ U := by
    refine ⟨N.m25_carrier_subset_connectedComponent
      (N.coordinate_map_mem ⟨mem_univ _, hs⟩), ?_⟩
    intro hcentral
    have hzero := ((N.mem_central_sphere_iff _).mp hcentral).2
    rw [N.coordinate_inverse_map (q, s) hs] at hzero
    exact hs0 hzero
  have hminus : N.coordinate_map (q, -N.epsilon⁻¹ / 2) ∈ U := by
    apply hpoint
    · constructor <;> linarith
    · linarith
  have hplus : N.coordinate_map (q, N.epsilon⁻¹ / 2) ∈ U := by
    apply hpoint
    · constructor <;> linarith
    · linarith
  obtain ⟨γ, hγ⟩ := hUpath.joinedIn _ hminus _ hplus
  have hcompact : IsCompact (Set.range γ) := isCompact_range γ.continuous
  have hmiddle (R : EpsilonNeck g) :
      R.center ∈ R.region (-H.epsilon⁻¹ / 2) (H.epsilon⁻¹ / 2) := by
    have hc := (R.mem_central_sphere_iff R.center).mp R.center_on_central_sphere
    refine ⟨hc.1, ?_, ?_⟩
    · rw [hc.2]
      linarith
    · rw [hc.2]
      linarith
  have hcover : Set.range γ ⊆ ⋃ R ∈ H.necks,
      R.region (-H.epsilon⁻¹ / 2) (H.epsilon⁻¹ / 2) := by
    intro x _hx
    have hxH : x ∈ H.X := by rw [hwhole]; exact mem_univ x
    obtain ⟨R, hR, hcenter⟩ := H.pointwise_center_cover x hxH
    refine mem_iUnion₂.mpr ⟨R, hR, ?_⟩
    rw [← hcenter]
    exact hmiddle R
  obtain ⟨F, hFsub, hFfinite, hFcover⟩ :=
    hcompact.elim_finite_subcover_image
      (b := H.necks)
      (c := fun R : EpsilonNeck g =>
        R.region (-H.epsilon⁻¹ / 2) (H.epsilon⁻¹ / 2))
      (fun R _hR => R.isOpen_region _ _) hcover
  exact ⟨γ, F, hFfinite, hFsub, hγ, hFcover⟩

end PoincareConjecture
