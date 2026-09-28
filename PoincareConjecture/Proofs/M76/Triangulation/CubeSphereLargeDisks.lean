import PoincareConjecture.Proofs.M76.Triangulation.AffineConvexSphereCapDisks
import PoincareConjecture.Proofs.M76.Mathlib.CubeCornerSeparation

set_option autoImplicit false

open Set Geometry
open scoped BigOperators

namespace Geometry

variable {ι : Type*} [Fintype ι] [Nonempty ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem isFinitePLBallPair_cube_frontier_cut {r : ℝ}
    (hrlo : -(Fintype.card ι : ℝ) < r) (hrhi : r < Fintype.card ι)
    (hdim : Fintype.card ι = Module.finrank ℝ F + 1) :
    IsFinitePLBallPair F
      (frontier (Metric.closedBall (0 : ι → ℝ) 1) ∩ {x | ∑ i, x i ≤ r})
      (frontier (Metric.closedBall (0 : ι → ℝ) 1) ∩ {x | ∑ i, x i = r}) := by
  classical
  let T := Metric.closedBall (0 : ι → ℝ) 1
  have hT : IsCompact T := isCompact_closedBall _ _
  let B (i : ι ⊕ ι) : (ι → ℝ) →ᵃ[ℝ] ℝ :=
    (signedCubeCoordinate i).toAffineMap - AffineMap.const ℝ _ 1
  let H := Finset.univ.image B
  have hrep : T = {x | ∀ A ∈ H, A x ≤ 0} := by
    change Metric.closedBall (0 : ι → ℝ) 1 = _
    rw [closedBall_eq_signedCube_halfspaces]
    ext x
    constructor
    · intro hx A hA
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
      exact sub_nonpos.mpr (hx i)
    · intro hx i
      exact sub_nonpos.mp (hx (B i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  obtain ⟨K, hK, hKT⟩ := hT.exists_finite_triangulation_of_halfspaces H hrep
  let L : (ι → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  let A : (ι → ℝ) →ᵃ[ℝ] ℝ := AffineMap.const ℝ _ r - L.toAffineMap
  have heval (x : ι → ℝ) : A x = r - ∑ i, x i := by simp [A, L]
  have hconst (t : ℝ) : A (fun _ => t) = r - (Fintype.card ι : ℝ) * t := by
    simp [heval]
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  let z := r / (Fintype.card ι : ℝ)
  have hzlo : -1 < z := (lt_div_iff₀ hcard).mpr (by linarith)
  have hzhi : z < 1 := (div_lt_iff₀ hcard).mpr (by linarith)
  have hzsum : (Fintype.card ι : ℝ) * z = r := by
    dsimp [z]
    field_simp
  have hint (t : ℝ) (htlo : -1 < t) (hthi : t < 1) : (fun _ : ι => t) ∈ interior T := by
    apply Metric.ball_subset_interior_closedBall
    simpa only [Metric.mem_ball, dist_zero_right, pi_norm_const, Real.norm_eq_abs,
      abs_lt] using And.intro htlo hthi
  have hneg : ∃ q ∈ interior T, A q < 0 := by
    refine ⟨fun _ => (z + 1) / 2, hint _ (by linarith) (by linarith), ?_⟩
    rw [hconst]
    nlinarith
  have hplane : ∃ w ∈ interior T, A w = 0 :=
    ⟨fun _ => z, hint z hzlo hzhi, by rw [hconst, hzsum, sub_self]⟩
  have hpair := K.isFinitePLBallPair_convex_frontier_affine_cap hK hT
    (convex_closedBall _ _) hKT A hneg hplane (by simpa using hdim)
  simpa only [heval, sub_nonneg, sub_eq_zero, eq_comm] using hpair

theorem exists_cube_frontier_disk_of_compact_with_open_interior {s : Set (ι → ℝ)}
    (hs : IsCompact s) (hsub : s ⊆ frontier (Metric.closedBall (0 : ι → ℝ) 1))
    (hp : (fun _ : ι => (1 : ℝ)) ∉ s)
    (hdim : Fintype.card ι = Module.finrank ℝ F + 1) :
    ∃ d q : Set (ι → ℝ), IsFinitePLBallPair F d q ∧
      d ⊆ frontier (Metric.closedBall (0 : ι → ℝ) 1) ∧ s ⊆ d \ q ∧
      (fun _ : ι => (1 : ℝ)) ∉ d ∧
      IsOpen ((Subtype.val : frontier (Metric.closedBall (0 : ι → ℝ) 1) → (ι → ℝ)) ⁻¹'
        (d \ q)) := by
  obtain ⟨r, hrlo, hrhi, hsr⟩ := exists_cube_cutting_level hs
    (hsub.trans (isCompact_closedBall (0 : ι → ℝ) 1).isClosed.frontier_subset) hp
  refine ⟨_, _, isFinitePLBallPair_cube_frontier_cut hrlo hrhi hdim,
    inter_subset_left, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨hsub hx, (hsr x hx).le⟩, fun hq => (hsr x hx).ne hq.2⟩
  · intro hp
    have h := hp.2
    simp only [mem_ofPred_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    exact hrhi.not_ge h
  · have heq : (Subtype.val : frontier (Metric.closedBall (0 : ι → ℝ) 1) → (ι → ℝ)) ⁻¹'
        ((frontier (Metric.closedBall (0 : ι → ℝ) 1) ∩ {x | ∑ i, x i ≤ r}) \
          (frontier (Metric.closedBall (0 : ι → ℝ) 1) ∩ {x | ∑ i, x i = r})) =
        {x : frontier (Metric.closedBall (0 : ι → ℝ) 1) | ∑ i, (x : ι → ℝ) i < r} := by
      ext x
      simp only [mem_preimage, mem_sdiff, mem_inter_iff, mem_ofPred_eq, x.property,
        true_and, lt_iff_le_and_ne]
    rw [heq]
    exact isOpen_lt (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).comp continuous_subtype_val) continuous_const

theorem exists_cube_frontier_disk_of_compact {s : Set (ι → ℝ)}
    (hs : IsCompact s) (hsub : s ⊆ frontier (Metric.closedBall (0 : ι → ℝ) 1))
    (hp : (fun _ : ι => (1 : ℝ)) ∉ s)
    (hdim : Fintype.card ι = Module.finrank ℝ F + 1) :
    ∃ d q : Set (ι → ℝ), IsFinitePLBallPair F d q ∧
      d ⊆ frontier (Metric.closedBall (0 : ι → ℝ) 1) ∧ s ⊆ d \ q ∧
      (fun _ : ι => (1 : ℝ)) ∉ d := by
  obtain ⟨d, q, hd, hds, hsq, hpd, _⟩ :=
    exists_cube_frontier_disk_of_compact_with_open_interior hs hsub hp hdim
  exact ⟨d, q, hd, hds, hsq, hpd⟩

end Geometry
