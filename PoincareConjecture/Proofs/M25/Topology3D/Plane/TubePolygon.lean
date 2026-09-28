import PoincareConjecture.Proofs.M25.Topology3D.Plane.InscribedPolygon
import PoincareConjecture.Proofs.M25.Topology3D.Plane.MonotoneChords

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

theorem exists_strict_circle_mesh {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ s : Fin (n + 1) → ℝ,
      StrictMono s ∧ s 0 = 0 ∧ s (Fin.last n) = 2 * Real.pi ∧
        ∀ i : Fin n, s i.succ - s i.castSucc < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 : ℝ) (2 * Real.pi / ε))
  have hn2 : (2 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hn3 : 3 ≤ n := by
    have : 2 < n := by exact_mod_cast hn2
    omega
  have hn0 : (0 : ℝ) < n := by linarith
  let v : ℝ := 2 * Real.pi / n
  have hv : 0 < v := div_pos (by positivity) hn0
  have hvε : v < ε := by
    have hdiv : 2 * Real.pi / ε < n := (le_max_right _ _).trans_lt hn
    apply (div_lt_iff₀ hn0).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hdiv
  refine ⟨n, hn3, fun i => (i.val : ℝ) * v, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) hv
  · simp
  · change (n : ℝ) * (2 * Real.pi / n) = 2 * Real.pi
    field_simp
  · intro i
    change ((i.val + 1 : ℕ) : ℝ) * v - (i.val : ℝ) * v < ε
    push_cast
    nlinarith

theorem exists_uniform_inscribed_tube_polygons
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : ℂ ≃ₗᵢ[ℝ] E) (q0 : sphere (0 : E) 1)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    (hx : ∀ y ∈ T.target, (T.symm y).2 ≠ 0)
    {K : Set ℝ} (hK : IsCompact K) {c d : ℝ → ℝ → E}
    (hc : ContinuousOn (fun a : ℝ × ℝ => c a.1 a.2) (K ×ˢ Icc 0 (2 * Real.pi)))
    (hd : ∀ z ∈ K, ∀ a ∈ Icc 0 (2 * Real.pi), HasDerivAt (c z) (d z a) a)
    (hcont : ContinuousOn (fun a : ℝ × ℝ => d a.1 a.2) (K ×ˢ Icc 0 (2 * Real.pi)))
    (htarget : ∀ z ∈ K, ∀ a ∈ Icc 0 (2 * Real.pi), (z, c z a) ∈ T.target)
    (hproj : ∀ z ∈ K, ∀ a : ℝ,
      curveTubeProjection q0 T (z, c z a) = sphereCircleParameter e a)
    (hloop : ∀ z ∈ K, c z (2 * Real.pi) = c z 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ s : Fin (n + 1) → ℝ,
      StrictMono s ∧ s 0 = 0 ∧ s (Fin.last n) = 2 * Real.pi ∧
      (∀ i : Fin n, s i.succ - s i.castSucc < ε) ∧
      ∀ z ∈ K, IsSimplePolygon (inscribedPolygon (c z) s) ∧
        MapsTo (fun y => (z, y)) ((inscribedPolygon (c z) s).boundary ℝ) T.target ∧
        BijOn (fun y => curveTubeProjection q0 T (z, y))
          ((inscribedPolygon (c z) s).boundary ℝ) univ := by
  obtain ⟨δ, hδ, _, hshort⟩ := exists_uniform_monotone_tube_chords e q0 T hInv hx hK
    hc hd hcont htarget hproj
  obtain ⟨n, hn, s, hs, hs0, hsN, hmesh⟩ := exists_strict_circle_mesh (lt_min hε hδ)
  have hsI : ∀ k, s k ∈ Icc 0 (2 * Real.pi) := by
    intro k
    constructor
    · rw [← hs0]
      exact hs.monotone (Fin.zero_le k)
    · rw [← hsN]
      exact hs.monotone (Fin.le_last k)
  refine ⟨n, hn, s, hs, hs0, hsN,
    fun i => (hmesh i).trans_le (min_le_left _ _), ?_⟩
  intro z hz
  let p := inscribedPolygon (c z) s
  let g : Fin n → ℝ → ℝ := fun i t => curveTubeAngle e q0 T ((z, s i.castSucc), p.edgePath ℝ i t)
  have hedge : ∀ i, p.edgePath ℝ i =
      AffineMap.lineMap (c z (s i.castSucc)) (c z (s i.succ)) := by
    apply inscribedPolygon_edgePath (c z) s
    simpa only [hsN, hs0] using hloop z hz
  have hch := fun i : Fin n => hshort z hz (s i.castSucc) (hsI i.castSucc)
    (s i.succ) (hsI i.succ) (hs (show i.castSucc < i.succ by exact Nat.lt_succ_self _))
      ((hmesh i).trans_le (min_le_right _ _))
  have hm : ∀ i, StrictMonoOn (g i) (Icc (0 : ℝ) 1) := by
    intro i
    simpa only [g, hedge] using (hch i).2.1
  have himg : ∀ i, g i '' Icc (0 : ℝ) 1 = Icc (s i.castSucc) (s i.succ) := by
    intro i
    simpa only [g, hedge] using (hch i).2.2
  have hrecover : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
      curveTubeProjection q0 T (z, p.edgePath ℝ i t) = sphereCircleParameter e (g i t) := by
    intro i t _
    exact (sphereCircleParameter_curveTubeAngle e q0 T ((z, s i.castSucc), p.edgePath ℝ i t)).symm
  obtain ⟨hsimple, hbij⟩ := inscribedPolygon_simple_and_bijOn_projection e (c z)
    (fun y => curveTubeProjection q0 T (z, y)) hn s hs hs0 hsN (hloop z hz) g hm himg hrecover
  refine ⟨hsimple, ?_, hbij⟩
  intro y hy
  obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff p y).mp hy
  obtain ⟨t, ht, rfl⟩ := hi
  have hdomain := ((hch i).1 t ht).1
  rw [← hedge i] at hdomain
  exact hdomain.1

end PoincareConjecture.M25.Topology3D
