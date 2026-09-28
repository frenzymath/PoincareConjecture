import PoincareConjecture.Proofs.Horizon.Topology.Plane.Triangles.CapSeparation
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Vertices.Trimming
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
open Set
open scoped ContDiff Topology Manifold
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

private theorem separator_deriv_pos_of_reparam
    {f g : ℝ → EuclideanSpace ℝ (Fin 2)} (A : OpenPartialHomeomorph ℝ ℝ)
    {ε t : ℝ} (hε : 0 < ε) (hAt : A ε = t)
    (hsource : Icc 0 ε ⊆ A.source) (hmono : StrictMonoOn A A.source)
    (hA : ContDiffOn ℝ ∞ A A.source)
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g ε)
    (heq : EqOn (f ∘ A) g (Icc 0 ε))
    (ℓ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (hnorm : ℓ (deriv g ε) = 1) :
    0 < ℓ (deriv f t) := by
  have hεI : ε ∈ Icc (0 : ℝ) ε := ⟨hε.le, le_rfl⟩
  have hεA := hsource hεI
  have hAd := ((hA ε hεA).contDiffAt (A.open_source.mem_nhds hεA)).differentiableAt (by simp)
  have hfd : HasDerivAt f (deriv f t) (A ε) := hAt ▸ hf.hasDerivAt
  have hcomp : HasDerivWithinAt (f ∘ A) (deriv A ε • deriv f t) (Icc 0 ε) ε :=
    (hfd.scomp ε hAd.hasDerivAt).hasDerivWithinAt
  have hcomp' : HasDerivWithinAt g (deriv A ε • deriv f t) (Icc 0 ε) ε :=
    hcomp.congr_of_mem (fun u hu => (heq hu).symm) hεI
  have hvec : deriv A ε • deriv f t = deriv g ε :=
    (uniqueDiffOn_Icc hε ε hεI).eq_deriv _ hcomp' hg.hasDerivAt.hasDerivWithinAt
  have hmul : deriv A ε * ℓ (deriv f t) = 1 := by
    simpa only [map_smul, smul_eq_mul, hnorm] using congrArg ℓ hvec
  have hnonneg : 0 ≤ deriv A ε := by
    rw [← derivWithin_of_isOpen A.open_source hεA]
    exact hmono.monotoneOn.derivWithin_nonneg
  exact pos_of_mul_pos_right (by rw [hmul]; norm_num) hnonneg

namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))

omit [T2Space M] in
theorem edgeFromEndpoint_contMDiff (a : D.EdgeIndex) (terminal : Bool) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (D.edgeFromEndpoint a terminal) := by
  cases terminal
  · exact D.edge_contMDiff a
  · exact (D.edge_contMDiff a).comp ((contDiff_const.sub contDiff_id).contMDiff)

omit [T2Space M] in

theorem edgeFromEndpoint_coordinate_deriv (a : D.EdgeIndex) (terminal : Bool)
    (x : M) (t : ℝ) :
    deriv (chartAt (EuclideanSpace ℝ (Fin 2)) x ∘ D.edgeFromEndpoint a terminal) t =
      if terminal then
        -deriv (chartAt (EuclideanSpace ℝ (Fin 2)) x ∘ (D.edge a.1 a.2).map) (1 - t)
      else deriv (chartAt (EuclideanSpace ℝ (Fin 2)) x ∘ (D.edge a.1 a.2).map) t := by
  cases terminal
  · rfl
  · exact deriv_comp_const_sub
      (f := fun u => chartAt (EuclideanSpace ℝ (Fin 2)) x ((D.edge a.1 a.2).map u))
      (a := 1) (x := t)

theorem exists_edge_cap_separator
    {p : M} {P : ChartCircleArrangementVertexPatch D.radius p}
    {x : Bool × Bool → M} (B : ChartCircleArrangementVertexPatch.VertexCapFaces P x)
    (s : Bool × Bool) (a : D.EdgeIndex) (terminal vertical : Bool)
    {cut : ℝ} (A : OpenPartialHomeomorph ℝ ℝ)
    (hAt : A B.scale = cut) (hsource : Icc 0 B.scale ⊆ A.source)
    (hmono : StrictMonoOn A A.source) (hA : ContDiffOn ℝ ∞ A A.source)
    (hcurve : ∀ u ∈ Icc 0 B.scale, D.edgeFromEndpoint a terminal (A u) =
      P.sectorCoordinates s (if vertical then (0, u) else (u, 0))) :
    ∃ (ℓ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (W : Set (EuclideanSpace ℝ (Fin 2))),
      IsOpen W ∧
      chartAt (EuclideanSpace ℝ (Fin 2)) (x s) (D.edgeFromEndpoint a terminal cut) ∈ W ∧
      0 < ℓ (deriv (chartAt (EuclideanSpace ℝ (Fin 2)) (x s) ∘
        D.edgeFromEndpoint a terminal) cut) ∧
      (if terminal then
        ℓ (deriv (chartAt (EuclideanSpace ℝ (Fin 2)) (x s) ∘
          (D.edge a.1 a.2).map) (1 - cut)) < 0
       else 0 < ℓ (deriv (chartAt (EuclideanSpace ℝ (Fin 2)) (x s) ∘
          (D.edge a.1 a.2).map) cut)) ∧
      (∀ t : ℝ, ℓ ((1 - t) • B.planarCoordinates s (B.scale, 0) +
        t • B.planarCoordinates s (0, B.scale) -
          chartAt (EuclideanSpace ℝ (Fin 2)) (x s) (D.edgeFromEndpoint a terminal cut)) = 0) ∧
      ∀ q ∈ (B.face s).carrier,
        chartAt (EuclideanSpace ℝ (Fin 2)) (x s) q ∈ W →
        ℓ (chartAt (EuclideanSpace ℝ (Fin 2)) (x s) q -
          chartAt (EuclideanSpace ℝ (Fin 2)) (x s) (D.edgeFromEndpoint a terminal cut)) ≤ 0 := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) (x s)
  let F := B.planarCoordinates s
  let axis : ℝ → ℝ × ℝ := fun u => if vertical then (0, u) else (u, 0)
  let g : ℝ → EuclideanSpace ℝ (Fin 2) := F ∘ axis
  have hεI : B.scale ∈ Icc (0 : ℝ) B.scale := ⟨B.scale_pos.le, le_rfl⟩
  have haxis : ContDiff ℝ ∞ axis := by cases vertical <;> dsimp [axis] <;> fun_prop
  have haxis_source : axis B.scale ∈ F.source := by
    apply B.planar_source s
    cases vertical <;> simp [axis, B.scale_pos.le]
  have hplanar (u : ℝ) (hu : u ∈ Icc (0 : ℝ) B.scale) :
      g u = c (P.sectorCoordinates s (axis u)) := by
    cases vertical
    · exact B.planar_first s u hu
    · exact B.planar_second s u hu
  have hbase : g B.scale = c (D.edgeFromEndpoint a terminal cut) := by
    rw [hplanar _ hεI, ← hcurve _ hεI, hAt]
  have hcutcap : D.edgeFromEndpoint a terminal cut ∈ (B.face s).carrier := by
    rw [← hAt, hcurve _ hεI]
    cases vertical
    · exact B.firstSide_subset_carrier s ⟨B.scale, hεI, rfl⟩
    · exact B.secondSide_subset_carrier s ⟨B.scale, hεI, rfl⟩
  have hcutchart := B.carrier_subset_chart s hcutcap
  have hf : DifferentiableAt ℝ (c ∘ D.edgeFromEndpoint a terminal) cut := by
    have hs : ContDiffOn ℝ ∞ (c ∘ D.edgeFromEndpoint a terminal)
        (D.edgeFromEndpoint a terminal ⁻¹' c.source) :=
      ((contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := x s)).comp
        (D.edgeFromEndpoint_contMDiff a terminal).contMDiffOn (fun _ ht => ht)).contDiffOn
    exact ((hs cut hcutchart).contDiffAt
      ((c.open_source.preimage (D.edgeFromEndpoint_contMDiff a terminal).continuous).mem_nhds
        hcutchart)).differentiableAt (by simp)
  have hg : DifferentiableAt ℝ g B.scale :=
    (((B.planar_smooth s _ haxis_source).contDiffAt
      (F.open_source.mem_nhds haxis_source)).differentiableAt (by simp)).comp
        B.scale ((haxis.differentiable (by simp)) B.scale)
  have heq : EqOn ((c ∘ D.edgeFromEndpoint a terminal) ∘ A) g (Icc 0 B.scale) := by
    intro u hu
    change c (D.edgeFromEndpoint a terminal (A u)) = g u
    rw [hplanar u hu, hcurve u hu]
  obtain ⟨ℓ, W, hnorm, hchord, hW, hbaseW, _, hcap⟩ :=
    exists_cap_chord_separator F (B.planar_smooth s) (B.planar_smooth_symm s)
      B.scale_pos (B.planar_source s) (B.planar_chord s) vertical
  have hnorm' : ℓ (deriv g B.scale) = 1 := by
    cases vertical <;> exact hnorm
  have hpos := separator_deriv_pos_of_reparam A B.scale_pos hAt hsource hmono hA hf hg heq ℓ hnorm'
  have hbase' : (if vertical then F (0, B.scale) else F (B.scale, 0)) =
      c (D.edgeFromEndpoint a terminal cut) := by
    cases vertical <;> exact hbase
  refine ⟨ℓ, W, hW, hbase' ▸ hbaseW, hpos, ?_, ?_, ?_⟩
  · have h := hpos
    rw [D.edgeFromEndpoint_coordinate_deriv] at h
    cases terminal
    · exact h
    · simpa only [Bool.true_eq, ite_true, map_neg, neg_pos] using h
  · intro t
    change ℓ ((1 - t) • F (B.scale, 0) + t • F (0, B.scale) - _) = 0
    rw [← hbase']
    cases vertical
    · have heq : (1 - t) • F (B.scale, 0) + t • F (0, B.scale) - F (B.scale, 0) =
          t • (F (0, B.scale) - F (B.scale, 0)) := by module
      have hd : ℓ (F (0, B.scale) - F (B.scale, 0)) = 0 := hchord
      simp only [Bool.false_eq_true, ite_false, heq, map_smul, hd, smul_zero]
    · have heq : (1 - t) • F (B.scale, 0) + t • F (0, B.scale) - F (0, B.scale) =
          (1 - t) • (F (B.scale, 0) - F (0, B.scale)) := by module
      have hd : ℓ (F (B.scale, 0) - F (0, B.scale)) = 0 := hchord
      simp only [ite_true, heq, map_smul, hd, smul_zero]
  · intro q hq hqW
    rw [B.carrier_planar s] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    have hzchart : z ∈ c.target := by
      obtain ⟨u, hu, rfl⟩ := hz
      exact B.planar_target s ((B.planarCoordinates s).map_source (B.planar_source s hu))
    have hc : c (c.symm z) = z := c.right_inv hzchart
    change ℓ (c (c.symm z) - c (D.edgeFromEndpoint a terminal cut)) ≤ 0
    rw [hc, ← hbase']
    change c (c.symm z) ∈ W at hqW
    exact hcap z ⟨by simpa only [hc] using hqW, hz⟩

theorem exists_vertex_caps_with_edge_separators
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
    (hlocal : ∀ p q, q ∈ (P p).carrier →
      (q ∈ chartDiskBoundaryUnion D.centers D.radius ↔ q ∈ (P p).circles))
    (x : D.vertices → Bool × Bool → M)
    (hchart : ∀ p i, (P p).closedSector i ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x p i)).source) :
    ∃ (ε : ℝ) (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p) (x p))
      (cut : D.EdgeIndex → Bool → ℝ),
      0 < ε ∧ (∀ p, (B p).scale = ε) ∧
      ∀ (a : D.EdgeIndex) (terminal : Bool), cut a terminal ∈ Ioo (0 : ℝ) (1 / 3) ∧
        ∃ (i j : Bool × Bool) (k : Fin 3), i ≠ j ∧ (k = 1 ∨ k = 2) ∧
          (((B (D.edgeEndpoint a terminal)).face i).boundary k).map '' Icc (0 : ℝ) 1 =
            D.edgeFromEndpoint a terminal '' Icc 0 (cut a terminal) ∧
          (((B (D.edgeEndpoint a terminal)).face j).boundary k).map '' Icc (0 : ℝ) 1 =
            D.edgeFromEndpoint a terminal '' Icc 0 (cut a terminal) ∧
          ∀ s, s = i ∨ s = j →
            (((B (D.edgeEndpoint a terminal)).face s).boundary k).map 0 =
              (D.edgeEndpoint a terminal : M) ∧
            (((B (D.edgeEndpoint a terminal)).face s).boundary k).map 1 =
              D.edgeFromEndpoint a terminal (cut a terminal) ∧
            let B₀ := B (D.edgeEndpoint a terminal)
            let c := chartAt (EuclideanSpace ℝ (Fin 2)) (x (D.edgeEndpoint a terminal) s)
            ∃ (ℓ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
              (W : Set (EuclideanSpace ℝ (Fin 2))),
              IsOpen W ∧ c (D.edgeFromEndpoint a terminal (cut a terminal)) ∈ W ∧
              0 < ℓ (deriv (c ∘ D.edgeFromEndpoint a terminal) (cut a terminal)) ∧
              (if terminal then
                ℓ (deriv (c ∘ (D.edge a.1 a.2).map) (1 - cut a terminal)) < 0
               else 0 < ℓ (deriv (c ∘ (D.edge a.1 a.2).map) (cut a terminal))) ∧
              (∀ t : ℝ, ℓ ((1 - t) • B₀.planarCoordinates s (B₀.scale, 0) +
                t • B₀.planarCoordinates s (0, B₀.scale) -
                  c (D.edgeFromEndpoint a terminal (cut a terminal))) = 0) ∧
              ∀ q ∈ (B₀.face s).carrier, c q ∈ W →
                ℓ (c q - c (D.edgeFromEndpoint a terminal (cut a terminal))) ≤ 0 := by
  obtain ⟨ε, B, cut, hε, hscale, hmatching⟩ :=
    D.exists_vertex_caps_matching_edges P hlocal x hchart
  refine ⟨ε, B, cut, hε, hscale, ?_⟩
  intro a terminal
  obtain ⟨hcut, i, j, k, hij, hk, hi, hj, hends⟩ := hmatching a terminal
  refine ⟨hcut, i, j, k, hij, hk, hi, hj, ?_⟩
  intro s hs
  obtain ⟨h0, h1, A, hAt, hsource, hmono, hA, _, hcurve⟩ := hends s hs
  refine ⟨h0, h1, ?_⟩
  apply D.exists_edge_cap_separator (B (D.edgeEndpoint a terminal)) s a terminal
    (decide (k = 1)) A hAt hsource hmono hA
  simpa only [decide_eq_true_eq] using hcurve

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
