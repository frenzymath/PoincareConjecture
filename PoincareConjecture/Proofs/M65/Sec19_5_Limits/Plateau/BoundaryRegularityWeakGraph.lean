import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityDiameter
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityWeakGreen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff SchwartzMap ENNReal

namespace PoincareConjecture.M65Boundary

theorem weakTrace_boundary_halfDisk_uniform :
    ∃ R : ℝ, 0 < R ∧ ∀ (p : ℂ), ‖p‖ = 1 →
      ∀ (u : Lp ℝ 2 (volume.restrict loopDiskSet))
        (d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet))
        (b : Lp ℝ 2 m65CircleBoundaryMeasure),
      M65DiskWeakTrace u d (m65CircleBoundaryPullback b) →
      let K := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
      let P := diskBoundaryCoordinate p
      ∃ (U : Lp ℝ 2 (volume.restrict K))
        (D : Fin 2 → Lp ℝ 2 (volume.restrict K))
        (B : Lp ℝ 2 (volume.restrict (Icc (-R) R))),
        U =ᵐ[volume.restrict K] (fun z => u (P z)) ∧
        (∀ i, D i =ᵐ[volume.restrict K] fun z =>
          ∑ j : Fin 2, (fderiv ℝ P z (EuclideanSpace.basisFun (Fin 2) ℝ i)) j * d j (P z)) ∧
        B =ᵐ[volume.restrict (Icc (-R) R)] (fun s =>
          b (P (s • EuclideanSpace.basisFun (Fin 2) ℝ 0))) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᵐ r ∂volume.restrict (Icc ε R),
          MemLp (fun θ => -r * Real.sin θ * D 0 (r • Proofs.M58.angularPoint θ) +
            r * Real.cos θ * D 1 (r • Proofs.M58.angularPoint θ))
              2 (volume.restrict (Icc (0 : ℝ) Real.pi)) ∧
          ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v 0 Real.pi ∧
            (v =ᵐ[volume.restrict (Icc (0 : ℝ) Real.pi)]
              fun θ => U (r • Proofs.M58.angularPoint θ)) ∧
            v 0 = B r ∧ v Real.pi = B (-r) ∧
            (∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
              v t - v s = ∫ θ in s..t,
                -r * Real.sin θ * D 0 (r • Proofs.M58.angularPoint θ) +
                  r * Real.cos θ * D 1 (r • Proofs.M58.angularPoint θ)) ∧
            ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2),
              (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
                D i z * test z + U z *
                  fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
                r * (∫ θ in (0 : ℝ)..Real.pi,
                  v θ * test (r • Proofs.M58.angularPoint θ) *
                    Proofs.M58.angularPoint θ i) -
                  (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
                    ∫ s in (-r)..r, B s * test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
  obtain ⟨R0, hR0, hgraph⟩ := boundary_smooth_graph_uniform
  let R := min R0 Real.pi
  have hR : 0 < R := lt_min hR0 Real.pi_pos
  have hRR0 : R ≤ R0 := min_le_left _ _
  have hRπ : R ≤ Real.pi := min_le_right _ _
  refine ⟨R, hR, ?_⟩
  intro p hp u d b htrace
  obtain ⟨f, A0, D0, C, U0, d0, hf, hA0, hD0, hC, hU0, hd0,
      hAU, hDd, hCb⟩ := hgraph p hp u d b htrace
  let K0 := closedBall (0 : LoopPlane) R0 ∩ {z | 0 ≤ z 1}
  let K := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
  let μ0 := volume.restrict K0
  let μ := volume.restrict K
  let P := diskBoundaryCoordinate p
  have hKK0 : K ⊆ K0 := inter_subset_inter (closedBall_subset_closedBall hRR0) Subset.rfl
  have hμ : μ ≤ (1 : ENNReal) • μ0 := by
    simpa only [one_smul] using (Measure.restrict_mono hKK0 le_rfl : μ ≤ μ0)
  let T : Lp ℝ 2 μ0 →L[ℝ] Lp ℝ 2 μ :=
    Lp.LpToLpOfMeasureLeSMul (by norm_num : (1 : ENNReal) ≠ ⊤) hμ
  have hT (V : Lp ℝ 2 μ0) : T V =ᵐ[μ] V :=
    Lp.coeFn_LpToLpOfMeasureLeSMul (by norm_num : (1 : ENNReal) ≠ ⊤) hμ V
  let A (n : ℕ) := T (A0 n)
  let Ds (n : ℕ) (i : Fin 2) := T (D0 n i)
  let U := T U0
  let D (i : Fin 2) := T (d0 i)
  have hAn (n : ℕ) : A n =ᵐ[μ] fun z => f n (P z) :=
    (hT (A0 n)).trans (ae_restrict_of_ae_restrict_of_subset hKK0 (hA0 n))
  have hDn (n : ℕ) (i : Fin 2) : Ds n i =ᵐ[μ]
      fun z => fderiv ℝ (f n ∘ P) z (EuclideanSpace.basisFun (Fin 2) ℝ i) :=
    (hT (D0 n i)).trans (ae_restrict_of_ae_restrict_of_subset hKK0 (hD0 n i))
  have hU : U =ᵐ[μ] fun z => u (P z) :=
    (hT U0).trans (ae_restrict_of_ae_restrict_of_subset hKK0 hU0)
  have hD (i : Fin 2) : D i =ᵐ[μ] fun z =>
      ∑ j : Fin 2, (fderiv ℝ P z (EuclideanSpace.basisFun (Fin 2) ℝ i)) j * d j (P z) :=
    (hT (d0 i)).trans (ae_restrict_of_ae_restrict_of_subset hKK0 (hd0 i))
  have hAlim : Tendsto A atTop (𝓝 U) := (T.continuous.tendsto U0).comp hAU
  have hDlim (i : Fin 2) : Tendsto (fun n => Ds n i) atTop (𝓝 (D i)) :=
    (T.continuous.tendsto (d0 i)).comp (hDd i)
  obtain ⟨Bseq, B, hBseq, hB, hBlim⟩ := diameter_boundary_graph hp hRπ f C b hC hCb
  have hfs (n : ℕ) : ContDiff ℝ 1 (f n ∘ P) :=
    ((hf n).comp (contDiff_diskBoundaryCoordinate p)).of_le (by simp)
  refine ⟨U, D, B, hU, hD, hB, ?_⟩
  intro ε hε
  have hGreen := halfDisk_graph_green hε (le_refl R) (fun n => f n ∘ P) hfs
    A Ds U D Bseq B hAn hDn hBseq hAlim hDlim hBlim
  have hAC := halfDisk_graph_AC hε (le_refl R) (fun n => f n ∘ P) hfs
    A Ds U D Bseq B hAn hDn hBseq hAlim hDlim hBlim
  filter_upwards [hGreen, hAC] with r hrG hrA
  obtain ⟨_hMemU, hGr⟩ := hrG
  obtain ⟨hMemD, v, hvAC, hvU, hv0, hvπ, hvint⟩ := hrA
  refine ⟨hMemD, v, hvAC, hvU, hv0, hvπ, hvint, ?_⟩
  intro test i
  rw [hGr test i]
  congr 2
  apply intervalIntegral.integral_congr_ae_restrict
  have hv : v =ᵐ[volume.restrict (uIoc (0 : ℝ) Real.pi)]
      fun θ => U (r • Proofs.M58.angularPoint θ) := ae_restrict_of_ae_restrict_of_subset
    (by simpa only [uIoc_of_le Real.pi_pos.le] using Ioc_subset_Icc_self) hvU
  filter_upwards [hv] with θ hθ
  rw [hθ]

theorem weakTrace_boundary_halfDisk {p : ℂ} (hp : ‖p‖ = 1)
    {u : Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {b : Lp ℝ 2 m65CircleBoundaryMeasure}
    (htrace : M65DiskWeakTrace u d (m65CircleBoundaryPullback b)) :
    ∃ R : ℝ, 0 < R ∧
      let K := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
      let P := diskBoundaryCoordinate p
      ∃ (U : Lp ℝ 2 (volume.restrict K))
        (D : Fin 2 → Lp ℝ 2 (volume.restrict K))
        (B : Lp ℝ 2 (volume.restrict (Icc (-R) R))),
        U =ᵐ[volume.restrict K] (fun z => u (P z)) ∧
        (∀ i, D i =ᵐ[volume.restrict K] fun z =>
          ∑ j : Fin 2, (fderiv ℝ P z (EuclideanSpace.basisFun (Fin 2) ℝ i)) j * d j (P z)) ∧
        B =ᵐ[volume.restrict (Icc (-R) R)] (fun s =>
          b (P (s • EuclideanSpace.basisFun (Fin 2) ℝ 0))) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᵐ r ∂volume.restrict (Icc ε R),
          MemLp (fun θ => -r * Real.sin θ * D 0 (r • Proofs.M58.angularPoint θ) +
            r * Real.cos θ * D 1 (r • Proofs.M58.angularPoint θ))
              2 (volume.restrict (Icc (0 : ℝ) Real.pi)) ∧
          ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v 0 Real.pi ∧
            (v =ᵐ[volume.restrict (Icc (0 : ℝ) Real.pi)]
              fun θ => U (r • Proofs.M58.angularPoint θ)) ∧
            v 0 = B r ∧ v Real.pi = B (-r) ∧
            (∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
              v t - v s = ∫ θ in s..t,
                -r * Real.sin θ * D 0 (r • Proofs.M58.angularPoint θ) +
                  r * Real.cos θ * D 1 (r • Proofs.M58.angularPoint θ)) ∧
            ∀ (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2),
              (∫ z in closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1},
                D i z * test z + U z *
                  fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
                r * (∫ θ in (0 : ℝ)..Real.pi,
                  v θ * test (r • Proofs.M58.angularPoint θ) *
                    Proofs.M58.angularPoint θ i) -
                  (EuclideanSpace.basisFun (Fin 2) ℝ 1) i *
                    ∫ s in (-r)..r, B s * test (s • EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
  obtain ⟨R, hR, hgraph⟩ := weakTrace_boundary_halfDisk_uniform
  exact ⟨R, hR, hgraph p hp u d b htrace⟩

end PoincareConjecture.M65Boundary
