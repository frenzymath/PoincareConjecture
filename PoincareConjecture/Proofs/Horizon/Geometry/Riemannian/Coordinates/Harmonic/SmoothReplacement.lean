import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.WeakDivergence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.WeakCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Classical
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.InteriorRegularity

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω Ω' : Set M}

theorem exists_smooth_weakPoisson_replacement [PreconnectedSpace M]
    (hn : 0 < n) (hΩo : IsOpen Ω) (hΩ : Ω ⊆ Ω') {P : ℝ}
    (hP0 : 0 ≤ P) (hP : HasTestPoincare D Ω P) (q : EnergyTest D Ω') :
    ∃ U : M → ℝ, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω ∧
      U =ᵐ[g.volumeMeasure.restrict Ω]
        (testToL2 D Ω' q + toL2 D Ω (weakPoisson D Ω hP0 hP q.laplacianLp) :
          Lp ℝ 2 g.volumeMeasure) ∧
      ∀ x ∈ Ω, D.laplacian U x = 0 := by
  let w := weakPoisson D Ω hP0 hP q.laplacianLp
  let u : H1Zero D Ω' := (q : H1Zero D Ω') + inclusion hΩ w
  have hu : toL2 D Ω' u = testToL2 D Ω' q + toL2 D Ω w := by
    simp only [u, map_add, toL2_coe, toL2_inclusion]
  have hrepresentative : ∃ U : M → ℝ,
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω ∧
      U =ᵐ[g.volumeMeasure.restrict Ω] (toL2 D Ω' u : M → ℝ) := by
    apply exists_smooth_representative_of_local hΩo (toL2 D Ω' u)
    intro x hx
    obtain ⟨e, he, hei, K, hK, hKs, O, hO, hOK, hxO, hOΩ, -⟩ :=
      exists_precompact_coordinate_neighborhood (n := n) hΩo hx
    have hOs := hOK.trans hKs
    let p (i : Fin n) := localCoordinateDerivative (D := D) (Ω := Ω')
      e he hei hK hKs hOK (EuclideanSpace.single i 1) u
    have huL2 : MemLp (fun y => toL2 D Ω' u (e y)) 2 (volume.restrict O) :=
      (g.memLp_pullback_on_compact e he hei (toL2 D Ω' u) hK hKs).mono_measure
        (Measure.restrict_mono hOK le_rfl)
    have hpL2 (i : Fin n) : MemLp (p i) 2 (volume.restrict O) := Lp.memLp (p i)
    obtain ⟨V, hVs, hVae⟩ : ∃ V : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiffOn ℝ ∞ V O ∧
          V =ᵐ[volume.restrict O] (fun y => toL2 D Ω' u (e y)) := by
      apply Poincare.Analysis.Elliptic.exists_smooth_representative hn hO
        (divergenceCoefficients g e) (fun _ => 0)
        (fun y => toL2 D Ω' u (e y)) (fun i y => p i y)
      · intro i j
        exact (contDiffOn_divergenceCoefficients e he hei i j).mono hOs
      · intro y hy
        apply Matrix.PosDef.of_dotProduct_mulVec_pos
        · ext i j
          change divergenceCoefficients g e y j i = divergenceCoefficients g e y i j
          exact divergenceCoefficients_symm e he hei (hOs hy) j i
        · intro v hv
          have hv' : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
            intro hz
            apply hv
            exact congrArg WithLp.ofLp hz
          have hpos := divergenceCoefficients_pos (g := g) e he hei (hOs hy)
            (WithLp.toLp 2 v) hv'
          simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
            Finset.mul_sum, PiLp.toLp_apply, mul_left_comm, mul_comm, mul_assoc] using hpos
      · exact contDiffOn_const
      · intro K _ hKO
        exact huL2.mono_measure (Measure.restrict_mono hKO le_rfl)
      · intro i K _ hKO
        exact (hpL2 i).mono_measure (Measure.restrict_mono hKO le_rfl)
      · intro i φ hφ hc hs
        exact localCoordinateDerivative_weak e he hei hK hKs hOK hO u i hφ hc hs
      · intro φ hφ hc hs
        simpa only [zero_mul, integral_zero] using
          weakPoisson_replacement_divergence_local hΩ hP0 hP q
            e he hei hK hKs hOK hOΩ hφ hc hs
    obtain ⟨F, hFs, hFae⟩ := g.exists_smooth_representative_on_coordinate_image
      e he hei hO hOs (toL2 D Ω' u) hVs hVae
    exact ⟨e '' O, e.isOpen_image_of_subset_source hO hOs, hxO, hOΩ, F, hFs, hFae⟩
  obtain ⟨U, hUs, hU⟩ := hrepresentative
  rw [hu] at hU
  exact ⟨U, hUs, hU, laplacian_eq_zero_of_smooth_weakHarmonicReplacement
    hΩo (testToL2 D Ω' q) w (weakPoisson_isWeakHarmonicReplacement hP0 hP q) hUs hU⟩

end PoincareConjecture.LeviCivitaData.Dirichlet

namespace PoincareConjecture.HarmonicCoordinates

open LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n]
  {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem exists_smooth_weakHarmonicReplacement_of_smooth (D : LeviCivitaData g)
    {R : ℝ} (hR : 0 < R) {q : EuclideanSpace ℝ (Fin n) → ℝ}
    (hq : ContDiff ℝ ∞ q) (w : H1Zero D (Metric.ball 0 R))
    (hw : ∀ f : EnergyTest D (Metric.ball 0 R),
      (∫ x, (q x + (toL2 D (Metric.ball 0 R) w) x) *
        D.laplacian f x ∂g.volumeMeasure) = 0) :
    ∃ U : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ ∞ U (Metric.ball 0 R) ∧
      U =ᵐ[g.volumeMeasure.restrict (Metric.ball 0 R)]
        (fun x => q x + (toL2 D (Metric.ball 0 R) w) x) ∧
      ∀ x ∈ Metric.ball 0 R, D.laplacian U x = 0 := by
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨R, 2 * R, hR, by linarith⟩
  let Q : EnergyTest D (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    ⟨fun x => b x * q x, contMDiff_iff_contDiff.mpr (b.contDiff.mul hq),
      b.hasCompactSupport.mul_right, subset_univ _⟩
  have hQeq (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 R) : Q x = q x := by
    have hb : b x = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    change b x * q x = q x
    rw [hb, one_mul]
  obtain ⟨P, hP0, hP⟩ := exists_metric_poincare_on_ball g D hR
  have hwQ : IsWeakHarmonicReplacement (testToL2 D Set.univ Q) w := by
    apply (isWeakHarmonicReplacement_iff_integral Q w).mpr
    intro f
    rw [← hw f]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (Q x + (toL2 D (Metric.ball 0 R) w) x) * D.laplacian f x =
        (q x + (toL2 D (Metric.ball 0 R) w) x) * D.laplacian f x
      by_cases hx : x ∈ Metric.ball 0 R
      · rw [hQeq x hx]
      · have hz := D.laplacian_eq_zero_of_notMem_tsupport
          (f := (f : EuclideanSpace ℝ (Fin n) → ℝ)) (fun ht => hx (f.support_subset ht))
        simp only [hz, mul_zero]
  have hwident : w = weakPoisson D (Metric.ball 0 R) hP0 hP Q.laplacianLp :=
    (existsUnique_weakHarmonicReplacement hP0 hP Q).unique hwQ
      (weakPoisson_isWeakHarmonicReplacement hP0 hP Q)
  obtain ⟨U, hUs, hU, hUharm⟩ := exists_smooth_weakPoisson_replacement
    (Nat.pos_of_ne_zero (NeZero.ne n)) Metric.isOpen_ball (subset_univ _) hP0 hP Q
  rw [← hwident] at hU
  refine ⟨U, hUs.contDiffOn, ?_, hUharm⟩
  filter_upwards [hU,
    ae_restrict_of_ae (Lp.coeFn_add (testToL2 D Set.univ Q) (toL2 D (Metric.ball 0 R) w)),
    ae_restrict_of_ae Q.memLp.coeFn_toLp,
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hadd hQ hxB
  rw [hx, hadd, Pi.add_apply, show (testToL2 D Set.univ Q) x = Q x from hQ, hQeq x hxB]

theorem exists_smooth_harmonicReplacement_on_ball (D : LeviCivitaData g)
    {R : ℝ} (hR : 0 < R) {q : EuclideanSpace ℝ (Fin n) → ℝ}
    (hq : ContDiff ℝ ∞ q) :
    ∃ w : H1Zero D (Metric.ball 0 R), ∃ U : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ ∞ U (Metric.ball 0 R) ∧
      U =ᵐ[g.volumeMeasure.restrict (Metric.ball 0 R)]
        (fun x => q x + (toL2 D (Metric.ball 0 R) w) x) ∧
      ∀ x ∈ Metric.ball 0 R, D.laplacian U x = 0 := by
  obtain ⟨w, hw, -⟩ := existsUnique_weakHarmonicReplacement_of_smooth D hR hq
  exact ⟨w, exists_smooth_weakHarmonicReplacement_of_smooth D hR hq w hw⟩

end PoincareConjecture.HarmonicCoordinates
