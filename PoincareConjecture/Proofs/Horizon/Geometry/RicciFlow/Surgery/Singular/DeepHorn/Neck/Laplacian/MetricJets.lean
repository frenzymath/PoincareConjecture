import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Laplacian.ScalarMap





noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

open Filter Set
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace PoincareConjecture.DeepHorn

section Calculus

variable {α E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {l : Filter α} {f : α → E → F} {f₀ : E → F} {x : E}

private theorem nat_le_infty (r : ℕ) : (r : ℕ∞ω) ≤ ∞ := by
  exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤)

theorem tendsto_jet_fderiv (r : ℕ)
    (h : Tendsto (fun i => iteratedFDeriv ℝ (r + 1) (f i) x) l
      (𝓝 (iteratedFDeriv ℝ (r + 1) f₀ x))) :
    Tendsto (fun i => iteratedFDeriv ℝ r (fderiv ℝ (f i)) x) l
      (𝓝 (iteratedFDeriv ℝ r (fderiv ℝ f₀) x)) := by
  have heq (q : E → F) : continuousMultilinearCurryRightEquiv' ℝ r E F
      (iteratedFDeriv ℝ (r + 1) q x) = iteratedFDeriv ℝ r (fderiv ℝ q) x := by
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  simpa only [Function.comp_def, heq] using
    (continuousMultilinearCurryRightEquiv' ℝ r E F).continuous.continuousAt.tendsto.comp h

theorem tendsto_jet_linear_comp (L : F →L[ℝ] G) (r : ℕ)
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) x) (hf₀ : ContDiffAt ℝ ∞ f₀ x)
    (h : Tendsto (fun i => iteratedFDeriv ℝ r (f i) x) l
      (𝓝 (iteratedFDeriv ℝ r f₀ x))) :
    Tendsto (fun i => iteratedFDeriv ℝ r (fun y => L (f i y)) x) l
      (𝓝 (iteratedFDeriv ℝ r (fun y => L (f₀ y)) x)) := by
  have hL : Continuous (fun A : E [×r]→L[ℝ] F => L.compContinuousMultilinearMap A) :=
    ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin r => E) F G) L).continuous
  simpa only [← L.iteratedFDeriv_comp_left (hf₀) (nat_le_infty r),
    ← L.iteratedFDeriv_comp_left (hf _) (nat_le_infty r), Function.comp_def] using
    hL.continuousAt.tendsto.comp h

theorem iteratedFDeriv_pi_eq {ι : Type*} [Fintype ι]
    {q : E → ι → F} (hq : ContDiffAt ℝ ∞ q x) (r : ℕ) :
    iteratedFDeriv ℝ r q x =
      ContinuousMultilinearMap.pi (fun j => iteratedFDeriv ℝ r (fun y => q y j) x) := by
  ext v j
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F) j).iteratedFDeriv_comp_left
    hq (nat_le_infty r)
  exact (congrArg (fun A => A v) h).symm

theorem tendsto_jet_pi {ι : Type*} [Fintype ι]
    {q : α → E → ι → F} {q₀ : E → ι → F}
    (hq : ∀ i, ContDiffAt ℝ ∞ (q i) x) (hq₀ : ContDiffAt ℝ ∞ q₀ x)
    (r : ℕ) (h : ∀ j, Tendsto (fun i => iteratedFDeriv ℝ r (fun y => q i y j) x) l
      (𝓝 (iteratedFDeriv ℝ r (fun y => q₀ y j) x))) :
    Tendsto (fun i => iteratedFDeriv ℝ r (q i) x) l
      (𝓝 (iteratedFDeriv ℝ r q₀ x)) := by
  simp_rw [iteratedFDeriv_pi_eq (hq _) r, iteratedFDeriv_pi_eq hq₀ r]
  exact (ContinuousMultilinearMap.piₗᵢ ℝ (fun _ : Fin r => E)).continuous.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr h)

theorem tendsto_jet_prod {q : α → E → G} {q₀ : E → G}
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) x) (hf₀ : ContDiffAt ℝ ∞ f₀ x)
    (hq : ∀ i, ContDiffAt ℝ ∞ (q i) x) (hq₀ : ContDiffAt ℝ ∞ q₀ x)
    (r : ℕ)
    (h : Tendsto (fun i => iteratedFDeriv ℝ r (f i) x) l
      (𝓝 (iteratedFDeriv ℝ r f₀ x)))
    (h' : Tendsto (fun i => iteratedFDeriv ℝ r (q i) x) l
      (𝓝 (iteratedFDeriv ℝ r q₀ x))) :
    Tendsto (fun i => iteratedFDeriv ℝ r (fun y => (f i y, q i y)) x) l
      (𝓝 (iteratedFDeriv ℝ r (fun y => (f₀ y, q₀ y)) x)) := by
  simp_rw [iteratedFDeriv_prodMk (hf _) (hq _) (nat_le_infty r),
    iteratedFDeriv_prodMk hf₀ hq₀ (nat_le_infty r)]
  have hp : Continuous (fun p : (E [×r]→L[ℝ] F) × (E [×r]→L[ℝ] G) => p.1.prod p.2) :=
    (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin r => E) F G).continuous
  exact hp.continuousAt.tendsto.comp (h.prodMk_nhds h')

theorem tendsto_value_of_zero_jet
    (h : Tendsto (fun i => iteratedFDeriv ℝ 0 (f i) x) l
      (𝓝 (iteratedFDeriv ℝ 0 f₀ x))) :
    Tendsto (fun i => f i x) l (𝓝 (f₀ x)) := by
  simpa [Function.comp_def] using (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) F
    (fun a => Fin.elim0 a)).continuous.continuousAt.tendsto.comp h

theorem tendsto_jet_directional (v : E) (r : ℕ)
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) x) (hf₀ : ContDiffAt ℝ ∞ f₀ x)
    (h : Tendsto (fun i => iteratedFDeriv ℝ (r + 1) (f i) x) l
      (𝓝 (iteratedFDeriv ℝ (r + 1) f₀ x))) :
    Tendsto (fun i => iteratedFDeriv ℝ r (fun y => fderiv ℝ (f i) y v) x) l
      (𝓝 (iteratedFDeriv ℝ r (fun y => fderiv ℝ f₀ y v) x)) :=
  tendsto_jet_linear_comp (ContinuousLinearMap.apply ℝ F v) r
    (fun i => (hf i).fderiv_right (by simp)) (hf₀.fderiv_right (by simp))
    (tendsto_jet_fderiv r h)

theorem tendsto_two_derivatives_comp (Φ : F → G)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hf₀ : ContDiff ℝ ∞ f₀)
    (hΦ : ∀ i y, ContDiffAt ℝ ∞ Φ (f i y))
    (hΦ₀ : ∀ y, ContDiffAt ℝ ∞ Φ (f₀ y))
    (hzero : Tendsto (fun i => f i x) l (𝓝 (f₀ x)))
    (hone : Tendsto (fun i => fderiv ℝ (f i) x) l (𝓝 (fderiv ℝ f₀ x)))
    (htwo : Tendsto (fun i => fderiv ℝ (fderiv ℝ (f i)) x) l
      (𝓝 (fderiv ℝ (fderiv ℝ f₀) x))) :
    Tendsto (fun i => fderiv ℝ (fun y => Φ (f i y)) x) l
      (𝓝 (fderiv ℝ (fun y => Φ (f₀ y)) x)) ∧
    Tendsto (fun i => fderiv ℝ (fderiv ℝ (fun y => Φ (f i y))) x) l
      (𝓝 (fderiv ℝ (fderiv ℝ (fun y => Φ (f₀ y))) x)) := by
  let K : F × (E →L[ℝ] F) → E →L[ℝ] G :=
    fun p => (fderiv ℝ Φ p.1).comp p.2
  have hK (p : F × (E →L[ℝ] F)) (hp : ContDiffAt ℝ ∞ Φ p.1) :
      ContDiffAt ℝ ∞ K p :=
    ((hp.fderiv_right (by simp)).comp p contDiffAt_fst).clm_comp contDiffAt_snd
  have heq (q : E → F) (hq : ContDiff ℝ ∞ q)
      (hΦq : ∀ y, ContDiffAt ℝ ∞ Φ (q y)) :
      fderiv ℝ (fun y => Φ (q y)) = fun y => K (q y, fderiv ℝ q y) := by
    funext y
    exact fderiv_comp y ((hΦq y).differentiableAt (by simp))
      (hq.differentiable (by simp) y)
  have hpair := hzero.prodMk_nhds hone
  have hkzero := (hK (f₀ x, fderiv ℝ f₀ x) (hΦ₀ x)).continuousAt.tendsto.comp hpair
  refine ⟨?_, ?_⟩
  · simpa only [heq _ (hf _) (hΦ _), heq _ hf₀ hΦ₀, Function.comp_def] using hkzero
  have hpairderiv : Tendsto
      (fun i => (fderiv ℝ (f i) x).prod (fderiv ℝ (fderiv ℝ (f i)) x)) l
      (𝓝 ((fderiv ℝ f₀ x).prod (fderiv ℝ (fderiv ℝ f₀) x))) :=
    (ContinuousLinearMap.prodₗᵢ ℝ).continuous.continuousAt.tendsto.comp
      (hone.prodMk_nhds htwo)
  have hDK : Tendsto (fun i => fderiv ℝ K (f i x, fderiv ℝ (f i) x)) l
      (𝓝 (fderiv ℝ K (f₀ x, fderiv ℝ f₀ x))) :=
    ((hK _ (hΦ₀ x)).fderiv_right (m := ∞) (by simp)).continuousAt.tendsto.comp hpair
  have hsecond (q : E → F) (hq : ContDiff ℝ ∞ q)
      (hΦq : ∀ y, ContDiffAt ℝ ∞ Φ (q y)) :
      fderiv ℝ (fderiv ℝ (fun y => Φ (q y))) x =
        (fderiv ℝ K (q x, fderiv ℝ q x)).comp
          ((fderiv ℝ q x).prod (fderiv ℝ (fderiv ℝ q) x)) := by
    rw [heq q hq hΦq]
    have hd : DifferentiableAt ℝ (fun y => (q y, fderiv ℝ q y)) x :=
      (hq.contDiffAt.differentiableAt (by simp)).prodMk
        ((hq.contDiffAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    have hc := fderiv_comp x ((hK _ (hΦq x)).differentiableAt (by simp)) hd
    simp only [Function.comp_def] at hc
    rw [hc]
    rw [DifferentiableAt.fderiv_prodMk (hq.contDiffAt.differentiableAt (by simp))
      ((hq.contDiffAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))]
  simp_rw [hsecond _ (hf _) (hΦ _), hsecond _ hf₀ hΦ₀]
  exact (continuous_fst.clm_comp continuous_snd).continuousAt.tendsto.comp
    (hDK.prodMk_nhds hpairderiv)

end Calculus

open DeTurckNative

variable {n : ℕ}

theorem contDiff_euclideanMetricState
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    ContDiff ℝ ∞ (euclideanMetricState g b) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hv (i j : Fin n) : ContDiffAt ℝ ∞
      (fun y => g.inner y (b i) (b j)) x :=
    ((g.contDiffAt_euclideanCoefficients x).clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hfirst (a i j : Fin n) : ContDiffAt ℝ ∞
      (fun y => fderiv ℝ (fun z => g.inner z (b i) (b j)) y (b a)) x :=
    ((hv i j).fderiv_right (by simp)).clm_apply contDiffAt_const
  exact (contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => hv i j).prodMk
    ((contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j =>
      hfirst a i j).prodMk (contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun c =>
        contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j =>
          ((hfirst c i j).fderiv_right (by simp)).clm_apply contDiffAt_const))

theorem tendsto_euclideanMetricState_jets
    {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n))
    (hjets : ∀ r : ℕ, r ≤ 4 → ∀ a c : Fin n,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).inner y (b a) (b c)) x) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x)))
    (r : ℕ) (hr : r ≤ 2) :
    Tendsto (fun i => iteratedFDeriv ℝ r (euclideanMetricState (gseq i) b) x) l
      (𝓝 (iteratedFDeriv ℝ r (euclideanMetricState g b) x)) := by
  have hV (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :=
    (contDiff_euclideanMetricState g' b).contDiffAt (x := x)
  have hs (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (a c : Fin n) :
      ContDiffAt ℝ ∞ (fun y => g'.inner y (b a) (b c)) x :=
    ((g'.contDiffAt_euclideanCoefficients x).clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hf (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (d a c : Fin n) :
      ContDiffAt ℝ ∞ (fun y => fderiv ℝ (fun z => g'.inner z (b a) (b c)) y (b d)) x :=
    ((hs g' a c).fderiv_right (by simp)).clm_apply contDiffAt_const
  change Tendsto (fun i => iteratedFDeriv ℝ r
    (fun y => ((euclideanMetricState (gseq i) b y).1,
      (euclideanMetricState (gseq i) b y).2)) x) l
      (𝓝 (iteratedFDeriv ℝ r (fun y =>
        ((euclideanMetricState g b y).1, (euclideanMetricState g b y).2)) x))
  apply tendsto_jet_prod (fun i => (hV (gseq i)).fst) (hV g).fst
    (fun i => (hV (gseq i)).snd) (hV g).snd r
  · apply tendsto_jet_pi (fun i => (hV (gseq i)).fst) (hV g).fst r
    intro a
    apply tendsto_jet_pi
      (fun i => (contDiffAt_pi.mp (hV (gseq i)).fst) a)
      ((contDiffAt_pi.mp (hV g).fst) a) r
    intro c
    exact hjets r (by omega) a c
  · apply tendsto_jet_prod (fun i => (hV (gseq i)).snd.fst) (hV g).snd.fst
      (fun i => (hV (gseq i)).snd.snd) (hV g).snd.snd r
    · apply tendsto_jet_pi (fun i => (hV (gseq i)).snd.fst) (hV g).snd.fst r
      intro d
      apply tendsto_jet_pi
        (fun i => (contDiffAt_pi.mp (hV (gseq i)).snd.fst) d)
        ((contDiffAt_pi.mp (hV g).snd.fst) d) r
      intro a
      apply tendsto_jet_pi
        (fun i => (contDiffAt_pi.mp ((contDiffAt_pi.mp (hV (gseq i)).snd.fst) d)) a)
        ((contDiffAt_pi.mp ((contDiffAt_pi.mp (hV g).snd.fst) d)) a) r
      intro c
      exact tendsto_jet_directional (b d) r (fun i => hs (gseq i) a c) (hs g a c)
        (hjets (r + 1) (by omega) a c)
    · apply tendsto_jet_pi (fun i => (hV (gseq i)).snd.snd) (hV g).snd.snd r
      intro d
      apply tendsto_jet_pi
        (fun i => (contDiffAt_pi.mp (hV (gseq i)).snd.snd) d)
        ((contDiffAt_pi.mp (hV g).snd.snd) d) r
      intro e
      apply tendsto_jet_pi
        (fun i => (contDiffAt_pi.mp ((contDiffAt_pi.mp (hV (gseq i)).snd.snd) d)) e)
        ((contDiffAt_pi.mp ((contDiffAt_pi.mp (hV g).snd.snd) d)) e) r
      intro a
      apply tendsto_jet_pi
        (fun i => (contDiffAt_pi.mp (contDiffAt_pi.mp
          ((contDiffAt_pi.mp (hV (gseq i)).snd.snd) d) e)) a)
        ((contDiffAt_pi.mp (contDiffAt_pi.mp
          ((contDiffAt_pi.mp (hV g).snd.snd) d) e)) a) r
      intro c
      exact tendsto_jet_directional (b d) r (fun i => hf (gseq i) e a c) (hf g e a c)
        (tendsto_jet_directional (b e) (r + 1) (fun i => hs (gseq i) a c) (hs g a c)
          (hjets (r + 1 + 1) (by omega) a c))


theorem tendsto_scalarCurvature_derivatives_of_four_jets
    {α : Type*} {l : Filter α}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ i, LeviCivitaData (gseq i)) (D : LeviCivitaData g)
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n))
    (hjets : ∀ r : ℕ, r ≤ 4 → ∀ a c : Fin n,
      Tendsto (fun i => iteratedFDeriv ℝ r
        (fun y => (gseq i).inner y (b a) (b c)) x) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y (b a) (b c)) x))) :
    Tendsto (fun i => fderiv ℝ (Dseq i).scalarCurvature x) l
      (𝓝 (fderiv ℝ D.scalarCurvature x)) ∧
    Tendsto (fun i => fderiv ℝ (fderiv ℝ (Dseq i).scalarCurvature) x) l
      (𝓝 (fderiv ℝ (fderiv ℝ D.scalarCurvature) x)) := by
  have h := tendsto_euclideanMetricState_jets b x hjets
  have hzero := tendsto_value_of_zero_jet (h 0 (by omega))
  have hone := tendsto_value_of_zero_jet (tendsto_jet_fderiv 0 (h 1 (by omega)))
  have htwo := tendsto_value_of_zero_jet
    (tendsto_jet_fderiv 0 (tendsto_jet_fderiv 1 (h 2 (by omega))))
  have hΦ (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (y : EuclideanSpace ℝ (Fin n)) :
      ContDiffAt ℝ ∞ scalarChartState (euclideanMetricState g' b y) :=
    smoothAt_scalarChartState _ (ne_of_gt (euclideanMetricState_posDef g' b y).det_pos)
  have heq (g' : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D' : LeviCivitaData g') :
      D'.scalarCurvature = fun y => scalarChartState (euclideanMetricState g' b y) :=
    funext (scalarCurvature_eq_scalarChartState D' b)
  simpa only [← heq _ (Dseq _), ← heq _ D] using
    tendsto_two_derivatives_comp scalarChartState
      (fun i => contDiff_euclideanMetricState (gseq i) b) (contDiff_euclideanMetricState g b)
      (fun i => hΦ (gseq i)) (hΦ g) hzero hone htwo

end PoincareConjecture.DeepHorn
