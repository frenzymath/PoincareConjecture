import PoincareConjecture.Proofs.M35.Thm12_28.CurvatureMetricJets









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M35

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 3)

local instance radialLimitDualNormedGroup : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
local instance radialLimitDualNormedSpace : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
local instance radialLimitMetricNormedGroup : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
  inferInstance
local instance radialLimitMetricNormedSpace : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance



theorem parallel_unit_of_metric_and_field_jets
    {gseq : ℕ → RiemannianMetric 3 V} {g : RiemannianMetric 3 V}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    {Zseq : ℕ → V → V} {Z : V → V} (pseq : ℕ → V) (p : V)
    (hZ : ContDiffAt ℝ ∞ Z p) (hZseq : ∀ k, ContDiffAt ℝ ∞ (Zseq k) (pseq k))
    (hmetric : ∀ m ≤ 1, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p)))
    (hfield : ∀ m ≤ 1, Tendsto (fun k => iteratedFDeriv ℝ m (Zseq k) (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m Z p)))
    (hunit : ∀ᶠ k in atTop, (gseq k).inner (pseq k)
      (Zseq k (pseq k)) (Zseq k (pseq k)) = 1)
    (hparallel : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ w : V,
      (gseq k).inner (pseq k) ((Dseq k).connection (Zseq k) (pseq k) w)
        ((Dseq k).connection (Zseq k) (pseq k) w) ≤
          ε ^ 2 * (gseq k).inner (pseq k) w w) :
    g.inner p (Z p) (Z p) = 1 ∧ ∀ w : V, D.connection Z p w = 0 := by
  have hB : Tendsto (fun k => (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (g.euclideanCoefficients p)) := by
    have h := ((continuousMultilinearCurryFin0 ℝ V (V →L[ℝ] V →L[ℝ] ℝ)).continuous.tendsto _).comp
      (hmetric 0 (by omega))
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  have hV : Tendsto (fun k => Zseq k (pseq k)) atTop (𝓝 (Z p)) := by
    have h := ((continuousMultilinearCurryFin0 ℝ V V).continuous.tendsto _).comp
      (hfield 0 (by omega))
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  have hDV : Tendsto (fun k => fderiv ℝ (Zseq k) (pseq k)) atTop
      (𝓝 (fderiv ℝ Z p)) := by
    let C := continuousMultilinearCurryFin1 ℝ V V
    have heq (f : V → V) (x : V) : C (iteratedFDeriv ℝ 1 f x) = fderiv ℝ f x := by
      ext v
      simp [C, continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    have h := (C.continuous.tendsto _).comp (hfield 1 le_rfl)
    simpa only [Function.comp_def, heq] using h
  have hev₁ : Continuous (fun z : (V →L[ℝ] V →L[ℝ] ℝ) × V => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have hev₂ : Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have hlength := (hev₂.tendsto _).comp
    (((hev₁.tendsto _).comp (hB.prodMk_nhds hV)).prodMk_nhds hV)
  have hunit' : (fun k => (gseq k).euclideanCoefficients (pseq k)
      (Zseq k (pseq k)) (Zseq k (pseq k))) =ᶠ[atTop] (fun _ => (1 : ℝ)) := hunit
  refine ⟨tendsto_nhds_unique hlength (tendsto_const_nhds.congr' hunit'.symm), ?_⟩
  intro w
  have hGamma : Tendsto
      (fun k => (Dseq k).euclideanConnection w (Zseq k (pseq k)) (pseq k)) atTop
      (𝓝 (D.euclideanConnection w (Z p) p)) := by
    have hj := euclideanConnection_field_jets_tendsto Dseq D pseq p w 0 hZ hZseq
      (fun m hm => hmetric m (by omega)) (fun m hm => hfield m (by omega))
    have h := ((continuousMultilinearCurryFin0 ℝ V V).continuous.tendsto _).comp hj
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  have hconn : Tendsto (fun k => (Dseq k).connection (Zseq k) (pseq k) w) atTop
      (𝓝 (D.connection Z p w)) := by
    have heq k := (Dseq k).connection_eq_fderiv_add
      ((hZseq k).differentiableAt (by simp)) w
    have he := D.connection_eq_fderiv_add (hZ.differentiableAt (by simp)) w
    have hev : Continuous (fun z : (V →L[ℝ] V) × V => z.1 z.2) :=
      continuous_fst.clm_apply continuous_snd
    have hd := (hev.tendsto _).comp (hDV.prodMk_nhds (tendsto_const_nhds (x := w)))
    simpa only [heq, he] using! hd.add hGamma
  have hnorm := (hev₂.tendsto _).comp
    (((hev₁.tendsto _).comp (hB.prodMk_nhds hconn)).prodMk_nhds hconn)
  have hnormw := (hev₂.tendsto _).comp
    (((hev₁.tendsto _).comp (hB.prodMk_nhds (tendsto_const_nhds (x := w)))).prodMk_nhds
      (tendsto_const_nhds (x := w)))
  have hle (ε : ℝ) (hε : 0 < ε) :
      g.inner p (D.connection Z p w) (D.connection Z p w) ≤ ε ^ 2 * g.inner p w w :=
    le_of_tendsto_of_tendsto hnorm (tendsto_const_nhds.mul hnormw)
      ((hparallel ε hε).mono fun k hk => hk w)
  have hz : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 2 * g.inner p w w)
      atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.pow 2).mul
      (tendsto_const_nhds (x := g.inner p w w))
  have hnonpos : g.inner p (D.connection Z p w) (D.connection Z p w) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hz
      (Eventually.of_forall fun n => hle _ (by positivity))
  by_contra hne
  exact (not_le_of_gt (g.pos p (D.connection Z p w) hne)) hnonpos

end

end PoincareConjecture.M35
