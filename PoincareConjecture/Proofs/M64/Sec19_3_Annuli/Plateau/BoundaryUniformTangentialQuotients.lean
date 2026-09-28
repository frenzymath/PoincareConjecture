import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMixedSmallPotential
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMetricComponentDifference
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMixedAbsorption

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64UniformTangential_bilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64UniformTangential_bilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64UniformTangential_trilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64UniformTangential_trilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 1600000 in

theorem m64WeightedMixedMetric_uniform_tangential_quotients
    (dirichlet : Fin n → Prop) {a : LoopPlane} {R : ℝ} (hR : 0 < R)
    (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (w : Fin 2 → ℝ) (V : Fin 2 → LoopPlane → E) (u : LoopPlane → E)
    {kappa mu C Lambda : ℝ} (hk : 0 < kappa) (hmu : 0 < mu) (hC : 0 < C)
    (hw : ∀ i, mu ≤ w i ∧ w i ≤ Lambda)
    (hG : ∀ p ∈ ball a R ∩ {p : LoopPlane | 0 < p 1},
      ‖G (u p)‖ ≤ C ∧ ‖T (u p)‖ ≤ C ∧ ∀ v : E, kappa * ‖v‖ ^ 2 ≤ G (u p) v v)
    (hLip : ∀ p ∈ ball a R ∩ {p : LoopPlane | 0 < p 1},
      ∀ q ∈ ball a R ∩ {p : LoopPlane | 0 < p 1},
      ‖G (u p) - G (u q)‖ ≤ C * ‖u p - u q‖ ∧
      ‖T (u p) - T (u q)‖ ≤ C * ‖u p - u q‖)
    (hu : Continuous u) (huc : HasCompactSupport u) (hu0 : u a = 0)
    (hz : ∀ j, dirichlet j → ∀ p : LoopPlane, p 1 < 0 → u p j = 0)
    (hV : ∀ i, MemLp (V i) 2 volume)
    (hweak : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) univ)
    (hflux : ∀ j : Fin n, ∀ i : Fin 2,
      MemLp (fun p => w i * G (u p) (V i p) (EuclideanSpace.single j 1))
        2 (volume.restrict (ball a R ∩ {p : LoopPlane | 0 < p 1})))
    (hsource : ∀ j : Fin n, IntegrableOn (fun p =>
      -(∑ i : Fin 2, w i * T (u p) (EuclideanSpace.single j 1) (V i p) (V i p)) / 2)
      (ball a R ∩ {p : LoopPlane | 0 < p 1}))
    (heq : ∀ j : Fin n, ∀ phi : LoopPlane → ℝ,
      ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ ball a R →
      (dirichlet j → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) →
      (∫ p, ∑ i : Fin 2, (ball a R ∩ {p : LoopPlane | 0 < p 1}).indicator
        (fun q => w i * G (u q) (V i q) (EuclideanSpace.single j 1)) p *
          fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p, (ball a R ∩ {p : LoopPlane | 0 < p 1}).indicator
          (fun q => -(∑ i : Fin 2,
            w i * T (u q) (EuclideanSpace.single j 1) (V i q) (V i q)) / 2) p * phi p) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∃ h0 : ℝ, 0 < h0 ∧ ∃ D : ℝ,
      ∀ j : Fin n, ∀ h : ℝ, h ≠ 0 → |h| ≤ h0 →
        (∫ p in ball a r ∩ {p : LoopPlane | 0 < p 1},
          ∑ i : Fin 2, diffQuot 0 h (fun q => V i q j) p ^ 2) ≤ D := by
  classical
  let nu := kappa * mu / 4
  let B := 32 * (2 * Lambda * C) ^ 2 / (kappa * mu) + 6 * (2 * Lambda * C)
  have hLambda : 0 < Lambda := hmu.trans_le ((hw 0).1.trans (hw 0).2)
  have hnu : 0 < nu := by dsimp [nu]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  let eta := nu / (8 * B)
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hsmall : 2 * B * (2 * eta) ≤ nu / 2 := by
    dsimp only [eta]
    field_simp
    ring_nf
    norm_num
  obtain ⟨rho, hrho, hrhoR, hpot⟩ := m64WeightedMixedMetric_small_potential
    dirichlet hR (G ∘ u) (T ∘ u) w V u hk hmu hC.le hw hG hu hu0 hz hV hweak
    hflux hsource heq heta
  let Hplane := {p : LoopPlane | 0 < p 1}
  have hHm : MeasurableSet Hplane :=
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous).measurableSet
  let S := ball a rho ∩ Hplane
  have hSm : MeasurableSet S := measurableSet_ball.inter hHm
  have hsub : S ⊆ ball a R ∩ Hplane := inter_subset_inter_left _ (ball_subset_ball hrhoR.le)
  let O := ball a (rho / 2)
  let H := S.indicator (fun p => ∑ i : Fin 2, ‖V i p‖ ^ 2)
  let W := S.indicator (fun _ : LoopPlane => (1 : ℝ))
  let Wp := Hplane.indicator (fun _ : LoopPlane => (1 : ℝ))
  let F := fun (j : Fin n) (i : Fin 2) =>
    S.indicator (fun p => w i * G (u p) (V i p) (EuclideanSpace.single j 1))
  let b := fun j : Fin n => S.indicator (fun p =>
    -(∑ i : Fin 2, w i * T (u p) (EuclideanSpace.single j 1) (V i p) (V i p)) / 2)
  have hFI (j : Fin n) (i : Fin 2) : MemLp (F j i) 2 volume :=
    (memLp_indicator_iff_restrict hSm).mpr
      ((hflux j i).mono_measure (Measure.restrict_mono hsub le_rfl))
  have hbI (j : Fin n) : Integrable (b j) :=
    (integrable_indicator_iff hSm).mpr ((hsource j).mono_set hsub)
  have hHI : Integrable H := (integrable_indicator_iff hSm).mpr
    ((integrable_finsetSum _ (fun i _ => (hV i).norm.integrable_sq)).integrableOn)
  have hWI : Integrable W := memLp_one_iff_integrable.mp
    (memLp_indicator_const 1 hSm 1 (Or.inr
      ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne))
  have hWp : MemLp Wp ⊤ volume := (memLp_top_const (1 : ℝ)).indicator hHm
  have hW0 (p : LoopPlane) : 0 ≤ Wp p := indicator_nonneg (fun _ _ => zero_le_one) p
  have hH0 (p : LoopPlane) : 0 ≤ H p :=
    indicator_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) p
  have hp0 (phi : LoopPlane → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
      (hs : tsupport phi ⊆ ball a rho) :
      (∫ p, H p * phi p ^ 2) ≤ eta *
        ∫ p, W p * ∑ i : Fin 2, (fderiv ℝ phi p (EuclideanSpace.single i 1)) ^ 2 := by
    have hleft : (fun p => H p * phi p ^ 2) =
        S.indicator (fun p => (∑ i : Fin 2, ‖V i p‖ ^ 2) * phi p ^ 2) := by
      funext p
      by_cases hp : p ∈ S <;> simp [H, hp]
    have hright : (fun p => W p * ∑ i : Fin 2,
        (fderiv ℝ phi p (EuclideanSpace.single i 1)) ^ 2) =
        S.indicator (fun p => ∑ i : Fin 2,
          (fderiv ℝ phi p (EuclideanSpace.single i 1)) ^ 2) := by
      funext p
      by_cases hp : p ∈ S <;> simp [W, hp]
    rw [hleft, hright, integral_indicator hSm, integral_indicator hSm]
    exact hpot phi hp hc hs
  obtain ⟨xi, hxi, hxic, hxi01, hxi1, hxis⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      (isCompact_closedBall a (rho / 8)) isOpen_ball
      (closedBall_subset_ball (by linarith : rho / 8 < rho / 4))
  have hucj (j : Fin n) : HasCompactSupport (fun p => u p j) :=
    huc.comp_left (g := fun v : E => v j) (by simp)
  have huj (j : Fin n) : Continuous (fun p => u p j) :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hu
  obtain ⟨D, hD⟩ := M60.suNaturalGrowth_cutoff_remainder_bounded
    (p := 2) (r := ⊤) (t := 1) (u := fun j p => u p j) (du := fun j i p => V i p j)
    (by norm_num) (by norm_num) (show 0 ≤ 2 * eta by positivity)
    huj hucj (fun j i => (hV i).eval_piLp j) (fun j i => hweak i j)
    hxi hxic (fun p => abs_le.mpr ⟨by linarith [(hxi01 ⟨p, rfl⟩).1],
      (hxi01 ⟨p, rfl⟩).2⟩) hHI hH0
    ((memLp_top_const (1 / 2 : ℝ)).indicator hHm)
  refine ⟨rho / 8, by positivity, by linarith, rho / 8, by positivity, (2 * B / nu) * D, ?_⟩
  intro j h hh hhh
  let v : LoopPlane := h • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  have hv : ‖v‖ = |h| := by simp [v, norm_smul]
  have hpv (p : LoopPlane) : (p + v) 1 = p 1 := by simp [v, PiLp.add_apply, PiLp.smul_apply]
  have hxy (p : LoopPlane) (hp : p ∈ O) :
      p ∈ ball a rho ∧ p + v ∈ ball a rho := by
    have ht := dist_triangle (p + v) p a
    have he : dist (p + v) p = ‖v‖ := by simp [dist_eq_norm]
    rw [he, hv] at ht
    exact ⟨ball_subset_ball (by linarith) hp,
      show dist (p + v) a < rho by change dist p a < rho / 2 at hp; linarith⟩
  let Hh := fun p => H p + H (p + v)
  have hHh : Integrable Hh := hHI.add
    ((measurePreserving_add_right volume v).integrable_comp_of_integrable hHI)
  have hpotential (phi : LoopPlane → ℝ) (hp : ContDiff ℝ ∞ phi)
      (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ O) :
      (∫ p, Hh p * phi p ^ 2) ≤ (2 * eta) *
        ∫ p, Wp p * ∑ i : Fin 2, (fderiv ℝ phi p (EuclideanSpace.single i 1)) ^ 2 := by
    have ht := M60.suNaturalGrowth_translated_potential hHI hWI hp0
      (a := v) (by rw [hv]; linarith : rho / 2 + ‖v‖ ≤ rho) hp hc hs
    have he (p : LoopPlane) : (W p + W (p + v)) *
        (∑ i : Fin 2, (fderiv ℝ phi p (EuclideanSpace.single i 1)) ^ 2) =
        2 * (Wp p * ∑ i : Fin 2, (fderiv ℝ phi p (EuclideanSpace.single i 1)) ^ 2) := by
      by_cases hpO : p ∈ O
      · have hb := hxy p hpO
        by_cases hpH : p ∈ Hplane
        · have hpS : p ∈ S := ⟨hb.1, hpH⟩
          have hqS : p + v ∈ S := ⟨hb.2, by simpa only [Hplane, mem_ofPred_eq, hpv] using hpH⟩
          norm_num [W, Wp, hpS, hqS, hpH]
        · have hpS : p ∉ S := fun hh => hpH hh.2
          have hqS : p + v ∉ S := fun hh => hpH (by
            simpa only [Hplane, mem_ofPred_eq, hpv] using hh.2)
          simp [W, Wp, hpS, hqS, hpH]
      · have hd (i : Fin 2) : fderiv ℝ phi p (EuclideanSpace.single i 1) = 0 := by
          rw [fderiv_of_notMem_tsupport ℝ (fun hh => hpO (hs hh))]
          rfl
        simp only [hd, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero]
    simp_rw [he] at ht
    rw [integral_const_mul] at ht
    exact ht.trans_eq (by ring)
  have hsupp : cthickening |h| (tsupport xi) ⊆ O := by
    apply (cthickening_subset_of_subset |h| hxis).trans
    rw [cthickening_ball (abs_nonneg h) (by positivity : 0 < rho / 4)]
    exact closedBall_subset_ball (by linarith)
  have hxiO : tsupport xi ⊆ O := hxis.trans (ball_subset_ball (by linarith))
  have heqS (j : Fin n) (phi : LoopPlane → ℝ) (hp : ContDiff ℝ ∞ phi)
      (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ O)
      (hz : dirichlet j → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) :
      (∫ p, ∑ i : Fin 2, F j i p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p, b j p * phi p := by
    have he := m64MixedBoundary_indicator_restrict (ball_subset_ball hrhoR.le)
      (heq j) hp hc (hs.trans (ball_subset_ball (by linarith : rho / 2 ≤ rho))) hz
    have hs' : ball a rho ∩ (ball a R ∩ Hplane) = S := by
      ext p
      constructor
      · intro hp
        exact ⟨hp.1, hp.2.2⟩
      · intro hp
        exact ⟨hp.1, ball_subset_ball hrhoR.le hp.1, hp.2⟩
    dsimp only [Hplane] at hs'
    rw [hs'] at he
    exact he
  have hpoint (p : LoopPlane) :
      nu * (Wp p * ∑ j : Fin n, ∑ i : Fin 2,
        (xi p * diffQuot 0 h (fun q => V i q j) p) ^ 2) ≤
      (∑ j : Fin n, ∑ i : Fin 2, diffQuot 0 h (F j i) p *
        (xi p ^ 2 * diffQuot 0 h (fun q => V i q j) p + 2 * xi p *
          fderiv ℝ xi p (EuclideanSpace.single i 1) * diffQuot 0 h (fun q => u q j) p)) -
      (∑ j : Fin n, diffQuot 0 h (b j) p * (xi p ^ 2 * diffQuot 0 h (fun q => u q j) p)) +
      B * ((Hh p * xi p ^ 2 + ∑ j : Fin n,
        Hh p * (xi p * diffQuot 0 h (fun q => u q j) p) ^ 2) + Wp p *
          ∑ j : Fin n, ∑ i : Fin 2,
            (fderiv ℝ xi p (EuclideanSpace.single i 1) * diffQuot 0 h (fun q => u q j) p) ^ 2) := by
    by_cases hp : p ∈ tsupport xi
    · have hxy' := hxy p (hxiO hp)
      by_cases hpH : p ∈ Hplane
      · have hpS : p ∈ S := ⟨hxy'.1, hpH⟩
        have hqS : p + v ∈ S := ⟨hxy'.2, by simpa only [Hplane, mem_ofPred_eq, hpv] using hpH⟩
        change p + h • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ∈ S at hqS
        have hqR := hsub hqS
        have hpR := hsub hpS
        have hact := m64WeightedMetric_component_difference G T w u V
          (fun i => fderiv ℝ xi p (EuclideanSpace.single i 1)) p
          (xi := xi p) hk hmu hC.le hw hh (hG _ hqR).1 (hG _ hqR).2.1
          (hG _ hqR).2.2 (hLip _ hqR _ hpR).1 (hLip _ hqR _ hpR).2
        have hmax (z : LoopPlane) : ‖(V 0 z, V 1 z)‖ ^ 2 ≤ ∑ i : Fin 2, ‖V i z‖ ^ 2 := by
          rw [Fin.sum_univ_two, Prod.norm_def]
          rcases le_total ‖V 0 z‖ ‖V 1 z‖ with hl | hl
          · rw [max_eq_right hl]
            nlinarith [sq_nonneg ‖V 0 z‖]
          · rw [max_eq_left hl]
            nlinarith [sq_nonneg ‖V 1 z‖]
        have henergy : ‖(V 0 (p + v), V 1 (p + v))‖ ^ 2 + ‖(V 0 p, V 1 p)‖ ^ 2 ≤ Hh p := by
          simp only [Hh, H, v, indicator_of_mem hpS, indicator_of_mem hqS]
          linarith [hmax p, hmax (p + v)]
        have hFq (j : Fin n) (i : Fin 2) : diffQuot 0 h (F j i) p =
            diffQuot 0 h (fun q => w i * G (u q) (V i q) (EuclideanSpace.single j 1)) p := by
          simp only [diffQuot_apply_of_ne 0 hh, F, indicator_of_mem hpS, indicator_of_mem hqS]
        have hbq (j : Fin n) : diffQuot 0 h (b j) p = diffQuot 0 h
            (fun q => -(∑ i : Fin 2,
              w i * T (u q) (EuclideanSpace.single j 1) (V i q) (V i q)) / 2) p := by
          simp only [diffQuot_apply_of_ne 0 hh, b, indicator_of_mem hpS, indicator_of_mem hqS]
        simp only [Wp, indicator_of_mem hpH, one_mul, hFq, hbq]
        apply hact.trans
        gcongr
      · have hpS : p ∉ S := fun hh => hpH hh.2
        have hqS : p + v ∉ S := fun hh => hpH (by
          simpa only [Hplane, mem_ofPred_eq, hpv] using hh.2)
        change p + h • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ∉ S at hqS
        simp only [Wp, indicator_of_notMem hpH, F, b, Hh, H, v,
          diffQuot_apply_of_ne 0 hh, indicator_of_notMem hpS, indicator_of_notMem hqS,
          zero_mul, mul_zero, sub_self, zero_div, Finset.sum_const_zero, add_zero, le_refl]
    · have hzero := image_eq_zero_of_notMem_tsupport hp
      have hd : fderiv ℝ xi p = 0 := fderiv_of_notMem_tsupport ℝ hp
      simp only [hzero, hd, zero_apply, zero_mul, mul_zero,
        zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, sub_zero, add_zero, le_refl]
  have hbound := m64NaturalGrowth_mixed_diffQuot_absorb dirichlet isOpen_ball hnu hB.le
    (show 0 ≤ 2 * eta by positivity) hsmall hHh hWp hW0 hFI hbI huj
    (fun j i => (hV i).eval_piLp j) (fun j i => hweak i j) hz hxi hxic hxiO heqS
    hpotential hh hsupp hpoint
  have hrem := hD 0 h
  have hweight (p : LoopPlane) : Hplane.indicator (fun _ : LoopPlane => (1 / 2 : ℝ)) p +
      Hplane.indicator (fun _ : LoopPlane => (1 / 2 : ℝ)) (p + v) = Wp p := by
    by_cases hp : p ∈ Hplane
    · have hq : p + v ∈ Hplane := by simpa only [Hplane, mem_ofPred_eq, hpv] using hp
      norm_num [Wp, hp, hq]
    · have hq : p + v ∉ Hplane := fun hh => hp (by simpa only [Hplane, mem_ofPred_eq, hpv] using hh)
      simp [Wp, hp, hq]
  dsimp only [v] at hweight
  simp only [Poincare.Analysis.Sobolev.translate, hweight] at hrem
  have htotal := hbound.trans (mul_le_mul_of_nonneg_left hrem (by positivity))
  have hsingle (j : Fin n) (i : Fin 2) : Integrable
      (fun p => Wp p * (xi p * diffQuot 0 h (fun q => V i q j) p) ^ 2) := by
    have hp : MemLp (fun p => xi p * diffQuot 0 h (fun q => V i q j) p) 2 volume :=
      (M60.suWeakMap_diffQuot_memLp ((hV i).eval_piLp j) 0 h).mul'
        (hxi.continuous.memLp_of_hasCompactSupport hxic : MemLp xi ⊤ volume)
    have hsquare : MemLp (fun p => (xi p * diffQuot 0 h (fun q => V i q j) p) ^ 2) 1 volume :=
      by simpa only [pow_two] using hp.mul' hp
    exact memLp_one_iff_integrable.mp (hsquare.mul' hWp)
  have hI : Integrable (fun p => Wp p * ∑ j : Fin n, ∑ i : Fin 2,
      (xi p * diffQuot 0 h (fun q => V i q j) p) ^ 2) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => hsingle j i
  have hIj : Integrable (fun p => Wp p * ∑ i : Fin 2,
      (xi p * diffQuot 0 h (fun q => V i q j) p) ^ 2) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun i _ => hsingle j i
  have hinner : MeasurableSet (ball a (rho / 8) ∩ Hplane) := measurableSet_ball.inter hHm
  calc
    _ = ∫ p in ball a (rho / 8) ∩ Hplane, Wp p * ∑ i : Fin 2,
        (xi p * diffQuot 0 h (fun q => V i q j) p) ^ 2 := by
      apply setIntegral_congr_fun hinner
      intro p hp
      simp only [Wp, indicator_of_mem hp.2, hxi1 p (ball_subset_closedBall hp.1), one_mul]
    _ ≤ ∫ p in ball a (rho / 8) ∩ Hplane, Wp p * ∑ j : Fin n, ∑ i : Fin 2,
        (xi p * diffQuot 0 h (fun q => V i q j) p) ^ 2 := by
      apply setIntegral_mono_on hIj.integrableOn hI.integrableOn hinner
      intro p _
      apply mul_le_mul_of_nonneg_left _ (hW0 p)
      exact Finset.single_le_sum (f := fun k : Fin n => ∑ i : Fin 2,
        (xi p * diffQuot 0 h (fun q => V i q k) p) ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∫ p, Wp p * ∑ j : Fin n, ∑ i : Fin 2,
        (xi p * diffQuot 0 h (fun q => V i q j) p) ^ 2 :=
      setIntegral_le_integral hI (Eventually.of_forall fun p =>
        mul_nonneg (hW0 p) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))
    _ ≤ _ := htotal

end PoincareConjecture
