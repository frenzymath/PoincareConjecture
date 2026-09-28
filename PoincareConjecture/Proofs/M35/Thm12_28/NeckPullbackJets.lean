import PoincareConjecture.Proofs.M35.Thm12_28.MetricChartCancellation
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCharts
import PoincareConjecture.Proofs.M35.Mathlib.FiniteJetOperations










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M35

local notation "E3" => EuclideanSpace ℝ (Fin 3)




theorem metric_pullback_cylinder_chart_sum
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 N) (F : M → N) (f : RoundCylinderCoordinates → M) (q : M)
    (p v w : RoundCylinderCoordinates)
    (hp : f p ∈ (extChartAt (𝓡 3) q).source)
    (hF : ContMDiffAt (𝓡 3) (𝓡 3) ∞ F (f p))
    (hf : ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞ f p) :
    g.inner (F (f p)) (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (F ∘ f) p v)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (F ∘ f) p w) =
      ∑ a : Fin 3, ∑ b : Fin 3,
        g.pullbackCoefficients (F ∘ (extChartAt (𝓡 3) q).symm) (extChartAt (𝓡 3) q (f p))
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) *
        (fderiv ℝ (extChartAt (𝓡 3) q ∘ f) p v) a *
        (fderiv ℝ (extChartAt (𝓡 3) q ∘ f) p w) b := by
  have hFd := mfderiv_comp p (hF.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))
  have hFv (z : RoundCylinderCoordinates) :
      mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (F ∘ f) p z =
        mfderiv (𝓡 3) (𝓡 3) F (f p)
          (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) f p z) :=
    congrArg (fun L : RoundCylinderCoordinates →L[ℝ] E3 => L z) hFd
  let c := extChartAt (𝓡 3) q
  have hsource : f p ∈ (chartAt E3 q).source := by
    rwa [← extChartAt_source (I := 𝓡 3)]
  have hc := contMDiffAt_extChartAt' (I := 𝓡 3) (n := ∞) hsource
  have hd := mfderiv_comp p (hc.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  have hmetric := g.pullbackCoefficients_chart_cancel F q hp hF
    (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) f p v)
    (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) f p w)
  let A := g.pullbackCoefficients (F ∘ c.symm) (c (f p))
  let V := fderiv ℝ (c ∘ f) p v
  let W := fderiv ℝ (c ∘ f) p w
  have hv : mfderiv (𝓡 3) (𝓡 3) c (f p)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) f p v) = V :=
    (congrArg (fun L : RoundCylinderCoordinates →L[ℝ] E3 => L v) hd).symm
  have hw : mfderiv (𝓡 3) (𝓡 3) c (f p)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) f p w) = W :=
    (congrArg (fun L : RoundCylinderCoordinates →L[ℝ] E3 => L w) hd).symm
  rw [hv, hw] at hmetric
  refine (congrArg₂ (fun v w : E3 => g.inner (F (f p)) v w) (hFv v) (hFv w)).trans
    (hmetric.symm.trans ?_)
  have he (z : E3) : ∑ a : Fin 3, z a • EuclideanSpace.basisFun (Fin 3) ℝ a = z := by
    simpa only [EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr z
  change A V W = ∑ a : Fin 3, ∑ b : Fin 3,
    A (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) * V a * W b
  calc
    A V W = A (∑ a : Fin 3, V a • EuclideanSpace.basisFun (Fin 3) ℝ a)
      (∑ b : Fin 3, W b • EuclideanSpace.basisFun (Fin 3) ℝ b) := by rw [he, he]
    _ = _ := by
      simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring




theorem roundCylinderPullback_coefficient_eq_chart_sum
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 N) (F : M → N) (coordinate : RoundCylinderSpace → M)
    (q : UnitTwoSphere) (c : M) (p : RoundCylinderCoordinates) (a b : Fin 3)
    (hp : coordinate ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2) ∈
      (extChartAt (𝓡 3) c).source)
    (hF : ContMDiffAt (𝓡 3) (𝓡 3) ∞ F
      (coordinate ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2)))
    (hc : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2)) :
    let H : RoundCylinderCoordinates → E3 := fun y =>
      extChartAt (𝓡 3) c (coordinate ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2))
    roundCylinderTensorCoefficient (roundCylinderPullback g (F ∘ coordinate))
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b =
      ∑ i : Fin 3, ∑ j : Fin 3,
        g.pullbackCoefficients (F ∘ (extChartAt (𝓡 3) c).symm) (H p)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) *
        (fderiv ℝ H p (roundCylinderCoordinateBasis a)) i *
        (fderiv ℝ H p (roundCylinderCoordinateBasis b)) j := by
  let K : RoundCylinderCoordinates → RoundCylinderSpace := fun y =>
    ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2)
  have hKdef : K = cylinderChart q ∘ cylinderCoordinateEquiv.symm := by
    funext y
    simp only [K, cylinderChart, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hK : ContMDiff 𝓘(ℝ, RoundCylinderCoordinates) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ K := by
    rw [hKdef]
    exact (cylinderChart_contMDiff q).comp cylinderCoordinateEquiv.symm.contDiff.contMDiff
  have hKD (v : RoundCylinderCoordinates) :
      mfderiv 𝓘(ℝ, RoundCylinderCoordinates) ((𝓡 2).prod 𝓘(ℝ, ℝ)) K p v =
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1 v.1, v.2) := by
    rw [hKdef, mfderiv_comp p ((cylinderChart_contMDiff q _).mdifferentiableAt (by simp))
      ((cylinderCoordinateEquiv.symm.contDiff (n := ∞)).contDiffAt.contMDiffAt.mdifferentiableAt
        (by simp)),
      mfderiv_eq_fderiv, cylinderCoordinateEquiv.symm.hasFDerivAt.fderiv]
    change mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (cylinderChart q)
      (cylinderCoordinateEquiv.symm p) (cylinderCoordinateEquiv.symm v) = _
    rw [mfderiv_cylinderChart, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  have hcomp := mfderiv_comp p ((hF.comp (K p) hc).mdifferentiableAt (by simp))
    ((hK p).mdifferentiableAt (by simp))
  have hv (v : RoundCylinderCoordinates) :
      mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ((F ∘ coordinate) ∘ K) p v =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (F ∘ coordinate) (K p)
          (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1 v.1, v.2) :=
    (congrArg (fun L : RoundCylinderCoordinates →L[ℝ] E3 => L v) hcomp).trans
      (congrArg (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (F ∘ coordinate) (K p)) (hKD v))
  have hpair := congrArg₂ (fun v w : E3 => g.inner (F (coordinate (K p))) v w)
    (hv (roundCylinderCoordinateBasis a)).symm (hv (roundCylinderCoordinateBasis b)).symm
  exact hpair.trans (metric_pullback_cylinder_chart_sum g F (coordinate ∘ K) c p
    (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b) hp hF (hc.comp p (hK p)))




theorem cylinder_pullback_jet_difference_tendsto_zero
    (f : ℕ → RoundCylinderCoordinates → E3) (f₀ : RoundCylinderCoordinates → E3)
    (p : ℕ → RoundCylinderCoordinates) (p₀ v w : RoundCylinderCoordinates)
    (A : ℕ → E3 → Fin 3 → Fin 3 → ℝ) (r : ℕ)
    (hf₀ : ContDiffAt ℝ ∞ f₀ p₀)
    (hf : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (f k) (p k))
    (hA : ∀ a b : Fin 3, ∀ᶠ k in atTop,
      ContDiffAt ℝ ∞ (fun y => A k y a b) (f k (p k)))
    (hfjet : ∀ m ≤ r + 1, Tendsto (fun k => iteratedFDeriv ℝ m (f k) (p k)) atTop
      (𝓝 (iteratedFDeriv ℝ m f₀ p₀)))
    (hAjet : ∀ m ≤ r, ∀ a b : Fin 3,
      Tendsto (fun k => iteratedFDeriv ℝ m (fun y => A k y a b) (f k (p k))) atTop (𝓝 0)) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun y : RoundCylinderCoordinates =>
      ∑ a : Fin 3, ∑ b : Fin 3,
        A k (f k y) a b * (fderiv ℝ (f k) y v) a * (fderiv ℝ (f k) y w) b) (p k))
      atTop (𝓝 0) := by
  let V (f : RoundCylinderCoordinates → E3) (v : RoundCylinderCoordinates) (a : Fin 3)
      (y : RoundCylinderCoordinates) := (fderiv ℝ f y v) a
  have hV (f : RoundCylinderCoordinates → E3) (y : RoundCylinderCoordinates)
      (hf : ContDiffAt ℝ ∞ f y) (v : RoundCylinderCoordinates) (a : Fin 3) :
      ContDiffAt ℝ ∞ (V f v a) y :=
    (EuclideanSpace.proj a).contDiff.contDiffAt.comp y
      ((hf.fderiv_right (by simp)).clm_apply contDiffAt_const)
  have hVlim (m : ℕ) (hm : m ≤ r) (v : RoundCylinderCoordinates) (a : Fin 3) :
      Tendsto (fun k => iteratedFDeriv ℝ m (V (f k) v a) (p k)) atTop
        (𝓝 (iteratedFDeriv ℝ m (V f₀ v a) p₀)) := by
    apply tendsto_iteratedFDeriv_clm_comp_of_jet m (EuclideanSpace.proj a)
      ((hf₀.fderiv_right (by simp)).clm_apply contDiffAt_const)
      (hf.mono fun k hk => (hk.fderiv_right (by simp)).clm_apply contDiffAt_const)
    exact tendsto_iteratedFDeriv_fderiv_apply_of_jet m v hf₀ hf (hfjet (m + 1) (by omega))
  let H (k : ℕ) (a b : Fin 3) (y : RoundCylinderCoordinates) :=
    A k (f k y) a b * V (f k) v a y * V (f k) w b y
  have hH (a b : Fin 3) : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ (H k a b) (p k) := by
    filter_upwards [hf, hA a b] with k hfk hAk
    exact ((hAk.comp (p k) hfk).mul (hV (f k) (p k) hfk v a)).mul
      (hV (f k) (p k) hfk w b)
  have hlim (a b : Fin 3) :
      Tendsto (fun k => iteratedFDeriv ℝ r (H k a b) (p k)) atTop (𝓝 0) := by
    have hcomp (m : ℕ) (hm : m ≤ r) :
        Tendsto (fun k => iteratedFDeriv ℝ m (fun y => A k (f k y) a b) (p k))
          atTop (𝓝 0) := by
      have h := tendsto_iteratedFDeriv_comp_of_jets m hf₀
        (contDiffAt_const (c := (0 : ℝ))) hf (hA a b)
        (fun n hn => hfjet n (by omega))
        (fun n hn => by
          simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hAjet n (by omega) a b)
      simpa only [Function.comp_def, iteratedFDeriv_fun_zero, Pi.zero_apply] using h
    have hfirst (m : ℕ) (hm : m ≤ r) :
        Tendsto (fun k => iteratedFDeriv ℝ m
          (fun y => A k (f k y) a b * V (f k) v a y) (p k)) atTop (𝓝 0) := by
      have h := tendsto_iteratedFDeriv_mul_of_jets
        (f₀ := fun _ => (0 : ℝ)) (g₀ := V f₀ v a) m contDiffAt_const (hV f₀ p₀ hf₀ v a)
        ((hf.and (hA a b)).mono fun k hk => hk.2.comp (p k) hk.1)
        (hf.mono fun k hk => hV (f k) (p k) hk v a)
        (fun n hn => by
          simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, Function.comp_def] using
            hcomp n (hn.trans hm))
        (fun n hn => hVlim n (hn.trans hm) v a)
      simpa only [zero_mul, iteratedFDeriv_fun_zero, Pi.zero_apply, Function.comp_def] using h
    have h := tendsto_iteratedFDeriv_mul_of_jets
      (f₀ := fun _ => (0 : ℝ)) (g₀ := V f₀ w b) r contDiffAt_const (hV f₀ p₀ hf₀ w b)
      ((hf.and (hA a b)).mono fun k hk =>
        (hk.2.comp (p k) hk.1).mul (hV (f k) (p k) hk.1 v a))
      (hf.mono fun k hk => hV (f k) (p k) hk w b)
      (fun m hm => by
        simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, Function.comp_def] using hfirst m hm)
      (fun m hm => hVlim m hm w b)
    simpa only [H, zero_mul, iteratedFDeriv_fun_zero, Pi.zero_apply, Function.comp_def] using h
  have hsum := tendsto_finsetSum Finset.univ (fun a _ =>
    tendsto_finsetSum Finset.univ (fun b _ => hlim a b))
  simp only [Finset.sum_const_zero] at hsum
  apply hsum.congr'
  have hAll : ∀ᶠ k in atTop, ∀ a b : Fin 3, ContDiffAt ℝ ∞ (H k a b) (p k) :=
    eventually_all.mpr (fun a => eventually_all.mpr (fun b => hH a b))
  filter_upwards [hAll] with k hk
  symm
  change iteratedFDeriv ℝ r (fun y => ∑ a : Fin 3, ∑ b : Fin 3, H k a b y) (p k) = _
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
  rw [iteratedFDeriv_fun_sum_apply (fun a _ =>
    (ContDiffAt.sum (fun b _ => hk a b)).of_le hr)]
  exact Finset.sum_congr rfl (fun a _ =>
    iteratedFDeriv_fun_sum_apply (fun b _ => (hk a b).of_le hr))

end PoincareConjecture.M35
