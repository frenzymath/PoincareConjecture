import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.RegularDomain
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.TiltedDirectionalSlab
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.TiltedBuffer
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Slab.Parameters
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Slab.AnnularSummation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometrySectional
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Normalized
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Slab.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Slab.Shift
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Slab.GeometricBound

open Set Function TopologicalSpace MeasureTheory PoincareConjecture
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology BigOperators
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
theorem PoincareConjecture.RiemannianMetric.exists_uniform_openFiber_annular_scalar_bound
    (m k : ℕ) (hm : 1 ≤ m) {Δ : ℝ}
    (hΔ : 0 < Δ) (hΔsmall : Δ ≤ 1 / (16 * ((k : ℝ) + 1)))
    (hΔstrong : Δ ≤ 1 / (256 * ((k : ℝ) + 2)^2))
    (hind : ∀ H η : ℝ, 0 ≤ H → 0 < η → ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin ((m + 2) + k))) M]
        [IsManifold (𝓡 ((m + 2) + k)) ∞ M],
        PoincareConjecture.NormalizedCornerScalarBound ((m + 2) + k) (m + 1) (k + 1)
          (by omega) M Δ H η C₀) :
    let ε := Δ / (8 * ((k : ℝ) + 1))
    let σ := ε^2 / 2048
    let v := 1 - σ^2 / 8
    0 < v ∧ v < 1 ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ C : ℝ, 0 ≤ C →
      ∃ r₀ B : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 2 ∧ 0 < B ∧
        ∀ (M : Type u) [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
          [MeasurableSpace M] [BorelSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin ((m + 2) + k))) M]
          [IsManifold (𝓡 ((m + 2) + k)) ∞ M]
          (g : RiemannianMetric ((m + 2) + k) M) (D : LeviCivitaData g),
          MetricComplete g →
          (∀ x (z w : TangentSpace (𝓡 ((m + 2) + k)) x),
            -1 ≤ D.sectionalCurvature x z w) →
          ∀ (f h : Fin k → M → ℝ)
            (hf : ∀ i, ContMDiff (𝓡 ((m + 2) + k)) 𝓘(ℝ,ℝ) ∞ (f i))
            (hh : ∀ i, ContMDiff (𝓡 ((m + 2) + k)) 𝓘(ℝ,ℝ) ∞ (h i))
            (U : Opens M) (δ : ℝ), 0 ≤ δ → δ ≤ δ₀ →
            (∀ x ∈ U, ∀ i,
              g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
              g.tangentNorm x (D.gradient (h i) x) ≤ 1 ∧
              g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2*δ) →
            (∀ x ∈ U, ∀ i j, i ≠ j →
              |g.inner x (D.gradient (f i) x) (D.gradient (f j) x)| ≤ δ ∧
              |g.inner x (D.gradient (f i) x) (D.gradient (h j) x)| ≤ δ ∧
              |g.inner x (D.gradient (h i) x) (D.gradient (f j) x)| ≤ δ ∧
              |g.inner x (D.gradient (h i) x) (D.gradient (h j) x)| ≤ δ) →
            (∀ x ∈ U, ∀ i j, i ≠ j →
              g.inner x (D.gradient (f i) x) (D.gradient (f j) x) ≤ 0) →
            (∀ x ∈ U, ∀ i z,
              D.hessian (f i) x z z ≤ C*g.inner x z z ∧
              D.hessian (h i) x z z ≤ C*g.inner x z z) →
            let P := fun x i => f i x
            let hP : ContMDiff (𝓡 ((m + 2) + k)) 𝓘(ℝ,Fin k → ℝ) ∞ P :=
              contMDiff_pi_space.mpr hf
            ∀ (hreg : ∀ x ∈ U, Surjective
                (mfderiv (𝓡 ((m + 2) + k)) 𝓘(ℝ,Fin k → ℝ) P x))
              (c : Fin k → ℝ),
              letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m+2)+k))) =
                  (m+2)+k) := ⟨finrank_euclideanSpace_fin⟩
              letI := openFiberChartedSpace (m := m+2) hP U hreg c
              letI := isManifold_openFiber (m := m+2) hP U hreg c
              let L := openFiber P U c
              let incl := openFiberIncl P U c
              let gL := g.openRegularFiberMetric hP U hreg c
              ∀ (p : L) (K : L → ℝ), Continuous K → (∀ x, 0 ≤ K x) →
                (∀ x (z w : TangentSpace (𝓡 (m+2)) x),
                  -K x ≤ gL.leviCivitaData.sectionalCurvature x z w) →
                ∀ r : ℝ, 0 < r → r ≤ r₀ →
                  (∀ y, g.edist (incl p) y ≤ ENNReal.ofReal (4*r) → y ∈ U) →
                  (∀ y : M, r/2 < (g.edist (incl p) y).toReal →
                    (g.edist (incl p) y).toReal < 3*r →
                    ∀ a : ℝ, 0 < a → ∃ z : M, (g.edist y z).toReal < a ∧
                      v*(g.edist y z).toReal <
                        (g.edist (incl p) z).toReal - (g.edist (incl p) y).toReal) →
                  (∫ x in {x : L | (g.edist (incl p) (incl x)).toReal ∈
                      Icc (113*r/96) (19*r/16)},
                    max 0 (gL.leviCivitaData.scalarCurvature x) ∂gL.volumeMeasure) ≤
                    B*(r^m + ∫ x in {x : L | (g.edist (incl p) (incl x)).toReal ∈
                      Icc (r/2) (3*r)}, K x ∂gL.volumeMeasure) := by
  classical
  dsimp only
  let ε := Δ / (8 * ((k : ℝ) + 1))
  let σ := ε^2 / 2048
  let τ := 1 / (1 + σ^2 / 8)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεeq : ε * (8 * ((k : ℝ) + 1)) = Δ := by
    dsimp [ε]; exact div_mul_cancel₀ _ (by positivity)
  have hΔ16 : Δ ≤ 1 / 16 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 16 * ((k : ℝ) + 1))).mp hΔsmall
    nlinarith [mul_nonneg hk hΔ.le]
  have hε128 : ε ≤ 1 / 128 := by nlinarith [mul_nonneg hk hε.le]
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσ1 : σ ≤ 1 := by dsimp [σ]; nlinarith
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ1 : τ ≤ 1 := by
    dsimp [τ]
    apply (div_le_one (by positivity)).mpr
    nlinarith only [sq_nonneg σ]
  have hv : 0 < 1 - σ^2 / 8 := by nlinarith
  have hv1 : 1 - σ^2 / 8 < 1 := by nlinarith
  obtain ⟨δ₀, μ, η, hδ₀, hμ, hη, hparams⟩ :=
    Poincare.CurvatureIntegral.exists_tilted_slab_parameters_with_uniform_tolerance hΔ hΔsmall
  refine ⟨hv, hv1, δ₀, hδ₀, ?_⟩
  intro C hC
  obtain ⟨r₁, H, hr₁, hr₁half, hH, hparameters⟩ := hparams C hC
  let ρ := min 1 (η / 80)
  let A := 9 * Real.exp (256 * H * ρ)
  let q := ρ / (4 * A ^ (k + 1))
  let N := ⌈RiemannianMetric.modelVolume ((m + 2) + k) 1 3 /
    RiemannianMetric.modelVolume ((m + 2) + k) 1 (q / 2)⌉₊
  let Λ := max 1 ((N : ℝ) * ρ)
  let β := min (40 * ρ) (q / 4)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hβ : 0 < β := by dsimp [β]; positivity
  obtain ⟨C₀, hC₀, hind₀⟩ := hind (Λ*H) (β/Λ) (mul_nonneg hΛ.le hH) (div_pos hβ hΛ)
  have hℓ : 0 < τ/1024 := by positivity
  have hℓ1 : τ/1024 ≤ 1 := by linarith
  obtain ⟨B, hB, hslab⟩ :=
    RiemannianMetric.exists_shifted_tilted_fiber_scalar_slab_bound
      m k hm hΔ.le hΔstrong hℓ hℓ1 hH hη hC₀
  let T := Poincare.CurvatureIntegral.normalizedStripCenters
  refine ⟨min r₁ (1/Λ), ((T.card:ℝ)+1)*B, by positivity,
    (min_le_left _ _).trans hr₁half, by positivity, ?_⟩
  intro M _ _ _ _ _ _ _ g D hc hsec f h hf hh U δ hδ hδsmall
    hpair hcross htight hhess hreg c
  let P := fun x i => f i x
  let hP : ContMDiff (𝓡 ((m+2)+k)) 𝓘(ℝ,Fin k → ℝ) ∞ P := contMDiff_pi_space.mpr hf
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((m+2)+k))) =
      (m+2)+k) := ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m+2) hP U hreg c
  let := isManifold_openFiber (m := m+2) hP U hreg c
  let L := openFiber P U c
  let incl := openFiberIncl P U c
  let gL := g.openRegularFiberMetric hP U hreg c
  intro p K hKc hK hKsec r hr hrsmall hbuffer hascent
  let p₀ := incl p
  let : ConnectedSpace M := { toNonempty := ⟨p₀⟩ }
  have hrr₁ : r ≤ r₁ := hrsmall.trans (min_le_left _ _)
  have hrhalf : r ≤ 1/2 := hrr₁.trans hr₁half
  have hrscale : Λ*r ≤ 1 := by
    have hh := (le_div_iff₀ hΛ).mp (hrsmall.trans (min_le_right _ _))
    nlinarith
  obtain ⟨hδstrong, hδε, hbudget, hcenter, hηeq, hHbound⟩ :=
    hparameters δ hδ hδsmall r hr hrr₁
  have holdcross : ∀ x∈U, ∀ i j, i ≠ j →
      |g.inner x (D.gradient (f i) x) (D.gradient (f j) x)| ≤ ε ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (f j) x)| ≤ ε ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (h j) x)| ≤ ε := by
    intro x hx i j hij
    exact ⟨(hcross x hx i j hij).1.trans hδε,
      (hcross x hx i j hij).2.2.1.trans hδε,
      (hcross x hx i j hij).2.2.2.trans hδε⟩
  obtain ⟨u, F, hu, hF, hFdef, hproperU, hregU, hband, hcore, hlevels⟩ :=
    g.exists_directional_tilted_regular_fiber_slabs (m := m+1)
      D hc hsec p₀ f h U.isOpen hf hh hδ hC (mul_pos hμ hr)
      (fun i x hx => hpair x hx i)
      (fun i x hx z => hhess x hx i z) htight hr (by linarith)
      hΔ hΔsmall hbuffer hbudget holdcross hascent
  have herr : σ^4*r/1048576 ≤ r/65536 := by
    have hpow : σ^4 ≤ 1 := pow_le_one₀ hσ.le hσ1
    have hh := mul_le_mul_of_nonneg_right hpow hr.le
    nlinarith
  have happrox : ∀ x, (g.edist p₀ x).toReal∈Icc (113*r/96) (19*r/16) →
      |u x-τ*(g.edist p₀ x).toReal|≤τ*(r/65536) := by
    intro x hx
    exact (hcore x (by linarith [hx.1]) (by linarith [hx.2])).1.trans
      (mul_le_mul_of_nonneg_left herr hτ.le)
  have hFeq : F = fun x => (1-Δ/4)*u x+((Δ/4)/((k:ℝ)+1))*∑ i, h i x := funext hFdef
  have hstripbounds :
      let s := τ*r/1024
      let center := fun t : Icc (7/12:ℝ) (3/5) =>
        (1-Δ/4)*(2*τ*((t:ℝ)*r))+((Δ/4)/((k:ℝ)+1))*∑ i, h i p₀
      let S := fun (t : Icc (7/12:ℝ) (3/5)) (b : ℝ) =>
        {x : L | u (incl x)∈Ioo (2*τ*((t:ℝ)*r)-s/4) (2*τ*((t:ℝ)*r)+s/4) ∧
          F (incl x)-center t+s/16∈Icc (3*s/64) b}
      ∀ t∈T, (∫ x in S t (5*s/64), max 0 (gL.leviCivitaData.scalarCurvature x)
        ∂gL.volumeMeasure) ≤
          B*(r^m+∫ x in S t (15*s/128), K x ∂gL.volumeMeasure) := by
    dsimp only
    intro t ht
    let s := τ*r/1024
    let z := 2*τ*((t:ℝ)*r)
    let b := (1-Δ/4)*z+((Δ/4)/((k:ℝ)+1))*∑ i, h i p₀
    have hs : 0 < s := by dsimp [s]; positivity
    have htR : (t:ℝ)*r ∈ Icc (7*r/12) (9*r/10) := by
      constructor <;> nlinarith only [mul_le_mul_of_nonneg_right t.property.1 hr.le,
        mul_le_mul_of_nonneg_right t.property.2 hr.le, hr]
    obtain ⟨hcompact, w, hw, hS, hregOld, hcentral, hcentralV,
      hVbounds, hfaug, hhaug, haugBounds, haugreg, hrestricted⟩ := hlevels ((t:ℝ)*r) htR
    let S : Opens M :=
      ⟨{x : M | u x∈Ioo (z-s/4) (z+s/4) ∧ ∀ i, |f i x-f i p₀|<μ*r},hS⟩
    have hSU : (S:Set M)⊆U := by
      intro x hx
      have hxrad := (hVbounds x hx.1).2.1
      apply hbuffer x
      rw [←ENNReal.ofReal_toReal (g.edist_ne_top p₀ x)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    let G := fun x => (1-Δ/4)*w x+((Δ/4)/((k:ℝ)+1))*∑ i, h i x
    have hG : ContMDiff (𝓡 ((m+2)+k)) 𝓘(ℝ,ℝ) ∞ G :=
      (contMDiff_const.mul hw).add
        (contMDiff_const.mul (ContMDiff.sum (fun i _ => hh i)))
    obtain ⟨hregS, hslabS⟩ := hslab M (hind₀ M) g D hc hsec f h F G hf hh hF hG
      S p₀ r b hr hrhalf hrscale
      (fun x hx i => ⟨((haugBounds x hx).1 i).1.2,
        ((haugBounds x hx).1 i).2.1.2⟩)
      (fun x hx i => ((haugBounds x hx).1 i).2.2)
      (by
        intro x hx i j hij
        have hij' := (haugBounds x hx).2.1 i j hij
        have hji' := (haugBounds x hx).2.1 j i hij.symm
        refine ⟨hij'.1, ?_, hij'.2.1, hij'.2.2.1⟩
        let : Bundle.RiemannianBundle (TangentSpace (𝓡 ((m+2)+k)) : M → Type _) :=
          ⟨g.toRiemannianMetric⟩
        change |inner ℝ (D.gradient (Fin.cons (α := fun _ : Fin (k+1) => M → ℝ) F f i) x)
          (D.gradient (Fin.cons (α := fun _ : Fin (k+1) => M → ℝ) G h j) x)| ≤ Δ
        have hji := hji'.2.1
        change |inner ℝ (D.gradient (Fin.cons (α := fun _ : Fin (k+1) => M → ℝ) G h j) x)
          (D.gradient (Fin.cons (α := fun _ : Fin (k+1) => M → ℝ) F f i) x)| ≤ Δ at hji
        simpa only [real_inner_comm] using hji)
      (fun x hx i j hij => ((haugBounds x hx).2.1 i j hij).2.2.2)
      (by
        intro x hx i v
        let : Bundle.RiemannianBundle (TangentSpace (𝓡 ((m+2)+k)) : M → Type _) :=
          ⟨g.toRiemannianMetric⟩
        have hv : 0 ≤ g.inner x v v := by
          change 0 ≤ inner ℝ v v
          exact real_inner_self_nonneg
        have hb := (haugBounds x hx).2.2.2 v i
        exact ⟨hb.1.trans (mul_le_mul_of_nonneg_right hHbound hv),
          hb.2.trans (mul_le_mul_of_nonneg_right hHbound hv)⟩)
    let := openFiberChartedSpace (m := m+2) hP S hregS c
    let := isManifold_openFiber (m := m+2) hP S hregS c
    let LS := openFiber P S c
    let incS := openFiberIncl P S c
    let gS := g.openRegularFiberMetric hP S hregS c
    let j : LS → L := fun x => ⟨⟨incS x,hSU x.1.2⟩,x.2⟩
    have hcval : (fun i => f i p₀) = c := p.2
    have hproperS : IsProperMap
        ((Ioo (b-s/16) (b+s/16)).restrictPreimage (F ∘ incS)) := by
      have hp := hrestricted.2.1
      change IsProperMap ((Ioo (b-s/16) (b+s/16)).restrictPreimage
        (F ∘ openFiberIncl P S (fun i => f i p₀))) at hp
      rw [hcval] at hp
      exact hp
    have hinner (x : LS) (hx : F (incS x)∈Ioo (b-s/16) (b+s/16)) :
        u (incS x)∈Ioo (z-s/6) (z+s/6) := by
      have hh := hrestricted.2.2.2
      change ∀ x : openFiber P S (fun i => f i p₀),
        F (openFiberIncl P S (fun i => f i p₀) x)∈Ioo (b-s/16) (b+s/16) →
          u (openFiberIncl P S (fun i => f i p₀) x)∈Ioo (z-s/6) (z+s/6) at hh
      rw [hcval] at hh
      exact hh x hx
    have hbufferS (x : M) (hx : x∈S) (hxc : P x=c)
        (hxF : F x∈Ioo (b-s/16) (b+s/16)) :
        ∀ y, g.edist x y≤ENNReal.ofReal (η*r) → y∈S := by
      let xx : LS := ⟨⟨x,hx⟩,hxc⟩
      have hxi : u x∈Ioo (z-s/6) (z+s/6) := hinner xx hxF
      have hxlevel : ∀ i, f i x=f i p₀ := fun i => congrFun (hxc.trans hcval.symm) i
      have hb := g.closedBall_subset_common_level_tube_of_normalized_slab
        hc f hf hu p₀ hr hτ hτ1 herr (mul_pos hμ hr) htR hband
        (fun y hy hy' => ⟨(hcore y hy hy').1,(hcore y hy hy').2.2.1⟩)
        (fun i y hy => (hpair y (hbuffer y hy) i).1) x hxlevel hxi
      intro y hy
      apply hb y
      change min (s/96) ((μ*r)/2)=η*r at hηeq
      change g.edist x y≤ENNReal.ofReal (min (s/96) ((μ*r)/2))
      rw [hηeq]
      exact hy
    obtain ⟨hj, _, hmetric, _, _⟩ :=
      g.openRegularFiberMetric_restriction_transport hP U S hSU hreg c
    have hjc : Continuous j := hj.continuous
    have hKsecS (x : LS) (v w : TangentSpace (𝓡 (m+2)) x) :
        -K (j x)≤gS.leviCivitaData.sectionalCurvature x v w := by
      rw [gS.leviCivitaData.sectionalCurvature_eq_of_local_isometry
        gL.leviCivitaData isOpen_univ hj.contMDiffOn
        (fun y _ => hmetric y) (mem_univ x)]
      exact hKsec _ _ _
    have hsℓ : (τ/1024)*r=s := by dsimp [s]; ring
    dsimp only at hslabS
    rw [hsℓ] at hslabS
    have hbound := hslabS c hproperS
      (by
        intro x hx hxc hxF
        have hh := (hVbounds x hx.1).2.1
        rw [←ENNReal.ofReal_toReal (g.edist_ne_top p₀ x)]
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hh)
      hbufferS (K ∘ j) (hKc.comp hjc).continuousOn
      (fun x _ => hK (j x)) (fun x _ => hKsecS x)
    let ψ := fun x : M => F x-b+s/16
    have hproperψ : IsProperMap
        ((Ioo (0:ℝ) (s/8)).restrictPreimage (ψ ∘ incS)) :=
      hproperS.restrictPreimage_shifted_interval
    have hbandTrans (b' : ℝ) (hb' : b'<s/8) :
        (∫ x in (ψ ∘ incS) ⁻¹' Icc (3*s/64) b',
          max 0 (gS.leviCivitaData.scalarCurvature x) ∂gS.volumeMeasure) =
        (∫ x in {x:L | u (incl x)∈Ioo (z-s/4) (z+s/4) ∧
            ψ (incl x)∈Icc (3*s/64) b'},
          max 0 (gL.leviCivitaData.scalarCurvature x) ∂gL.volumeMeasure) ∧
        (∫ x in (ψ ∘ incS) ⁻¹' Icc (3*s/64) b', K (j x) ∂gS.volumeMeasure) =
        (∫ x in {x:L | u (incl x)∈Ioo (z-s/4) (z+s/4) ∧
            ψ (incl x)∈Icc (3*s/64) b'}, K x ∂gL.volumeMeasure) := by
      obtain ⟨hR,hW⟩ := g.openFiber_closedBand_integrals_of_proper_restriction
        hP U S hSU hreg c ψ hproperψ (3*s/64) b'
        (fun t ht => ⟨by linarith [ht.1],ht.2.trans_lt hb'⟩)
      have hset : {x:L | incl x∈S ∧ ψ (incl x)∈Icc (3*s/64) b'} =
          {x:L | u (incl x)∈Ioo (z-s/4) (z+s/4) ∧
            ψ (incl x)∈Icc (3*s/64) b'} := by
        ext x
        constructor
        · exact fun hx => ⟨hx.1.1,hx.2⟩
        · intro hx
          refine ⟨⟨hx.1,?_⟩,hx.2⟩
          intro i
          have hh : f i (incl x)=f i p₀ := congrFun (x.2.trans hcval.symm) i
          simp only [hh,sub_self,abs_zero]
          positivity
      refine ⟨?_,?_⟩
      · have hh := hR (fun x => max 0 x)
        change (∫ x in (ψ ∘ incS) ⁻¹' Icc (3*s/64) b',
            max 0 (gS.leviCivitaData.scalarCurvature x) ∂gS.volumeMeasure) =
          ∫ x in {x:L | incl x∈S ∧ ψ (incl x)∈Icc (3*s/64) b'},
            max 0 (gL.leviCivitaData.scalarCurvature x) ∂gL.volumeMeasure at hh
        rw [hset] at hh
        exact hh
      · have hh := hW K
        change (∫ x in (ψ ∘ incS) ⁻¹' Icc (3*s/64) b', K (j x) ∂gS.volumeMeasure) =
          ∫ x in {x:L | incl x∈S ∧ ψ (incl x)∈Icc (3*s/64) b'}, K x ∂gL.volumeMeasure at hh
        rw [hset] at hh
        exact hh
    have hi := hbandTrans (5*s/64) (by linarith)
    have ho := hbandTrans (15*s/128) (by linarith)
    change (∫ x in (ψ ∘ incS) ⁻¹' Icc (3*s/64) (5*s/64),
        max 0 (gS.leviCivitaData.scalarCurvature x) ∂gS.volumeMeasure) ≤
      B*(r^m+∫ x in (ψ ∘ incS) ⁻¹' Icc (3*s/64) (15*s/128), K (j x) ∂gS.volumeMeasure) at hbound
    rw [hi.1,ho.2] at hbound
    exact hbound
  have hsum := g.integral_openFiber_pos_scalar_annulus_le_of_tilted_strips
    D hc f h u hf hh hu U hreg c p hΔ hΔsmall hδ hδstrong hr hbuffer
    (fun i x hx => hpair x hx i) hband happrox K hKc hK B hB.le
    (by simpa only [hFeq, Nat.add_sub_cancel] using hstripbounds)
  refine hsum.trans ?_
  have hnonneg : 0 ≤ r^m+∫ x in {x:L | (g.edist p₀ (incl x)).toReal∈Icc (r/2) (3*r)},
      K x ∂gL.volumeMeasure := add_nonneg (pow_nonneg hr.le _) (integral_nonneg hK)
  apply mul_le_mul_of_nonneg_right _ hnonneg
  nlinarith
