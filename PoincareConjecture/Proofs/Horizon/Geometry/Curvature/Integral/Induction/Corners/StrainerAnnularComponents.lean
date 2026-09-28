import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.StrainerComponents
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberEquiv
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Volume
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace PoincareConjecture
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology Bundle

theorem PoincareConjecture.RiemannianMetric.strainer_openFiber_components_and_diameter_annular
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m + k) M) (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (hn : 1 ≤ m+k)
    (hsec : ∀ x (v w : TangentSpace (𝓡 (m+k)) x), -1 ≤ D.sectionalCurvature x v w)
    (f h : Fin k → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (h i))
    (U : Opens M) {δ H : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (256 * ((k : ℝ) + 1) ^ 2)) (hHnonneg : 0 ≤ H)
    (hunit : ∀ x ∈ U, ∀ i,
      g.tangentNorm x (g.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (g.gradient (h i) x) ≤ 1)
    (hopposite : ∀ x ∈ U, ∀ i,
      g.inner x (g.gradient (f i) x) (g.gradient (h i) x) ≤ -1 + 2 * δ)
    (hcross : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ ∧
      |g.inner x (g.gradient (h i) x) (g.gradient (f j) x)| ≤ δ)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (g.gradient (f i) x) (g.gradient (f j) x) ≤ 0)
    {r η : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1/2) (hη : 0 < η)
    (hH : ∀ x ∈ U, ∀ i w,
      D.hessian (f i) x w w ≤ (H/r) * g.inner x w w ∧
      D.hessian (h i) x w w ≤ (H/r) * g.inner x w w) (p : M) :
    let ρ := min 1 (η/80)
    let A := 9 * Real.exp (256*H*ρ)
    let q := ρ / (4*A^k)
    let N := ⌈PoincareConjecture.RiemannianMetric.modelVolume (m+k) 1 3 /
      PoincareConjecture.RiemannianMetric.modelVolume (m+k) 1 (q/2)⌉₊
    let F := fun y i => f i y
    let hF : ContMDiff (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) ∞ F :=
      contMDiff_pi_space.mpr hf
    ∃ hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) F x),
      ∀ c : Fin k → ℝ,
        (∀ x ∈ U, F x = c → x ∈ g.ball p (2*r)) →
        (∀ x ∈ U, F x = c → ∀ z,
          g.edist x z ≤ ENNReal.ofReal (η*r) → z ∈ U) →
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI := openFiberChartedSpace (m := m) hF U hreg c
        letI := isManifold_openFiber (m := m) hF U hreg c
        let L := openFiber F U c
        let gL := g.openRegularFiberMetric hF U hreg c
        IsCompact (Set.univ : Set L) ∧ PoincareConjecture.MetricComplete gL ∧
          Finite (ConnectedComponents L) ∧ Nat.card (ConnectedComponents L) ≤ N ∧
          ∀ x y : L, y ∈ connectedComponent x →
            gL.edist x y ≤ ENNReal.ofReal ((N:ℝ)*ρ*r) := by
  classical
  let F := fun y i => f i y
  let hF : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ F := contMDiff_pi_space.mpr hf
  let ρ := min 1 (η/80)
  let A := 9*Real.exp (256*H*ρ)
  let q := ρ/(4*A^k)
  let N := ⌈RiemannianMetric.modelVolume (m+k) 1 3 /
    RiemannianMetric.modelVolume (m+k) 1 (q/2)⌉₊
  have hρ : 0<ρ := lt_min (by norm_num) (by positivity)
  have hρ1 : ρ≤1 := min_le_left _ _
  have hρη : 80*ρ≤η := by
    have hh := min_le_right (1:ℝ) (η/80)
    dsimp only [ρ] at *
    linarith
  let a : ℝ := ((2*r)^2)⁻¹
  have ha : 0<a := by dsimp [a]; positivity
  let G := rescaledMetric g a ha
  let DS := rescaledMetric_connection g D a ha
  let f' := fun i x => Real.sqrt a*f i x
  let h' := fun i x => Real.sqrt a*h i x
  let F' := fun x i => f' i x
  have hf' : ∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ (f' i) :=
    fun i => contMDiff_const.mul (hf i)
  have hh' : ∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ (h' i) :=
    fun i => contMDiff_const.mul (hh i)
  have hF' : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ F' :=
    contMDiff_pi_space.mpr hf'
  have hsqrt : Real.sqrt a=(2*r)⁻¹ := by
    dsimp [a]
    rw [Real.sqrt_inv,Real.sqrt_sq (by positivity)]
  have hsqrtpos : 0<Real.sqrt a := Real.sqrt_pos.mpr ha
  have hscale : (H/r)/Real.sqrt a=2*H := by
    rw [hsqrt]
    field_simp
  have hsecG : ∀ x (v w:TangentSpace (𝓡 (m+k)) x),
      -1≤DS.sectionalCurvature x v w := by
    intro x v w
    rw [rescaledMetric_sectionalCurvature]
    dsimp [a]
    rw [inv_inv]
    have he := mul_le_mul_of_nonneg_left (hsec x v w) (sq_nonneg (2*r))
    nlinarith
  have hunitG : ∀ x∈U, ∀ i,
      G.tangentNorm x (G.gradient (f' i) x)≤1 ∧
      G.tangentNorm x (G.gradient (h' i) x)≤1 := by
    intro x hx i
    simpa only [G,f',h',rescaledMetric_tangentNorm_gradient_sqrt_mul] using hunit x hx i
  have hpairG : ∀ x∈U, ∀ i,
      G.inner x (G.gradient (f' i) x) (G.gradient (h' i) x)≤ -1+2*δ := by
    intro x hx i
    simpa only [G,f',h',rescaledMetric_inner_gradient_sqrt_mul] using hopposite x hx i
  have hcrossG : ∀ x∈U, ∀ i j, i≠j →
      |G.inner x (G.gradient (f' i) x) (G.gradient (f' j) x)|≤δ ∧
      |G.inner x (G.gradient (h' i) x) (G.gradient (f' j) x)|≤δ := by
    intro x hx i j hij
    simpa only [G,f',h',rescaledMetric_inner_gradient_sqrt_mul] using hcross x hx i j hij
  have htightG : ∀ x∈U, ∀ i j, i≠j →
      G.inner x (G.gradient (f' i) x) (G.gradient (f' j) x)≤0 := by
    intro x hx i j hij
    simpa only [G,f',h',rescaledMetric_inner_gradient_sqrt_mul] using htight x hx i j hij
  have hHG : ∀ x∈U, ∀ i w,
      DS.hessian (f' i) x w w≤(2*H)*G.inner x w w ∧
      DS.hessian (h' i) x w w≤(2*H)*G.inner x w w := by
    intro x hx i w
    exact ⟨by simpa only [hscale] using
      rescaledMetric_hessian_sqrt_mul_le g D a ha (f i) x w (H/r) (hH x hx i w).1,
      by simpa only [hscale] using
        rescaledMetric_hessian_sqrt_mul_le g D a ha (h i) x w (H/r) (hH x hx i w).2⟩
  obtain ⟨hregG,hgeoG⟩ := G.strainer_openFiber_components_and_diameter DS
    (metricComplete_rescaledMetric g a ha hc) hn hsecG f' h' hf' hh' U hδ hsmall
    (show 0≤2*H by positivity) hunitG hpairG hcrossG htightG hHG p hρ hρ1
  obtain ⟨hreg,_⟩ := g.strainer_openFiber_edist_le_of_ambient_closedBall D hc
    f h hf hh U hδ hsmall (show 0≤H/r by positivity) hunit hopposite
    hcross htight hH hr
  refine ⟨hreg,?_⟩
  intro c hinside hbuffer
  let c' : Fin k → ℝ := fun i => Real.sqrt a*c i
  have heq (x:M) : F' x=c' ↔ F x=c := by
    constructor
    · intro hh
      funext i
      exact mul_left_cancel₀ hsqrtpos.ne' (congrFun hh i)
    · intro hh
      funext i
      exact congrArg (fun z => Real.sqrt a*z) (congrFun hh i)
  have hinsideG : ∀ x∈U, F' x=c' → x∈G.ball p 1 := by
    intro x hx hfx
    rw [rescaledMetric_ball,hsqrt]
    simpa only [div_inv_eq_mul,one_mul] using hinside x hx ((heq x).mp hfx)
  have hbufferG : ∀ x∈U, F' x=c' → ∀ y,
      G.edist x y≤ENNReal.ofReal (40*ρ) → y∈U := by
    intro x hx hfx y hy
    apply hbuffer x hx ((heq x).mp hfx) y
    have hb := mul_le_mul' (le_refl (ENNReal.ofReal (2*r))) hy
    rw [rescaledMetric_edist,hsqrt,←mul_assoc,←ENNReal.ofReal_mul (by positivity : 0≤2*r),
      mul_inv_cancel₀ (by positivity : 2*r≠0),ENNReal.ofReal_one,one_mul,
      ←ENNReal.ofReal_mul (by positivity : 0≤2*r)] at hb
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k)))=m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hF U hreg c
  let := isManifold_openFiber (m := m) hF U hreg c
  let := openFiberChartedSpace (m := m) hF' U hregG c'
  let := isManifold_openFiber (m := m) hF' U hregG c'
  let L := openFiber F U c
  let L' := openFiber F' U c'
  let gL := g.openRegularFiberMetric hF U hreg c
  let gL' := G.openRegularFiberMetric hF' U hregG c'
  have he (x:M) : (x∈U ∧ F x=c) ↔ (x∈U ∧ F' x=c') :=
    and_congr_right fun _ => (heq x).symm
  let e := openFiberDiffeomorphOfEq (m := m) hF hF' hreg hregG he
  obtain ⟨hcompact',_,hfinite',hcard',hdiam'⟩ := hgeoG c' hinsideG hbufferG
  have hN : ⌈RiemannianMetric.modelVolume (m+k) 1 3 /
      RiemannianMetric.modelVolume (m+k) 1
        ((ρ/(4*(9*Real.exp (128*(2*H)*ρ))^k))/2)⌉₊=N := by
    dsimp only [N,q,A]
    rw [show 128*(2*H)*ρ=256*H*ρ by ring]
  rw [hN] at hcard' hdiam'
  let : CompactSpace L' := isCompact_univ_iff.mp hcompact'
  have hcompact : IsCompact (Set.univ : Set L) := by
    have hh := isCompact_range e.symm.contMDiff.continuous
    rwa [(show Surjective (e.symm : L' → L) from e.symm.surjective).range_eq] at hh
  let : CompactSpace L := isCompact_univ_iff.mp hcompact
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : L → Type _) :=
    ⟨gL.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin m))
      (TangentSpace (𝓡 m) : L → Type _) :=
    ⟨⟨gL.inner,gL.toContinuousRiemannianMetric.continuous,fun _ _ _ => rfl⟩⟩
  let : EMetricSpace L := EMetricSpace.ofRiemannianMetric (𝓡 m) L
  have hcomplete : MetricComplete gL := by
    change CompleteSpace L
    infer_instance
  have hsurj := e.symm.contMDiff.continuous.connectedComponentsMap_surjective e.symm.surjective
  let := hfinite'
  have hfinite : Finite (ConnectedComponents L) := Finite.of_surjective _ hsurj
  have hcard : Nat.card (ConnectedComponents L)≤N :=
    (Nat.card_le_card_of_surjective _ hsurj).trans hcard'
  refine ⟨hcompact,hcomplete,hfinite,hcard,?_⟩
  intro x y hxy
  have hd := hdiam' (e x) (e y) (e.contMDiff.continuous.mapsTo_connectedComponent x hxy)
  have hedist := openRegularFiberMetric_edist_equivOfEq hF hF' hreg hregG he G x y
  have hs : (G.openRegularFiberMetric hF U hreg c).edist x y =
      ENNReal.ofReal (Real.sqrt a)*gL.edist x y :=
    rescaledMetric_edist gL a ha x y
  change gL'.edist (e x) (e y)=_ at hedist
  rw [hedist,hs,hsqrt] at hd
  have hb := mul_le_mul' (le_refl (ENNReal.ofReal (2*r))) hd
  rw [←mul_assoc,←ENNReal.ofReal_mul (by positivity : 0≤2*r),
    mul_inv_cancel₀ (by positivity : 2*r≠0),ENNReal.ofReal_one,one_mul,
    ←ENNReal.ofReal_mul (by positivity : 0≤2*r)] at hb
  rw [show 2*r*((N:ℝ)*ρ/2)=(N:ℝ)*ρ*r by ring] at hb
  exact hb
